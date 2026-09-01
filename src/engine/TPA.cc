/*
 * Copyright (c) 2021-2023, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "TPA.h"
#include "TPABase.hh"

#include "Common.h"
#include "ModelBasedProjection.h"
#include "QuantifierElimination.h"
#include "TermUtils.h"
#include "TransformationUtils.h"
#include "TransitionSystem.h"
#include "Witnesses.h"
#include "common/TreeOps.h"
#include "pterms/PTRef.h"
#include "transformers/NestedLoopTransformation.h"
#include "transformers/SingleLoopTransformation.h"
#include "utils/SmtSolver.h"
#include <memory>

namespace golem {
const std::string TPAEngine::TPA = "tpa";
const std::string TPAEngine::SPLIT_TPA = "split-tpa";

std::unique_ptr<TPABase> TPAEngine::mkSolver() {
    switch (coreAlgorithm) {
        case TPACore::BASIC:
            return std::make_unique<TPABasic>(logic, options);
        case TPACore::SPLIT:
            return std::make_unique<TPASplit>(logic, options);
    }
    throw std::logic_error("UNREACHABLE");
}

VerificationResult TPAEngine::solve(const ChcDirectedGraph & graph) {
    if (isTrivial(graph)) { return solveTrivial(graph); }
    if (logic.hasArrays()) { return VerificationResult{VerificationAnswer::UNKNOWN}; }
    if (isTransitionSystem(graph)) {
        auto ts = toTransitionSystem(graph);
        ts = ensureNoAuxiliaryVariablesInInitAndQuery(std::move(ts));
        auto solver = mkSolver();
        auto res = solver->solveTransitionSystem(*ts);
        if (not shouldComputeWitness()) { return VerificationResult(res); }
        switch (res) {
            case VerificationAnswer::UNSAFE:
                return VerificationResult(res, computeInvalidityWitness(graph, solver->getTransitionStepCount()));
            case VerificationAnswer::SAFE: {
                PTRef inductiveInvariant = solver->getInductiveInvariant();
                if (inductiveInvariant == PTRef_Undef) { return VerificationResult(res); }
                // std::cout << "TS invariant: " << logic.printTerm(inductiveInvariant) << std::endl;
                return VerificationResult(res, computeValidityWitness(graph, *ts, inductiveInvariant));
            }
            case VerificationAnswer::UNKNOWN:
            default:
                assert(false);
                throw std::logic_error("Unreachable!");
        }
    } else if ((isTransitionSystemDAG(graph) && not options.hasOption(Options::FORCE_TS)) ||
               options.hasOption(Options::SIMPLIFY_NESTED)) {
        if (options.hasOption(Options::SIMPLIFY_NESTED)) {
            NestedLoopTransformation transformation;
            auto [transformedGraph, preTranslator] = transformation.transform(graph);
            assert(isTransitionSystemDAG(*transformedGraph));
            auto res = solveTransitionSystemGraph(*transformedGraph);
            return preTranslator->translate(res);
        } else {
            return solveTransitionSystemGraph(graph);
        }
    }
    // Translate CHCGraph into transition system
    SingleLoopTransformation transformation;
    auto [ts, backtranslator] = transformation.transform(graph);
    assert(ts);
    auto solver = mkSolver();
    auto res = solver->solveTransitionSystem(*ts);
    if (not shouldComputeWitness()) { return VerificationResult(res); }
    switch (res) {
        case VerificationAnswer::UNSAFE:
            return backtranslator->translate({res, solver->getTransitionStepCount()});
        case VerificationAnswer::SAFE: {
            PTRef inductiveInvariant = solver->getInductiveInvariant();
            if (inductiveInvariant == PTRef_Undef) { return VerificationResult(res); }
            return backtranslator->translate({res, inductiveInvariant});
        }
        case VerificationAnswer::UNKNOWN:
        default:
            assert(false);
            throw std::logic_error("Unreachable!");
    }
}

/*
 * Extension for DAG of transition systems
 */
class TransitionSystemNetworkManager {
    TPAEngine & owner;
    Logic & logic;
    ChcDirectedGraph const & graph;
    AdjacencyListsGraphRepresentation adjacencyRepresentation;

public:
    TransitionSystemNetworkManager(TPAEngine & owner, ChcDirectedGraph const & graph)
        : owner(owner),
          logic(owner.logic),
          graph(graph),
          adjacencyRepresentation(AdjacencyListsGraphRepresentation::from(graph)) {}

    VerificationResult solve() &&;

private:
    struct NetworkNode {
        std::unique_ptr<TPABase> solver{nullptr};
        PTRef preSafe{PTRef_Undef};
        PTRef postSafe{PTRef_Undef};
        std::size_t blocked_children{0};
        std::vector<EId> children;
        std::vector<PTRef> blockedReason;
    };

    std::unordered_map<SymRef, NetworkNode, SymRefHash> networkMap;

    struct QueryResult {
        ReachabilityResult reachabilityResult;
        PTRef explanation;
    };

    [[nodiscard]] static bool reachable(ReachabilityResult res) { return res == ReachabilityResult::REACHABLE; }

    void initNetwork();

    [[nodiscard]] std::unique_ptr<TPABase> mkSolver() const { return owner.mkSolver(); }

    [[nodiscard]] TransitionSystem constructTransitionSystemFor(SymRef vid) const;

    [[nodiscard]] NetworkNode & getNode(SymRef vid) { return networkMap.at(vid); }
    [[nodiscard]] NetworkNode const & getNode(SymRef vid) const { return networkMap.at(vid); }

    [[nodiscard]] vec<SymRef> getGraphStarts() const {
        vec<SymRef> graphStarts;
        for (auto outgoingEdge : adjacencyRepresentation.getOutgoingEdgesFor(graph.getEntry())) {
            graphStarts.push(graph.getTarget(outgoingEdge));
        }
        return graphStarts;
    }

    [[nodiscard]] vec<SymRef> getGraphEnds() const {
        vec<SymRef> graphEnds;
        for (auto incomingEdge : adjacencyRepresentation.getIncomingEdgesFor(graph.getExit())) {
            graphEnds.push(graph.getSource(incomingEdge));
        }
        return graphEnds;
    }

    [[nodiscard]] QueryResult queryEdge(EId eid, PTRef sourceCondition, PTRef targetCondition) const;

    [[nodiscard]] QueryResult queryTransitionSystem(NetworkNode const & node, PTRef sourceCondition,
                                                    PTRef targetCondition) const;

    [[nodiscard]] witness_t computeInvalidityWitness(std::vector<EId> const & path) const;

    [[nodiscard]] witness_t computeValidityWitness() const;
};

VerificationResult TPAEngine::solveTransitionSystemGraph(const ChcDirectedGraph & graph) {
    return TransitionSystemNetworkManager(*this, graph).solve();
}

void TransitionSystemNetworkManager::initNetwork() {
    assert(networkMap.empty());
    for (auto vid : graph.getVertices()) {
        auto [it, _] = networkMap.insert({vid, NetworkNode()});
        auto & node = it->second;
        node.preSafe = logic.getTerm_false();
        node.postSafe = logic.getTerm_false();
        node.blocked_children = 0;
        if (vid == graph.getEntry() or vid == graph.getExit()) { continue; }
        node.solver = mkSolver();
        TransitionSystem ts = constructTransitionSystemFor(vid);
        node.solver->resetTransitionSystem(ts);
    }
    // Connect the network
    auto isSelfLoop = [this](EId eid) { return graph.getSource(eid) == graph.getTarget(eid); };
    // TODO: no need for reverse post order, better to process outgoing edges
    for (auto vid : reversePostOrder(graph, adjacencyRepresentation)) {
        if (vid != graph.getEntry()) {
            auto incomingEdges = adjacencyRepresentation.getIncomingEdgesFor(vid);
            for (auto edge : incomingEdges) {
                if (isSelfLoop(edge)) { continue; }
                getNode(graph.getSource(edge)).children.push_back(edge);
                getNode(graph.getSource(edge)).blockedReason.push_back(PTRef_Undef);
            }
        }
    }
}

namespace {

enum class NodeState { PRE, POST };
struct Entry {
    NodeState state;
    SymRef node;
    std::optional<EId> incomingEdge; // Edge used to get into this node, valid only for PRE state
    PTRef reached;
};

using Path = std::vector<Entry>;

std::vector<EId> extractPath(Path const & path) {
    std::vector<EId> res;
    for (auto const & entry : path) {
        if (entry.state == NodeState::PRE) { res.push_back(entry.incomingEdge.value()); }
    }
    return res;
}

} // namespace

VerificationResult TransitionSystemNetworkManager::solve() && {
    initNetwork();
    Path path;
    path.push_back({NodeState::POST, graph.getEntry(), std::nullopt, logic.getTerm_true()});
    while (not path.empty()) {
        auto const & [state, node, eid, reached] = path.back();
        auto & networkNode = getNode(node);
        switch (state) {
            case NodeState::PRE: // Traverse loop
            {
                auto res = queryTransitionSystem(networkNode, reached, logic.mkNot(networkNode.postSafe));
                if (res.reachabilityResult == ReachabilityResult::REACHABLE) {
                    path.push_back({NodeState::POST, node, std::nullopt, res.explanation});
                } else {
                    networkNode.preSafe = logic.mkOr(networkNode.preSafe, res.explanation);
                    path.pop_back();
                }
                break;
            }
            case NodeState::POST: // Traverse bridge
            {
                if (networkNode.blocked_children == networkNode.children.size()) { // No way out
                    PTRef blocked = logic.mkAnd(networkNode.blockedReason);
                    networkNode.postSafe = logic.mkOr(networkNode.postSafe, blocked);
                    path.pop_back();
                    for (PTRef & reason : networkNode.blockedReason) {
                        reason = PTRef_Undef;
                    }
                    networkNode.blocked_children = 0;
                } else { // Try continuing with the next edge
                    assert(networkNode.blocked_children < networkNode.children.size());
                    auto childIndex = networkNode.blocked_children;
                    EId nextEdge = networkNode.children[childIndex];
                    auto target = graph.getTarget(nextEdge);
                    auto res = queryEdge(nextEdge, reached, logic.mkNot(getNode(target).preSafe));
                    if (res.reachabilityResult == ReachabilityResult::REACHABLE) {
                        path.push_back({NodeState::PRE, target, nextEdge, res.explanation});
                        if (target == graph.getExit()) {
                            witness_t witness = owner.shouldComputeWitness()
                                                    ? computeInvalidityWitness(extractPath(path))
                                                    : NoWitness{};
                            return {VerificationAnswer::UNSAFE, std::move(witness)};
                        }
                    } else {
                        networkNode.blockedReason[childIndex] = res.explanation;
                        ++networkNode.blocked_children;
                    }
                }
                break;
            }
        }
    }
    witness_t witness = owner.shouldComputeWitness() ? computeValidityWitness() : NoWitness{};
    return {VerificationAnswer::SAFE, std::move(witness)};
}

witness_t TransitionSystemNetworkManager::computeInvalidityWitness(std::vector<EId> const & path) const {
    std::vector<EId> errorPath;
    for (EId edge : path) {
        errorPath.push_back(edge);
        SymRef target = graph.getTarget(edge);
        if (target != graph.getExit()) {
            auto steps = getNode(target).solver->getTransitionStepCount();
            errorPath.insert(errorPath.end(), steps, getSelfLoopFor(target, graph, adjacencyRepresentation).value());
        }
    }
    return InvalidityWitness::fromErrorPath(ErrorPath{std::move(errorPath)}, graph);
}

witness_t TransitionSystemNetworkManager::computeValidityWitness() const {
    assert(isTransitionSystemDAG(graph));
    TermUtils utils(logic);
    TimeMachine timeMachine(logic);
    auto definitions = ValidityWitness::trivialDefinitions(graph);

    for (auto vertex : graph.getVertices()) {
        if (vertex == graph.getEntry() || vertex == graph.getExit()) continue;
        auto const & node = getNode(vertex);

        auto graphVars = utils.predicateArgsInOrder(graph.getStateVersion(vertex));
        vec<PTRef> unversionedVars;
        auto systemVars = node.solver->getStateVars(0);

        TermUtils::substitutions_map subs;
        for (std::size_t i = 0; i < graphVars.size(); ++i) {
            unversionedVars.push(timeMachine.getUnversioned(graphVars[i]));
            subs.insert({systemVars[i], unversionedVars.last()});
        }
        auto [res, explanation] = queryTransitionSystem(node, node.preSafe, logic.mkNot(node.postSafe));
        assert(res == ReachabilityResult::UNREACHABLE);
        if (res == ReachabilityResult::UNREACHABLE) {
            PTRef graphInvariant = utils.varSubstitute(node.solver->getInductiveInvariant(), subs);
            definitions[vertex] = graphInvariant;
        } else {
            return NoWitness("Unexpected situation occurred during witness computation in TPA engine");
        }
    }
    return ValidityWitness(std::move(definitions));
}

TransitionSystem TransitionSystemNetworkManager::constructTransitionSystemFor(SymRef vid) const {
    EId loopEdge = getSelfLoopFor(vid, graph, adjacencyRepresentation).value();
    auto edgeVars = getVariablesFromEdge(logic, graph, loopEdge);
    auto systemType = std::make_unique<SystemType>(edgeVars.stateVars, edgeVars.auxiliaryVars, logic);
    PTRef loopLabel = graph.getEdgeLabel(loopEdge);
    PTRef transitionFla = transitionFormulaInSystemType(*systemType, edgeVars, loopLabel, logic);
    return TransitionSystem(logic, std::move(systemType), logic.getTerm_true(), transitionFla, logic.getTerm_true());
}

TransitionSystemNetworkManager::QueryResult TransitionSystemNetworkManager::queryEdge(EId eid, PTRef sourceCondition,
                                                                                      PTRef targetCondition) const {
    SMTSolver solver(logic, SMTSolver::WitnessProduction::MODEL_AND_INTERPOLANTS);
    solver.getConfig().setLRAInterpolationAlgorithm(itp_lra_alg_decomposing_strong);
    solver.getConfig().setSimplifyInterpolant(4);
    PTRef label = graph.getEdgeLabel(eid);
    TRACE(1, "Querying edge " << eid.id << " with label " << logic.pp(label) << "\n\tsource is "
                              << logic.pp(sourceCondition) << "\n\ttarget is " << logic.pp(targetCondition))
    PTRef target = TimeMachine(logic).sendFlaThroughTime(targetCondition, 1);
    solver.assertProp(sourceCondition);
    solver.assertProp(label);
    solver.assertProp(target);
    auto res = solver.check();
    if (res == SMTSolver::Answer::SAT) {
        auto model = solver.getModel();
        ModelBasedProjection mbp(logic);
        PTRef query = logic.mkAnd({sourceCondition, label, target});
        auto targetVars = TermUtils(logic).predicateArgsInOrder(graph.getNextStateVersion(graph.getTarget(eid)));
        PTRef eliminated = mbp.keepOnly(query, targetVars, *model);
        eliminated = TimeMachine(logic).sendFlaThroughTime(eliminated, -1);
        TRACE(1, "Propagating along the edge " << logic.pp(eliminated))
        return {ReachabilityResult::REACHABLE, eliminated};
    } else if (res == SMTSolver::Answer::UNSAT) {
        auto itpContext = solver.getInterpolationContext();
        ipartitions_t mask = (1 << 1) + (1 << 2); // This puts label + target into the A-part

        vec<PTRef> itps;
        itpContext->getSingleInterpolant(itps, mask);
        assert(itps.size() == 1);
        PTRef explanation = logic.mkNot(itps[0]);
        TRACE(1, "Blocking edge with " << logic.pp(explanation))
        return {ReachabilityResult::UNREACHABLE, explanation};
    }
    throw std::logic_error("Error in the underlying SMT solver");
}

TransitionSystemNetworkManager::QueryResult
TransitionSystemNetworkManager::queryTransitionSystem(NetworkNode const & node, PTRef sourceCondition,
                                                      PTRef targetCondition) const {
    node.solver->resetInitialStates(sourceCondition);
    node.solver->resetQueryStates(targetCondition);
    auto res = node.solver->solve();
    assert(res != VerificationAnswer::UNKNOWN);
    switch (res) {
        case VerificationAnswer::UNSAFE: {
            PTRef reachedPostStates = node.solver->getReachedStates();
            assert(reachedPostStates != PTRef_Undef);
            TRACE(1, "TS propagates reachable states to " << logic.pp(reachedPostStates))
            return {ReachabilityResult::REACHABLE, reachedPostStates};
        }
        case VerificationAnswer::SAFE: {
            PTRef explanation = node.solver->getSafetyExplanation();
            assert(explanation != PTRef_Undef);
            TRACE(1, "TS blocks " << logic.pp(explanation))
            return {ReachabilityResult::UNREACHABLE, explanation};
        }
        default:
            assert(false);
            throw std::logic_error("Unreachable");
    }
}

InvalidityWitness TPAEngine::computeInvalidityWitness(ChcDirectedGraph const & graph, unsigned steps) const {
    return InvalidityWitness::fromTransitionSystem(graph, steps);
}

ValidityWitness TPAEngine::computeValidityWitness(ChcDirectedGraph const & graph, TransitionSystem const & ts,
                                                  PTRef inductiveInvariant) const {
    return ValidityWitness::fromTransitionSystem(logic, graph, ts, inductiveInvariant);
}
} // namespace golem
