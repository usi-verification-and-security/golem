/*
 * Copyright (c) 2020-2025, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "Bmc.h"

#include "Common.h"

#include "TermUtils.h"
#include "TransformationUtils.h"
#include "transformers/SingleLoopTransformation.h"
#include "utils/SmtSolver.h"

namespace golem {
VerificationResult BMC::solve(ChcDirectedGraph const & graph) {
    if (isTrivial(graph)) { return solveTrivial(graph); }
    if (isTransitionSystem(graph)) { return solveTransitionSystem(graph); }
    if (not forceTransitionSystem) { return solveGeneralLinearSystem(graph); }

    SingleLoopTransformation transformation;
    auto [ts, backtranslator] = transformation.transform(graph);
    assert(ts);
    auto res = solveTransitionSystemInternal(*ts);
    return needsWitness ? backtranslator->translate(res) : VerificationResult{res.answer};
}

VerificationResult BMC::solveTransitionSystem(ChcDirectedGraph const & graph) {
    auto ts = toTransitionSystem(graph);
    auto res = solveTransitionSystemInternal(*ts);
    return needsWitness ? translateTransitionSystemResult(res, graph, *ts) : VerificationResult{res.answer};
}

TransitionSystemVerificationResult BMC::solveTransitionSystemInternal(TransitionSystem const & system) {
    std::size_t maxLoopUnrollings = std::numeric_limits<std::size_t>::max();
    PTRef init = system.getInit();
    PTRef query = system.getQuery();
    PTRef transition = system.getTransition();

    SMTSolver solver(logic, SMTSolver::WitnessProduction::NONE);
    //    std::cout << "Adding initial states: " << logic.pp(init) << std::endl;
    solver.assertProp(init);
    {
        // Check for system with empty initial states
        auto res = solver.check();
        if (res == SMTSolver::Answer::UNSAT) {
            return TransitionSystemVerificationResult{VerificationAnswer::SAFE, logic.getTerm_false()};
        }
    }

    TimeMachine tm{logic};
    for (std::size_t currentUnrolling = 0; currentUnrolling < maxLoopUnrollings; ++currentUnrolling) {
        PTRef versionedQuery = tm.sendFlaThroughTime(query, currentUnrolling);
        //        std::cout << "Adding query: " << logic.pp(versionedQuery) << std::endl;
        solver.push();
        solver.assertProp(versionedQuery);
        auto res = solver.check();
        if (res == SMTSolver::Answer::SAT) {
            if (verbosity > 0) { std::cout << "; BMC: Bug found in depth: " << currentUnrolling << std::endl; }
            return TransitionSystemVerificationResult{.answer = VerificationAnswer::UNSAFE,
                                                      .witness = static_cast<std::size_t>(currentUnrolling)};
        }
        if (verbosity > 1) { std::cout << "; BMC: No path of length " << currentUnrolling << " found!" << std::endl; }
        solver.pop();
        PTRef versionedTransition = tm.sendFlaThroughTime(transition, currentUnrolling);
        //        std::cout << "Adding transition: " << logic.pp(versionedTransition) << std::endl;
        solver.assertProp(versionedTransition);
    }
    return TransitionSystemVerificationResult{VerificationAnswer::UNKNOWN, 0u};
}

namespace {
constexpr const char * auxName = "golem_bmc";

class BMCUtils {
public:
    explicit BMCUtils(Logic & logic) : logic(logic) {}

    PTRef getVarFor(SymRef node, std::size_t step) {
        return logic.mkBoolVar((auxName + std::to_string(node.x) + '#' + std::to_string(step)).c_str());
    }

private:
    Logic & logic;
};

InvalidityWitness computeWitness(ChcDirectedGraph const & graph, Model & model, std::size_t const steps,
                                 std::unordered_set<PTRef, PTRefHash> const & knownNodes) {
    auto adjacencyLists = AdjacencyListsGraphRepresentation::from(graph);
    Logic & logic = graph.getLogic();
    PTRef trueT = logic.getTerm_true();
    BMCUtils utils(logic);
    std::vector<EId> errorPath;
    PTRef errorReached = utils.getVarFor(graph.getExit(), steps);
    if (model.evaluate(errorReached) != trueT) { return {}; }
    auto current = graph.getExit();
    auto remaining = steps;
    while (remaining > 0) {
        // figure out the predecessor;
        for (auto eid : adjacencyLists.getIncomingEdgesFor(current)) {
            auto source = graph.getSource(eid);
            PTRef reached = utils.getVarFor(source, remaining - 1);
            if (knownNodes.find(reached) == knownNodes.end()) { continue; }
            if (model.evaluate(reached) == trueT and model.evaluate(TimeMachine(logic).sendFlaThroughTime(
                                                         graph.getEdgeLabel(eid), remaining - 1)) == trueT) {
                errorPath.push_back(eid);
                current = source;
                break; // the for loop
            }
        }
        --remaining;
    }
    if (errorPath.size() != steps) { return {}; }
    std::reverse(errorPath.begin(), errorPath.end());
    return InvalidityWitness::fromErrorPath(ErrorPath(std::move(errorPath)), graph);
}
} // namespace

/**
 * Algorithm to check linear system of CHCs using a single solver.
 *
 * The algorithm maintains a frontier of reachable nodes for each level l and in each iteration computes
 * the next frontier for level l+1.
 *
 * The algorithm uses auxiliary boolean variables n_l to track if a node n is reached at level l.
 * We constain the search in the solver with conditions that if  a node is reached at level l+1 then
 * one of its predecessors must be reached at level l.
 * The auxiliary variables also help to extract the feasible path.
 *
 * TODO: Figure out a way to avoid these extra checks
 *
 * Preconditions:
 *  - There are no multiedges (No target can be reached from the same source by two different edges)
 */
VerificationResult BMC::solveGeneralLinearSystem(ChcDirectedGraph const & graph) {
    if (verbosity > 0) { std::cout << "; BMC: Solving general system!" << std::endl; }
    Logic & logic = graph.getLogic();
    BMCUtils utils(logic);
    auto adjacencyLists = AdjacencyListsGraphRepresentation::from(graph);
    TimeMachine tm(logic);
    std::unordered_set<SymRef, SymRefHash> frontier, nextFrontier;
    frontier.insert(graph.getEntry());
    SMTSolver solver(logic, SMTSolver::WitnessProduction::ONLY_MODEL);
    auto allnodes = graph.getVertices();
    std::size_t maxLoopUnrollings = std::numeric_limits<int>::max() - 1;

    // TODO: Figure out how to compute CEX without this. Maybe OpenSMT should have a model that does not use default
    // values?
    std::unordered_set<PTRef, PTRefHash> encounteredNodes;
    {
        PTRef entry = utils.getVarFor(graph.getEntry(), 0u);
        solver.assertProp(entry);
        encounteredNodes.insert(entry);
    }
    for (std::size_t currentUnrolling = 0u; currentUnrolling < maxLoopUnrollings; ++currentUnrolling) {
        nextFrontier.clear();
        bool exitEncountered = false;
        for (auto node : allnodes) {
            vec<PTRef> predecessorTransitions;
            for (EId eid : adjacencyLists.getIncomingEdgesFor(node)) {
                auto source = graph.getSource(eid);
                if (frontier.find(source) == frontier.end()) { continue; }
                PTRef sourceReached = utils.getVarFor(source, currentUnrolling);
                PTRef transition = tm.sendFlaThroughTime(graph.getEdgeLabel(eid), static_cast<int>(currentUnrolling));
                predecessorTransitions.push(logic.mkAnd(transition, sourceReached));
            }
            if (predecessorTransitions.size() > 0) {
                exitEncountered |= node == graph.getExit();
                PTRef nodeReached = utils.getVarFor(node, currentUnrolling + 1);
                solver.assertProp(logic.mkImpl(nodeReached, logic.mkOr(predecessorTransitions)));
                nextFrontier.insert(node);
                encounteredNodes.insert(nodeReached);
            }
        }
        if (exitEncountered) {
            // TODO: Implement check-sat-assuming in OpenSMT
            PTRef exitReached = utils.getVarFor(graph.getExit(), currentUnrolling + 1);
            solver.push();
            solver.assertProp(exitReached);
            auto res = solver.check();
            if (res == SMTSolver::Answer::SAT) {
                if (verbosity > 0) { std::cout << "; BMC: Bug found in depth: " << currentUnrolling << std::endl; }
                if (not needsWitness) { return {VerificationAnswer::UNSAFE, NoWitness{}}; }
                return {VerificationAnswer::UNSAFE,
                        computeWitness(graph, *solver.getModel(), currentUnrolling + 1, encounteredNodes)};
            }
            solver.pop();
        }
        if (verbosity > 1) { std::cout << "; BMC: No path of length " << currentUnrolling << " found!" << std::endl; }
        std::swap(frontier, nextFrontier);
    }
    return VerificationResult(VerificationAnswer::UNKNOWN);
}
} // namespace golem