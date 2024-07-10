/*
 * Copyright (c) 2020-2024, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "Bmc.h"

#include "Common.h"

#include "TermUtils.h"
#include "TransformationUtils.h"
#include "transformers/SingleLoopTransformation.h"
#include "utils/SmtSolver.h"

VerificationResult BMC::solve(ChcDirectedGraph const & graph) {
    if (isTrivial(graph)) {
        return solveTrivial(graph);
    }
    if (isTransitionSystem(graph)) {
        return solveTransitionSystem(graph);
    }
    if (not forceTransitionSystem) {
        return solveGeneralLinearSystem(graph);
    }

    SingleLoopTransformation transformation;
    auto[ts, backtranslator] = transformation.transform(graph);
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

    SMTSolver solverWrapper(logic, SMTSolver::WitnessProduction::NONE);
    auto & solver = solverWrapper.getCoreSolver();
//    std::cout << "Adding initial states: " << logic.pp(init) << std::endl;
    solver.insertFormula(init);
    { // Check for system with empty initial states
        auto res = solver.check();
        if (res == s_False) {
            return TransitionSystemVerificationResult{VerificationAnswer::SAFE, logic.getTerm_false()};
        }
    }

    TimeMachine tm{logic};
    for (std::size_t currentUnrolling = 0; currentUnrolling < maxLoopUnrollings; ++currentUnrolling) {
        PTRef versionedQuery = tm.sendFlaThroughTime(query, currentUnrolling);
//        std::cout << "Adding query: " << logic.pp(versionedQuery) << std::endl;
        solver.push();
        solver.insertFormula(versionedQuery);
        auto res = solver.check();
        if (res == s_True) {
            if (verbosity > 0) { std::cout << "; BMC: Bug found in depth: " << currentUnrolling << std::endl; }
            return TransitionSystemVerificationResult{.answer = VerificationAnswer::UNSAFE, .witness = static_cast<std::size_t>(currentUnrolling)};
        }
        if (verbosity > 1) { std::cout << "; BMC: No path of length " << currentUnrolling << " found!" << std::endl; }
        solver.pop();
        PTRef versionedTransition = tm.sendFlaThroughTime(transition, currentUnrolling);
//        std::cout << "Adding transition: " << logic.pp(versionedTransition) << std::endl;
        solver.insertFormula(versionedTransition);
    }
    return TransitionSystemVerificationResult{VerificationAnswer::UNKNOWN, 0u};
}

namespace {
constexpr const char * auxName = "golem_bmc";

InvalidityWitness computeWitness(ChcDirectedGraph const & graph, Model & model, std::size_t const steps, std::unordered_set<PTRef, PTRefHash> const & knownNodes) {
    auto adjacencyLists = AdjacencyListsGraphRepresentation::from(graph);
    Logic & logic = graph.getLogic();
    auto getVarFor = [&](SymRef node, std::size_t step) {
        return logic.mkBoolVar((auxName + std::to_string(node.x) + '#' + std::to_string(step)).c_str());
    };
    std::vector<EId> errorPath;
    PTRef errorReached = getVarFor(graph.getExit(), steps);
    if (model.evaluate(errorReached) != logic.getTerm_true()) { return {}; }
    auto current = graph.getExit();
    auto remaining = steps;
    while (remaining > 0) {
        // figure out the predecessor;
        for (auto eid : adjacencyLists.getIncomingEdgesFor(current)) {
            auto source = graph.getSource(eid);
            PTRef reached = getVarFor(source, remaining - 1);
            if (knownNodes.find(reached) == knownNodes.end()) { continue; }
            if (model.evaluate(reached) == logic.getTerm_true()) {
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
}

/**
 * Algorithm to check linear system of CHCs using a single solver.
 *
 * The algorithm maintains a frontier of reachable nodes for each level l and in each iteration computes
 * the next frontier for level l+1. When an edge to an error node is encountered, the solver checks
 * the feasibility of traversing the edge.
 *
 * The algorithm uses auxiliary boolean variables n_l to track if a node n is reached at level l.
 * We use this because we do not unroll into a tree, but into a DAG, with multiple possible paths to the same node.
 * The auxiliary variables are used to ensure that if a node n is reached at level l, then some successor must be
 * reached at level l+1. Similarly, if a node is reached at level l+1 then one of its predecessors must be reached
 * at level l.
 * The auxiliary variables also help to extract the feasible path.
 *
 * However, with these extra conditions we need to check true reachability of every node we want to add to the frontier.
 * Otherwise, it would make the whole unrolled DAG infeasible.
 *
 * TODO: Figure out a way to avoid these extra checks
 *
 * Preconditions:
 *  - There are no multiedges (No target can be reached from the same source by two different edges)
 *  - There are no inconsistent edges 
 */
VerificationResult BMC::solveGeneralLinearSystem(ChcDirectedGraph const & graph) {
    if (verbosity > 0) { std::cout << "BMC: Solving general system!" << std::endl; }
    Logic & logic = graph.getLogic();
    auto getVarFor = [&](SymRef node, std::size_t step) {
        return logic.mkBoolVar((auxName + std::to_string(node.x) + '#' + std::to_string(step)).c_str());
    };
    auto adjacencyLists = AdjacencyListsGraphRepresentation::from(graph);
    TimeMachine tm(logic);
    std::unordered_set<SymRef, SymRefHash> frontier;
    frontier.insert(graph.getEntry());
    std::unordered_map<SymRef, PTRef, SymRefHash> nextFrontier;
    SMTSolver solver(logic, SMTSolver::WitnessProduction::ONLY_MODEL);

    // TODO: Figure out how to compute CEX withtout this. Maybe OpenSMT should have a model that does not use default values?
    std::unordered_set<PTRef, PTRefHash> encounteredNodes;
    {
        PTRef entry = getVarFor(graph.getEntry(), 0u);
        solver.getCoreSolver().insertFormula(entry);
        encounteredNodes.insert(entry);
    }
    std::size_t maxLoopUnrollings = std::numeric_limits<std::size_t>::max() - 1;
    for(std::size_t currentUnrolling = 0u; currentUnrolling < maxLoopUnrollings; ++currentUnrolling) {
        for (auto node : frontier) {
            PTRef currentNodeReached = getVarFor(node, currentUnrolling);
            vec<PTRef> nextTransitions;
            for (EId eid : adjacencyLists.getOutgoingEdgesFor(node)) {
                auto target = graph.getTarget(eid);
                PTRef transition = tm.sendFlaThroughTime(graph.getEdgeLabel(eid), currentUnrolling);
                PTRef nextTargetReached = getVarFor(target, currentUnrolling + 1);
                nextTransitions.push(logic.mkAnd(transition, nextTargetReached));
                nextFrontier.emplace(target, nextTargetReached);
            }
            solver.getCoreSolver().insertFormula(logic.mkImpl(currentNodeReached, logic.mkOr(nextTransitions)));
        }

        for (auto const & [node, nodeReached] : nextFrontier) {
            vec<PTRef> predecessorTransitions;
            for (EId eid : adjacencyLists.getIncomingEdgesFor(node)) {
                auto source = graph.getSource(eid);
                if (frontier.find(source) == frontier.end()) { continue; }
                PTRef sourceReached = getVarFor(source, currentUnrolling);
                PTRef transition = tm.sendFlaThroughTime(graph.getEdgeLabel(eid), currentUnrolling);
                predecessorTransitions.push(logic.mkAnd(transition, sourceReached));
            }
            solver.getCoreSolver().insertFormula(logic.mkImpl(nodeReached, logic.mkOr(predecessorTransitions)));
        }
        frontier.clear();
        std::vector<PTRef> notReached;
        std::transform(nextFrontier.begin(), nextFrontier.end(), std::back_inserter(notReached),
                       [&](auto const & entry) { return logic.mkNot(entry.second); });
        for (auto const & [node, nodeReached] : nextFrontier) {
            // TODO: Implement check-sat-assuming in OpenSMT
            PTRef nodeNotReached = logic.mkNot(nodeReached);
            auto it = std::find(notReached.begin(), notReached.end(), nodeNotReached);
            assert(it != notReached.end());
            *it = nodeReached;
            solver.getCoreSolver().push();
            solver.getCoreSolver().insertFormula(logic.mkAnd(notReached));
            *it = nodeNotReached;
            auto res = solver.getCoreSolver().check();
            if (node == graph.getExit() and res == s_True) {
                if (not needsWitness) { return {VerificationAnswer::UNSAFE, NoWitness{}}; }
                return {VerificationAnswer::UNSAFE, computeWitness(graph, *solver.getCoreSolver().getModel(), currentUnrolling + 1, encounteredNodes)};
            }
            if (res != s_False) {
                frontier.insert(node);
                encounteredNodes.insert(nodeReached);
            }
            solver.getCoreSolver().pop();
        }
        nextFrontier.clear();
        if (frontier.empty()) { return VerificationResult(VerificationAnswer::SAFE); }
        if (verbosity > 1) { std::cout << "; BMC: No path of length " << currentUnrolling << " found!" << std::endl; }
    }
    return VerificationResult(VerificationAnswer::UNKNOWN);
}
