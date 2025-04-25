/*
 * Copyright (c) 2022-2025, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "Kind.h"

#include "Common.h"
#include "TermUtils.h"
#include "TransformationUtils.h"
#include "utils/SmtSolver.h"

namespace golem {

class BSE {
public:
    explicit BSE(Logic & logic) : logic(logic) {}
    VerificationResult run(ChcDirectedGraph const & graph);
private:
    Logic & logic;
};

VerificationResult Kind::solve(ChcDirectedGraph const & graph) {
    if (isTrivial(graph)) {
        return solveTrivial(graph);
    }
    if (isTransitionSystem(graph)) {
        return solveTransitionSystem(graph);
    }
    return BSE{logic}.run(graph);
}

VerificationResult Kind::solveTransitionSystem(ChcDirectedGraph const & graph) {
    auto ts = toTransitionSystem(graph);
    ts = ensureNoAuxiliaryVariablesInInitAndQuery(std::move(ts));
    auto res = solveTransitionSystemInternal(*ts);
    return computeWitness ? translateTransitionSystemResult(res, graph, *ts) : VerificationResult(res.answer);
}

TransitionSystemVerificationResult Kind::solveTransitionSystemInternal(TransitionSystem const & system) {
    std::size_t maxK = std::numeric_limits<std::size_t>::max();
    PTRef init = system.getInit();
    PTRef query = system.getQuery();
    PTRef transition = system.getTransition();
    PTRef backwardTransition = TransitionSystem::reverseTransitionRelation(system);

    // Base step: Init(x0) and Tr^k(x0,xk) and Query(xk), if SAT -> return UNSAFE
    // Inductive step forward:
    // ~Query(x0) and Tr(x0,x1) and ~Query(x1) and Tr(x1,x2) ... and ~Query(x_{k-1}) and Tr(x_{k-1},x_k) => ~Query(x_k), is valid ->  return SAFE
    // Inductive step backward:
    // ~Init(x0) <= Tr(x0,x1) and ~Init(x1) and ... and Tr(x_{k-1},x_k) and ~Init(xk), is valid -> return SAFE

    SMTSolver solverBase(logic, SMTSolver::WitnessProduction::NONE);
    SMTSolver solverStepForward(logic, SMTSolver::WitnessProduction::NONE);
    SMTSolver solverStepBackward(logic, SMTSolver::WitnessProduction::NONE);

    PTRef negQuery = logic.mkNot(query);
    PTRef negInit = logic.mkNot(init);
    // starting point
    solverBase.assertProp(init);
    solverStepBackward.assertProp(init);
    solverStepForward.assertProp(query);
    { // Check for system with empty initial states
        auto res = solverBase.check();
        if (res == SMTSolver::Answer::UNSAT) {
            return TransitionSystemVerificationResult{VerificationAnswer::SAFE, logic.getTerm_false()};
        }
    }

    TimeMachine tm{logic};
    for (std::size_t k = 0; k < maxK; ++k) {
        PTRef versionedQuery = tm.sendFlaThroughTime(query, k);
        // Base case
        solverBase.push();
        solverBase.assertProp(versionedQuery);
        auto res = solverBase.check();
        if (res == SMTSolver::Answer::SAT) {
            if (verbosity > 0) {
                std::cout << "; KIND: Bug found in depth: " << k << std::endl;
            }
            if (computeWitness) {
                return TransitionSystemVerificationResult{VerificationAnswer::UNSAFE, k};
            } else {
                return TransitionSystemVerificationResult{VerificationAnswer::UNSAFE, 0u};
            }
        }
        if (verbosity > 1) {
            std::cout << "; KIND: No path of length " << k << " found!" << std::endl;
        }
        solverBase.pop();
        PTRef versionedTransition = tm.sendFlaThroughTime(transition, k);
        //        std::cout << "Adding transition: " << logic.pp(versionedTransition) << std::endl;
        solverBase.assertProp(versionedTransition);

        // step forward
        res = solverStepForward.check();
        if (res == SMTSolver::Answer::UNSAT) {
            if (verbosity > 0) {
                std::cout << "; KIND: Found invariant with forward induction, which is " << k << "-inductive" << std::endl;
            }
            if (computeWitness) {
                return TransitionSystemVerificationResult{VerificationAnswer::SAFE, invariantFromForwardInduction(system, k)};
            } else {
                return TransitionSystemVerificationResult{VerificationAnswer::SAFE, logic.getTerm_true()};
            }
        }
        PTRef versionedBackwardTransition = tm.sendFlaThroughTime(backwardTransition, k);
        solverStepForward.push();
        solverStepForward.assertProp(versionedBackwardTransition);
        solverStepForward.assertProp(tm.sendFlaThroughTime(negQuery,k+1));

        // step backward
        res = solverStepBackward.check();
        if (res == SMTSolver::Answer::UNSAT) {
            if (verbosity > 0) {
                std::cout << "; KIND: Found invariant with backward induction, which is " << k << "-inductive" << std::endl;
            }
            if (computeWitness) {
                return TransitionSystemVerificationResult{VerificationAnswer::SAFE, invariantFromBackwardInduction(system, k)};
            } else {
                return TransitionSystemVerificationResult{VerificationAnswer::SAFE, logic.getTerm_true()};
            }
        }
        solverStepBackward.push();
        solverStepBackward.assertProp(versionedTransition);
        solverStepBackward.assertProp(tm.sendFlaThroughTime(negInit, k+1));
    }
    return TransitionSystemVerificationResult{VerificationAnswer::UNKNOWN, 0u};
}

PTRef Kind::invariantFromForwardInduction(TransitionSystem const & transitionSystem, unsigned long k) const {
    PTRef kinductiveInvariant = logic.mkNot(transitionSystem.getQuery());
    PTRef inductiveInvariant = kinductiveToInductive(kinductiveInvariant, k, transitionSystem);
    return inductiveInvariant;
}

PTRef Kind::invariantFromBackwardInduction(TransitionSystem const & transitionSystem, unsigned long k) const {
    auto reversedSystem = TransitionSystem::reverse(transitionSystem);
    PTRef kinductiveInvariant = logic.mkNot(reversedSystem.getQuery());
    PTRef inductiveInvariant = kinductiveToInductive(kinductiveInvariant, k, reversedSystem);
    PTRef originalInvariant = logic.mkNot(inductiveInvariant);
    return originalInvariant;
}

VerificationResult BSE::run(ChcDirectedGraph const & graph) {
    // Simple version of backward symbolic execution:
    // Start from false, and try to move backward, for each node reached, test if it feasible.
    // If not, do not continue from that node
    // If init is reached and feasible => UNSAT
    // If no nodes left => SAT

    struct ARGNode {
        SymRef predicate;
        PTRef fla;
    };

    auto isFeasible = [&](PTRef fla) {
        SMTSolver solver{logic, SMTSolver::WitnessProduction::NONE};
        solver.assertProp(fla);
        auto const res = solver.check();
        return res == SMTSolver::Answer::SAT;
    };

    auto adjacencyLists = AdjacencyListsGraphRepresentation::from(graph);
    std::deque<ARGNode> queue;
    auto inQueue = [&](ARGNode const & candidate) {
        return std::find_if(queue.begin(), queue.end(), [&](ARGNode const & other) {
            return candidate.predicate == other.predicate and candidate.fla == other.fla;
        }) != queue.end();
    };
    queue.push_back(ARGNode{.predicate =  graph.getExit(), .fla = logic.getTerm_true()});
    TimeMachine tm(logic);
    while (not queue.empty()) {
        ARGNode toExpand = queue.front();
        queue.pop_front();
        PTRef shiftedFla = tm.sendFlaThroughTime(toExpand.fla, 1);
        for (EId eid : adjacencyLists.getIncomingEdgesFor(toExpand.predicate)) {
            auto source = graph.getSource(eid);
            PTRef fla = logic.mkAnd(shiftedFla, graph.getEdgeLabel(eid));
            auto vars = TermUtils(logic).predicateArgsInOrder(graph.getStateVersion(source));
            PTRef simplified = TrivialQuantifierElimination(logic).tryEliminateVarsExcept(vars, fla);
            ARGNode newNode{.predicate =  source, .fla = simplified};
            if (not inQueue(newNode)) {
                if (isFeasible(simplified)) {
                    if (source == graph.getEntry()) {
                        return {VerificationAnswer::UNSAFE, NoWitness{}};
                    }
                queue.push_back(newNode);
                }
            }
        }
    }
    return {VerificationAnswer::SAFE, NoWitness{}};
}


} // namespace golem