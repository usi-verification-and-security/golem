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
VerificationResult Kind::solve(ChcDirectedGraph const & graph) {
    if (isTrivial(graph)) {
        return solveTrivial(graph);
    }
    if (isTransitionSystem(graph)) {
        return solveTransitionSystem(graph);
    }
    return VerificationResult(VerificationAnswer::UNKNOWN);
}

VerificationResult Kind::solveTransitionSystem(ChcDirectedGraph const & graph) {
    auto ts = toTransitionSystem(graph);
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
} // namespace golem