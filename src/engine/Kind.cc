
/*
 * Copyright (c) 2022, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "Kind.h"

#include "TermUtils.h"
#include "TransformationUtils.h"

GraphVerificationResult Kind::solve(ChcDirectedGraph const & system) {
    if (isTransitionSystem(system)) {
        auto ts = toTransitionSystem(system, logic);
        return solveTransitionSystem(*ts, system);
    }
    return GraphVerificationResult(VerificationResult::UNKNOWN);
}

namespace{
PTRef reverseTransition(Logic & logic, PTRef transition, std::vector<PTRef> const & stateVars, std::vector<PTRef> const & nextStateVars) {
    TimeMachine tm(logic);
    std::vector<PTRef> helperVars;
    helperVars.reserve(stateVars.size());
    std::transform(stateVars.begin(), stateVars.end(), std::back_inserter(helperVars), [&](PTRef var) {
        return tm.sendVarThroughTime(var,2);
    });
    TermUtils utils(logic);
    TermUtils::substitutions_map subst;
    std::size_t varCount = stateVars.size();
    for (auto i = 0u; i < varCount; ++i) {
        subst.insert({stateVars[i], helperVars[i]});
    }
    transition = utils.varSubstitute(transition, subst);

    subst.clear();
    for (auto i = 0u; i < varCount; ++i) {
        subst.insert({nextStateVars[i], stateVars[i]});
    }
    transition = utils.varSubstitute(transition, subst);

    subst.clear();
    for (auto i = 0u; i < varCount; ++i) {
        subst.insert({helperVars[i], nextStateVars[i]});
    }
    transition = utils.varSubstitute(transition, subst);

    return transition;
}
}

GraphVerificationResult Kind::solveTransitionSystem(TransitionSystem const & system, ChcDirectedGraph const & graph) {
    std::size_t maxK = std::numeric_limits<std::size_t>::max();
    PTRef init = system.getInit();
    PTRef query = system.getQuery();
    PTRef transition = system.getTransition();
    PTRef backwardTransition = reverseTransition(logic, transition, system.getStateVars(), system.getNextStateVars());

    // Base step: Init(x0) and Tr^k(x0,xk) and Query(xk), if SAT -> return UNSAFE
    // Inductive step forward:
    // ~Query(x0) and Tr(x0,x1) and ~Query(x1) and Tr(x1,x2) ... and ~Query(x_{k-1}) and Tr(x_{k-1},x_k) => ~Query(x_k), is valid ->  return SAFE
    // Inductive step backward:
    // ~Init(x0) <= Tr(x0,x1) and ~Init(x1) and ... and Tr(x_{k-1},x_k) and ~Init(xk), is valid -> return SAFE

    SMTConfig configBase;
    SMTConfig configStepForward;
    SMTConfig configStepBackward;
    MainSolver solverBase(logic, configBase, "KIND-base");
    MainSolver solverStepForward(logic, configStepForward, "KIND-stepForward");
    MainSolver solverStepBackward(logic, configStepBackward, "KIND-stepBackward");

    PTRef negQuery = logic.mkNot(query);
    PTRef negInit = logic.mkNot(init);
    // starting point
    solverBase.insertFormula(init);
    solverStepBackward.insertFormula(init);
    solverStepForward.insertFormula(query);
    { // Check for system with empty initial states
        auto res = solverBase.check();
        if (res == s_False) {
            return GraphVerificationResult{VerificationResult::SAFE};
        }
    }

    TimeMachine tm{logic};
    for (std::size_t k = 0; k < maxK; ++k) {
        PTRef versionedQuery = tm.sendFlaThroughTime(query, k);
        // Base case
        solverBase.push();
        solverBase.insertFormula(versionedQuery);
        auto res = solverBase.check();
        if (res == s_True) {
            // std::cout << "Bug found in depth: " << k << std::endl;
            return GraphVerificationResult(VerificationResult::UNSAFE, InvalidityWitness::fromTransitionSystem(graph, k));
        }
//        std::cout << "No path of length " << currentUnrolling << " found!\n";
        solverBase.pop();
        PTRef versionedTransition = tm.sendFlaThroughTime(transition, k);
//        std::cout << "Adding transition: " << logic.pp(versionedTransition) << std::endl;
        solverBase.insertFormula(versionedTransition);

        // step forward
        res = solverStepForward.check();
        if (res == s_False) {
            return GraphVerificationResult(VerificationResult::SAFE);
        }
        PTRef versionedBackwardTransition = tm.sendFlaThroughTime(backwardTransition, k);
        solverStepForward.push();
        solverStepForward.insertFormula(versionedBackwardTransition);
        solverStepForward.insertFormula(tm.sendFlaThroughTime(negQuery,k+1));

        // step backward
        res = solverStepBackward.check();
        if (res == s_False) {
            return GraphVerificationResult(VerificationResult::SAFE);
        }
        solverStepBackward.push();
        solverStepBackward.insertFormula(versionedTransition);
        solverStepBackward.insertFormula(tm.sendFlaThroughTime(negInit, k+1));
    }
    return GraphVerificationResult(VerificationResult::UNKNOWN);
}
