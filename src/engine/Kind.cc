
/*
 * Copyright (c) 2022, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "Kind.h"

#include "QuantifierElimination.h"
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
            if (verbosity > 0) {
                 std::cout << "; KIND: Bug found in depth: " << k << std::endl;
            }
            if (computeWitness) {
                return GraphVerificationResult(VerificationResult::UNSAFE, InvalidityWitness::fromTransitionSystem(graph, k));
            } else {
                return GraphVerificationResult(VerificationResult::UNSAFE);
            }
        }
        if (verbosity > 1) {
            std::cout << "; KIND: No path of length " << k << " found!" << std::endl;
        }
        solverBase.pop();
        PTRef versionedTransition = tm.sendFlaThroughTime(transition, k);
//        std::cout << "Adding transition: " << logic.pp(versionedTransition) << std::endl;
        solverBase.insertFormula(versionedTransition);

        // step forward
        res = solverStepForward.check();
        if (res == s_False) {
            if (verbosity > 0) {
                std::cout << "; KIND: Found invariant with forward induction, which is " << k << "-inductive" << std::endl;
            }
            if (computeWitness) {
                return GraphVerificationResult(VerificationResult::SAFE, witnessFromForwardInduction(graph, system, k));
            } else {
                return GraphVerificationResult(VerificationResult::SAFE);
            }
        }
        PTRef versionedBackwardTransition = tm.sendFlaThroughTime(backwardTransition, k);
        solverStepForward.push();
        solverStepForward.insertFormula(versionedBackwardTransition);
        solverStepForward.insertFormula(tm.sendFlaThroughTime(negQuery,k+1));

        // step backward
        res = solverStepBackward.check();
        if (res == s_False) {
            if (verbosity > 0) {
                std::cout << "; KIND: Found invariant with backward induction, which is " << k << "-inductive" << std::endl;
            }
            return GraphVerificationResult(VerificationResult::SAFE);
        }
        solverStepBackward.push();
        solverStepBackward.insertFormula(versionedTransition);
        solverStepBackward.insertFormula(tm.sendFlaThroughTime(negInit, k+1));
    }
    return GraphVerificationResult(VerificationResult::UNKNOWN);
}

ValidityWitness Kind::witnessFromForwardInduction(ChcDirectedGraph const & graph, TransitionSystem const & transitionSystem, unsigned long k) const {
    PTRef kinductiveInvariant = logic.mkNot(transitionSystem.getQuery());
    PTRef inductiveInvariant = kinductiveToInductive(kinductiveInvariant, k, transitionSystem);
    return ValidityWitness::fromTransitionSystem(logic, graph, transitionSystem, inductiveInvariant);
}

// TODO: Unify this with TPA
PTRef Kind::kinductiveToInductive(PTRef invariant, unsigned long k, TransitionSystem const & system) const {
    /*
     * If P(x) is k-inductive invariant then the following formula is 1-inductive invariant:
     * P(x_0)
     * \land \forall x_1 (Tr(x_0,x_1) \implies P(x_1)
     * \land \forall x_1,x_2 (Tr(x_0,x_1 \land P(x_1) \land Tr(x_1,x_2) \implies P(x_2))
     * ...
     * \land \forall x_1,x_2,\ldots,x_{k-1}(Tr(x_0,x_1) \land p(x_1) \land \ldots \land P(x_{k-2}) \land Tr(x_{k-2},x_{k-1} \implies P(x_{k_1}))
     *
     * This is equivalent to
     * * P(x_0)
     * \land \neg \exists x_1 (Tr(x_0,x_1) \land \neg P(x_1)
     * \land \neg \exists x_1,x_2 (Tr(x_0,x_1 \land P(x_1) \land Tr(x_1,x_2) \land \neg P(x_2))
     * ...
     * \land \neg \exists x_1,x_2,\ldots,x_{k-1}(Tr(x_0,x_1) \land p(x_1) \land \ldots \land P(x_{k-2}) \land Tr(x_{k-2},x_{k-1} \land \neg P(x_{k_1}))
     *
     * Some computation can be re-used between iteration as going from one iteration to another (ignoring the last negated P(x_i)) we only and
     * next version of P(x_i) and Tr(x_i, x_{i+1})
     */
    vec<PTRef> stateVars = system.getStateVars();
    vec<PTRef> resArgs;
    // step 0
    resArgs.push(invariant);
    vec<PTRef> helpers;
    helpers.push(PTRef_Undef);
    PTRef transition = system.getTransition();
    auto getNextVersion = [this](PTRef fla, int shift) {
        return TimeMachine(logic).sendFlaThroughTime(fla, shift);
    };
    auto getStateVars = [this, &stateVars](int version) {
        vec<PTRef> versioned;
        TimeMachine timeMachine(logic);
        for (PTRef var : stateVars) {
            versioned.push(timeMachine.sendVarThroughTime(var, version));
        }
        return versioned;
    };
    // step 1
//    std::cout << "Step 1 out of " << k << std::endl;
    PTRef afterElimination = QuantifierElimination(logic).keepOnly(logic.mkAnd(transition, logic.mkNot(getNextVersion(invariant, 1))), stateVars);
    resArgs.push(logic.mkNot(afterElimination));
    helpers.push(transition);
    // steps 2 to k-1
    for (unsigned long i = 2; i < k; ++i) {
//        std::cout << "Step " << i << " out of " << k << std::endl;
        PTRef helper = logic.mkAnd({helpers[i-1], getNextVersion(invariant, i-1), getNextVersion(transition, i-1)});
        helper = QuantifierElimination(logic).eliminate(helper, getStateVars(i-1));
        helpers.push(helper);
        afterElimination = QuantifierElimination(logic).keepOnly(logic.mkAnd(helper, logic.mkNot(getNextVersion(invariant, i))), stateVars);
        resArgs.push(logic.mkNot(afterElimination));
    }
    return logic.mkAnd(resArgs);
}
