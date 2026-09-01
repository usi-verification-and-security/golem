/*
 * Copyright (c) 2021-2023, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

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
#include "utils/SmtSolver.h"

namespace golem {

TPASplit::~TPASplit() {
    clearReachabilitySolvers();
}

void TPASplit::clearReachabilitySolvers() {
    for (SolverWrapper * solver : reachabilitySolvers) {
        delete solver;
    }
    reachabilitySolvers.clear(true);
}

PTRef TPASplit::getExactPower(unsigned short power) const {
    assert(power < exactPowers.size());
    return exactPowers[power];
}

void TPASplit::storeExactPower(unsigned short power, PTRef tr) {
    //    std::cout << "Strengthening exact reachability on level " << power << " with " << logic.printTerm(tr) <<
    //    std::endl;
    if (power != 0 and not isPureTransitionFormula(tr)) {
        throw std::logic_error("Transition relation has some auxiliary variables!");
    }
    exactPowers.growTo(power + 1, PTRef_Undef);
    PTRef current = exactPowers[power];
    PTRef toStore = current == PTRef_Undef ? tr : TermUtils(logic).conjoin(tr, current);
    exactPowers[power] = toStore;

    reachabilitySolvers.growTo(power + 2, nullptr);
    PTRef nextLevelTransitionStrengthening = logic.mkAnd(tr, getNextVersion(tr));
    if (not reachabilitySolvers[power + 1]) {
        reachabilitySolvers[power + 1] =
            new SolverWrapperIncrementalWithRestarts(logic, nextLevelTransitionStrengthening);
        //        reachabilitySolvers[power + 1] = new SolverWrapperIncremental(logic,
        //        nextLevelTransitionStrengthening); reachabilitySolvers[power + 1] = new SolverWrapperSingleUse(logic,
        //        nextLevelTransitionStrengthening);
    } else {
        reachabilitySolvers[power + 1]->strengthenTransition(nextLevelTransitionStrengthening);
    }
}

PTRef TPASplit::getLessThanPower(unsigned short power) const {
    assert(power < lessThanPowers.size());
    return lessThanPowers[power];
}

void TPASplit::storeLessThanPower(unsigned short power, PTRef tr) {
    //    std::cout << "Strengthening less-than reachability on level " << power << " with " << logic.printTerm(tr) <<
    //    std::endl;
    if (power >= 2 and not isPureTransitionFormula(tr)) {
        throw std::logic_error("Transition relation has some auxiliary variables!");
    }
    lessThanPowers.growTo(power + 1, PTRef_Undef);
    PTRef current = lessThanPowers[power];
    PTRef toStore = current == PTRef_Undef ? tr : TermUtils(logic).conjoin(tr, current);
    lessThanPowers[power] = toStore;
}

SolverWrapper * TPASplit::getExactReachabilitySolver(unsigned short power) const {
    assert(reachabilitySolvers.size() > power);
    return reachabilitySolvers[power];
}

VerificationAnswer TPASplit::checkPower(unsigned short power) {
    TRACE(1, "Checking power " << power);
    queryCache.emplace_back();
    auto res = reachabilityQueryLessThan(init, query, power);
    if (isReachable(res)) {
        reachedStates = ReachedStates{res.refinedTarget, res.steps};
        return VerificationAnswer::UNSAFE;
    } else if (isUnreachable(res)) {
        if (verbose() > 0) { std::cout << "; System is safe up to <2^" << power + 1 << " steps" << std::endl; }
        bool fixedPointReached = checkLessThanFixedPoint(power + 1);
        if (fixedPointReached) { return VerificationAnswer::SAFE; }
        fixedPointReached = checkExactFixedPoint(power);
        if (fixedPointReached) { return VerificationAnswer::SAFE; }
    }
    res = reachabilityQueryExact(init, query, power);
    if (isReachable(res)) {
        reachedStates = ReachedStates{res.refinedTarget, res.steps};
        return VerificationAnswer::UNSAFE;
    } else if (isUnreachable(res)) {
        if (verbose() > 0) { std::cout << "; System is safe up to 2^" << power + 1 << " steps" << std::endl; }
        bool fixedPointReached = checkExactFixedPoint(power);
        if (fixedPointReached) {
            assert(explanation.invariantType != SafetyExplanation::TransitionInvariantType::NONE);
            return VerificationAnswer::SAFE;
        }
        return VerificationAnswer::UNKNOWN;
    } else {
        assert(false);
        throw std::logic_error("Unreachable code!");
    }
}

/*
 * Check if 'to' is reachable from 'from' (these are state formulas) in exactly 2^{n+1} steps (n is 'power').
 * We do this using the n-th abstraction of the transition relation and check 2-step reachability in this abstraction.
 * If 'to' is unreachable, we interpolate over the 2 step transition to obtain 1-step transition of level n+1.
 */
TPASplit::QueryResult TPASplit::reachabilityQueryExact(PTRef from, PTRef to, unsigned short power) {
    //        std::cout << "Checking exact reachability on level " << power << " from " << logic.printTerm(from) << " to
    //        " << logic.printTerm(to) << std::endl;
    TRACE(2, "Checking exact reachability on level " << power << " from " << from.x << " to " << to.x)
    assert(queryCache.size() > power);
    auto it = queryCache[power].find({from, to});
    if (it != queryCache[power].end()) {
        TRACE(1, "Query found in cache on level " << power)
        return it->second;
    }
    QueryResult result;
    PTRef goal = getNextVersion(to, 2);
    unsigned counter = 0;
    while (true) {
        TRACE(3, "Exact: Iteration " << ++counter << " on level " << power)
        auto solver =
            getExactReachabilitySolver(power + 1); // Solver at n+1 contains reachability in two steps of ATr^{=n}
        assert(solver);
        auto res = solver->checkConsistent(logic.mkAnd(from, goal));
        switch (res) {
            case ReachabilityResult::REACHABLE: {
                TRACE(3, "Top level query was reachable")
                PTRef previousTransition = getExactPower(power);
                PTRef translatedPreviousTransition = getNextVersion(previousTransition);
                auto model = solver->lastQueryModel();
                if (power == 0) { // Base case, the 2 steps of the exact transition relation have been used
                    result.result = ReachabilityResult::REACHABLE;
                    result.refinedTarget = refineTwoStepTarget(
                        from, logic.mkAnd(previousTransition, translatedPreviousTransition), goal, *model);
                    result.steps = 2;
                    TRACE(3, "Exact: Truly reachable states are " << result.refinedTarget.x)
                    TRACE(4, "Exact: Truly reachable states are " << logic.pp(result.refinedTarget))
                    assert(result.refinedTarget != logic.getTerm_false());
                    queryCache[power].insert({{from, to}, result});
                    return result;
                }
                // Create the three states corresponding to current, next and next-next variables from the query
                //              PTRef modelMidpoint = getNextVersion(extractStateFromModel(getStateVars(1), *model),
                //              -1);
                PTRef nextState = extractMidPoint(from, previousTransition, translatedPreviousTransition, goal, *model);
                //              std::cout << "Midpoint single point: " << logic.printTerm(modelMidpoint) << '\n';
                TRACE(3, "Midpoint from MBP: " << nextState.x)
                // check the reachability using lower level abstraction
                assert(power > 0);
                auto subQueryRes = reachabilityQueryExact(from, nextState, power - 1);
                if (isUnreachable(subQueryRes)) {
                    TRACE(3, "Exact: First half was unreachable, repeating...")
                    assert(getExactPower(power) != previousTransition);
                    continue; // We need to re-check this level with refined abstraction
                } else {
                    assert(isReachable(subQueryRes));
                    // TODO: check that this is really a subset of the original midpoint
                    TRACE(3, "Exact: First half was reachable")
                    nextState = extractReachableTarget(subQueryRes);
                    if (nextState == PTRef_Undef) {
                        throw std::logic_error("Refined reachable target not set in subquery!");
                    }
                    TRACE(3, "Midpoint from MBP - part 2: " << nextState.x)
                }
                unsigned stepsToMidpoint = extractStepsTaken(subQueryRes);
                // here the first half of the found path is feasible, check the second half
                subQueryRes = reachabilityQueryExact(nextState, to, power - 1);
                if (isUnreachable(subQueryRes)) {
                    TRACE(3, "Exact: Second half was unreachable, repeating...")
                    assert(getExactPower(power) != previousTransition);
                    continue; // We need to re-check this level with refined abstraction
                }
                assert(isReachable(subQueryRes));
                TRACE(3, "Exact: Second half was reachable, reachable states are "
                             << extractReachableTarget(subQueryRes).x)
                // both halves of the found path are feasible => this path is feasible!
                subQueryRes.steps += stepsToMidpoint;
                queryCache[power].insert({{from, to}, subQueryRes});
                return subQueryRes;
            }
            case ReachabilityResult::UNREACHABLE: {
                TRACE(3, "Top level query was unreachable")
                PTRef itp = solver->lastQueryTransitionInterpolant();
                itp = simplifyInterpolant(itp);
                itp = cleanInterpolant(itp);
                //                std::cout << "Strenghtening representation of exact reachability on level " << power
                //                << " :"; TermUtils(logic).printTermWithLets(std::cout, itp); std::cout << std::endl;
                TRACE(3, "Learning " << itp.x)
                TRACE(4, "Learning " << logic.pp(itp))
                assert(itp != logic.getTerm_true());
                storeExactPower(power + 1, itp);
                result.result = ReachabilityResult::UNREACHABLE;
                return result;
            }
        }
    }
}

/*
 * Check if 'to' is reachable from 'from' (these are state formulas) in less than 2^{n+1} steps (n is 'power').
 * We do this using the n-th abstractions of the transition relation (both exact and less-than).
 * Reachability in <2^{n+1} steps can happen if it is reachable in <2^n steps or if it is reachable in 2^n + <2^n steps.
 * If 'to' is unreachable, we interpolate over the 2 step transition to obtain 1-step transition of level n+1.
 */
TPASplit::QueryResult TPASplit::reachabilityQueryLessThan(PTRef from, PTRef to, unsigned short power) {
    //        std::cout << "Checking less-than reachability on level " << power << " from " << logic.printTerm(from) <<
    //        " to " << logic.printTerm(to) << std::endl;
    TRACE(2, "Checking less-than reachability on level " << power << " from " << from.x << " to " << to.x)
    if (from == to) {
        QueryResult result;
        result.result = ReachabilityResult::REACHABLE;
        result.refinedTarget = to;
        result.steps = 0;
        return result;
    }
    QueryResult result;
    PTRef goal = getNextVersion(to, 2);
    unsigned counter = 0;
    while (true) {
        SMTSolver solver(logic, SMTSolver::WitnessProduction::MODEL_AND_INTERPOLANTS);
        auto & config = solver.getConfig();
        TRACE(3, "Less-than: Iteration " << ++counter << " on level " << power)
        config.setReduction(1);
        config.setSimplifyInterpolant(4);
        config.setLRAInterpolationAlgorithm(itp_lra_alg_decomposing_strong);
        // Tr^{<n} or (Tr^{<n} concat Tr^{=n})
        PTRef previousLessThanTransition = getLessThanPower(power);
        PTRef translatedExactTransition = getNextVersion(getExactPower(power));
        PTRef currentToNextNextPreviousLessThanTransition = shiftOnlyNextVars(previousLessThanTransition);
        PTRef twoStepTransition = logic.mkOr(currentToNextNextPreviousLessThanTransition,
                                             logic.mkAnd(previousLessThanTransition, translatedExactTransition));
        // TODO: assert from and to are current-state formulas
        solver.assertProp(twoStepTransition);
        solver.assertProp(logic.mkAnd(from, goal));
        auto res = solver.check();
        if (res == SMTSolver::Answer::UNSAT) {
            TRACE(3, "Top level query was unreachable")
            auto itpContext = solver.getInterpolationContext();
            vec<PTRef> itps;
            ipartitions_t mask = 1;
            itpContext->getSingleInterpolant(itps, mask);
            assert(itps.size() == 1);
            config.setLRAInterpolationAlgorithm(itp_lra_alg_strong); // compute also McMillan's interpolant
            itpContext->getSingleInterpolant(itps, mask);
            assert(itps.size() == 2);
            PTRef itp = logic.mkAnd(itps);
            // replace next-next variables with next-variables
            itp = simplifyInterpolant(itp);
            itp = cleanInterpolant(itp);
            TRACE(3, "Learning " << itp.x)
            TRACE(4, "Learning " << logic.pp(itp))
            // If itp == logic.getTerm_true, then the error states were trivially unreachable
            if (itp == logic.getTerm_true()) { assert(power == 0); }
            storeLessThanPower(power + 1, itp);
            result.result = ReachabilityResult::UNREACHABLE;
            return result;
        } else if (res == SMTSolver::Answer::SAT) {
            TRACE(3, "Top level query was reachable")
            auto model = solver.getModel();
            if (model->evaluate(currentToNextNextPreviousLessThanTransition) == logic.getTerm_true()) {
                // First disjunct was responsible for the positive answer, check it
                TRACE(3, "First disjunct was satisfiable")
                if (power == 0) { // This means the goal is reachable in 0 steps, no need to re-check anythin
                    result.result = ReachabilityResult::REACHABLE;
                    result.refinedTarget = logic.mkAnd(from, to);
                    result.steps = 0;
                    TRACE(3, "Less-than: Truly reachable states are " << result.refinedTarget.x)
                    TRACE(4, "Less-than: Truly reachable states are " << logic.pp(result.refinedTarget))
                    return result;
                }
                auto subQueryRes = reachabilityQueryLessThan(from, to, power - 1);
                if (isReachable(subQueryRes)) {
                    TRACE(3, "Less-than: First half was reachable!")
                    return subQueryRes;
                } else {
                    TRACE(3, "Less-than: First half was unreachable, repeating...")
                    assert(isUnreachable(subQueryRes));
                    assert(getLessThanPower(power) != previousLessThanTransition);
                    continue;
                }
            } else {
                // Second disjunct was responsible for the positive answer
                assert(model->evaluate(logic.mkAnd(previousLessThanTransition, translatedExactTransition)) ==
                       logic.getTerm_true());
                TRACE(3, "Second disjunct was satisfiable")
                if (power == 0) { //  Reachable in exactly 1 step
                    result.result = ReachabilityResult::REACHABLE;
                    // TODO: simplify to refine only one step of exact relation (which is just Tr)
                    result.refinedTarget = refineTwoStepTarget(
                        from, logic.mkAnd(previousLessThanTransition, translatedExactTransition), goal, *model);
                    result.steps = 1;
                    TRACE(3, "Less-than: Truly reachable states are " << result.refinedTarget.x)
                    return result;
                }
                PTRef nextState =
                    extractMidPoint(from, previousLessThanTransition, translatedExactTransition, goal, *model);
                TRACE(3, "Midpoint is " << nextState.x)
                TRACE(4, "Midpoint is " << logic.pp(nextState));
                // check the reachability using lower level abstraction
                auto subQueryRes = reachabilityQueryLessThan(from, nextState, power - 1);
                if (isUnreachable(subQueryRes)) {
                    TRACE(3, "Less-than: First half was unreachable, repeating...")
                    assert(getLessThanPower(power) != previousLessThanTransition);
                    continue; // We need to re-check this level with refined abstraction
                } else {
                    assert(isReachable(subQueryRes));
                    TRACE(3, "Less-than: First half was reachable!")
                    nextState = extractReachableTarget(subQueryRes);
                    if (nextState == PTRef_Undef) {
                        throw std::logic_error("Refined reachable target not set in subquery!");
                    }
                    TRACE(3, "Modified midpoint : " << nextState.x)
                    TRACE(4, "Modified midpoint : " << logic.pp(nextState))
                }
                unsigned stepsToMidpoint = extractStepsTaken(subQueryRes);
                // here the first half of the found path is feasible, check the second half
                PTRef previousExactTransition = getExactPower(power);
                (void)previousExactTransition;
                subQueryRes = reachabilityQueryExact(nextState, to, power - 1);
                if (isUnreachable(subQueryRes)) {
                    assert(getExactPower(power) != previousExactTransition);
                    TRACE(3, "Less-than: Second half was unreachable, repeating...")
                    continue; // We need to re-check this level with refined abstraction
                }
                assert(isReachable(subQueryRes));
                TRACE(3, "Less-than: Second half was reachable, reachable states are "
                             << extractReachableTarget(subQueryRes).x)
                // both halves of the found path are feasible => this path is feasible!
                subQueryRes.steps += stepsToMidpoint;
                return subQueryRes;
            }
        } else {
            throw std::logic_error("TPA: Unexpected situation checking reachability");
        }
    }
}

void TPASplit::resetPowers() {
    this->exactPowers.clear();
    this->lessThanPowers.clear();
    this->clearReachabilitySolvers();
    storeExactPower(0, transition); // ATr^{=0} = Tr
    lessThanPowers.push(identity);  // Atr^{<0} = Id
}

bool TPASplit::verifyPower(unsigned short power, TPAType relationType) const {
    if (relationType == TPAType::LESS_THAN) {
        return verifyLessThanPower(power);
    } else {
        return verifyExactPower(power);
    }
}

bool TPASplit::verifyLessThanPower(unsigned short power) const {
    assert(power > 0);
    SMTSolver solver(logic, SMTSolver::WitnessProduction::NONE);
    PTRef current = getLessThanPower(power);
    PTRef previous = getLessThanPower(power - 1);
    PTRef previousExact = getExactPower(power - 1);
    //    std::cout << "Previous exact: " << logic.printTerm(previousExact) << std::endl;
    // check that previous or previousExact concatenated with previous implies current
    solver.assertProp(logic.mkOr(shiftOnlyNextVars(previous), logic.mkAnd(previous, getNextVersion(previousExact))));
    solver.assertProp(logic.mkNot(shiftOnlyNextVars(current)));
    auto res = solver.check();
    return res == SMTSolver::Answer::UNSAT;
}

bool TPASplit::verifyExactPower(unsigned short power) const {
    assert(power >= 1);
    if (power > 1) {
        bool previousRes = verifyExactPower(power - 1);
        if (not previousRes) { return false; }
    }
    SMTSolver solver(logic, SMTSolver::WitnessProduction::NONE);
    PTRef current = getExactPower(power);
    PTRef previous = getExactPower(power - 1);
    //    std::cout << "Exact on level " << power << " : " << logic.printTerm(current) << std::endl;
    //    std::cout << "Exact on level " << power - 1 << " : " << logic.printTerm(previous) << std::endl;
    // check that previous or previousExact concatenated with previous implies current
    solver.assertProp(logic.mkAnd(previous, getNextVersion(previous)));
    solver.assertProp(logic.mkNot(shiftOnlyNextVars(current)));
    auto res = solver.check();
    return res == SMTSolver::Answer::UNSAT;
}

bool TPASplit::checkExactFixedPoint(unsigned short power) {
    assert(power == 0 or verifyExactPower(power));
    for (unsigned short i = 1; i <= power; ++i) {
        PTRef currentLevelTransition = getExactPower(i);
        PTRef currentTwoStep = logic.mkAnd(currentLevelTransition, getNextVersion(currentLevelTransition));
        PTRef shifted = shiftOnlyNextVars(currentLevelTransition);
        SMTSolver solver(logic, SMTSolver::WitnessProduction::NONE);
        solver.assertProp(logic.mkAnd({currentTwoStep, logic.mkNot(shifted)}));
        auto satres = solver.check();
        char restrictedInvariant = 0;
        if (satres != SMTSolver::Answer::UNSAT) {
            solver.push();
            solver.assertProp(getNextVersion(logic.mkAnd(init, getLessThanPower(i)), -1));
            satres = solver.check();
            if (satres == SMTSolver::Answer::UNSAT) { restrictedInvariant = 1; }
        }
        if (satres != SMTSolver::Answer::UNSAT) {
            solver.pop();
            solver.push();
            solver.assertProp(logic.mkAnd(getNextVersion(getLessThanPower(i), 2), getNextVersion(query, 3)));
            satres = solver.check();
            if (satres == SMTSolver::Answer::UNSAT) { restrictedInvariant = 2; }
        }
        if (satres == SMTSolver::Answer::UNSAT) {
            if (verbose() > 0) {
                std::cout << "; Fixed point detected in equals relation on level " << i << " from " << power
                          << std::endl;
                std::cout << "; Fixed point detected for ";
                switch (restrictedInvariant) {
                    case 0:
                        std::cout << "whole transition relation";
                        break;
                    case 1:
                        std::cout << "transition relation restricted to init";
                        break;
                    case 2:
                        std::cout << "transition relation restricted to bad";
                        break;
                    default:
                        assert(false);
                }
                std::cout << std::endl;
            }
            explanation.invariantType =
                restrictedInvariant == 0   ? SafetyExplanation::TransitionInvariantType::UNRESTRICTED
                : restrictedInvariant == 1 ? SafetyExplanation::TransitionInvariantType::RESTRICTED_TO_INIT
                                           : SafetyExplanation::TransitionInvariantType::RESTRICTED_TO_QUERY;
            explanation.relationType = TPAType::EQUALS;
            explanation.inductivnessPowerExponent = i;
            explanation.safeTransitionInvariant =
                logic.mkOr(shiftOnlyNextVars(getPower(i, TPAType::LESS_THAN)),
                           logic.mkAnd(getPower(i, TPAType::LESS_THAN), getNextVersion(getPower(i, TPAType::EQUALS))));
            return true;
        }
    }
    return false;
}

PTRef TPASplit::getPower(unsigned short power, TPAType relationType) const {
    if (relationType == TPAType::LESS_THAN) { return getLessThanPower(power); }
    assert(relationType == TPAType::EQUALS);
    return getExactPower(power);
}

PTRef TPASplit::inductiveInvariantFromEqualsTransitionInvariant() const {
    unsigned short power = explanation.inductivnessPowerExponent;
    assert(verifyLessThanPower(power));
    assert(verifyExactPower(power));
    //    std::cout << "Less-than transition: " << logic.printTerm(getLessThanPower(power)) << '\n';
    //    std::cout << "Exact transition: " << logic.printTerm(getExactPower(power)) << std::endl;
    PTRef transitionInvariant = logic.mkOr(shiftOnlyNextVars(getLessThanPower(power)),
                                           logic.mkAnd(getLessThanPower(power), getNextVersion(getExactPower(power))));
    //    std::cout << "Transition invariant: " << logic.printTerm(transitionInvariant) << std::endl;
    PTRef stateInvariant =
        QuantifierElimination(logic).eliminate(logic.mkAnd(init, transitionInvariant), getStateVars(0));
    //    std::cout << "After eliminating current state vars: " << logic.printTerm(stateInvariant) << std::endl;
    stateInvariant = QuantifierElimination(logic).eliminate(stateInvariant, getStateVars(1));
    stateInvariant = getNextVersion(stateInvariant, -2);
    //    std::cout << "State invariant: " << logic.printTerm(stateInvariant) << std::endl;
    if (power >= 64) { return PTRef_Undef; } // MB: Cannot shift more than 63 bits
    unsigned long k = 1ul << power;
    assert(verifyKinductiveInvariant(stateInvariant, k));
    //    std::cout << "K-inductivness of invariant sucessfully checked for k=" << k << std::endl;
    TransitionSystem transitionSystem(logic, std::make_unique<SystemType>(stateVariables, auxiliaryVariables, logic),
                                      init, transition, query);
    PTRef inductiveInvariant = kinductiveToInductive(stateInvariant, k, transitionSystem);
    //    std::cout << "Inductive invariant: " << logic.printTerm(inductiveInvariant) << std::endl;
    //    std::cout << "Inductive invariant computed!" << std::endl;
    assert(verifyKinductiveInvariant(inductiveInvariant, 1));
    return inductiveInvariant;
}

} // namespace golem
