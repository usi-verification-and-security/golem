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
#include "unsatcores/UnsatCore.h"
#include "utils/InductiveInterpolants.h"
#include "utils/SmtSolver.h"

#define GENERALIZE 1
#define INDITP 0
#define PROPAGATE 1
#define BOTH 0

namespace golem {

bool TPABasic::checkLemma(unsigned short power, PTRef lemma01, bool inductive) const {
    SMTSolver solver(logic, SMTSolver::WitnessProduction::NONE);
    PTRef AT01 = getLevelTransition(power);
    PTRef AT12 = getNextVersion(AT01);
    PTRef lemma12 = getNextVersion(lemma01);
    PTRef lemma02 = shiftOnlyNextVars(lemma01);

    bool ok = true;

    // Check: T -> AT
    solver.push();
    solver.assertProp(logic.mkOr(transition, identity));
    solver.assertProp(logic.mkNot(AT01));
    if (solver.check() != SMTSolver::Answer::UNSAT) {
        std::cerr << "AT is not implied by T!" << std::endl;
        ok = false;
    }
    solver.pop();

    // Check: T -> lemma
    solver.push();
    solver.assertProp(logic.mkOr(transition, identity));
    solver.assertProp(logic.mkNot(lemma01));
    if (solver.check() != SMTSolver::Answer::UNSAT) {
        std::cerr << "Lemma is not implied by T!" << std::endl;
        ok = false;
    }
    solver.pop();

    if (not inductive) {
        // Check (A01 & A12) -> lemma02 
        solver.push();
        solver.assertProp(AT01);
        solver.assertProp(AT12);
        solver.assertProp(logic.mkNot(lemma02));
        if (solver.check() != SMTSolver::Answer::UNSAT) {
            std::cerr << "Lemma is not implied by previous frames" << std::endl;
            ok = false;
        }
        solver.pop();
    } else {
        // Check (A01 & lemma01 & A12 & lemma12) -> lemma02 
        solver.push();
        solver.assertProp(AT01);
        solver.assertProp(AT12);
        solver.assertProp(lemma01);
        solver.assertProp(lemma12);
        solver.assertProp(logic.mkNot(lemma02));
        if (solver.check() != SMTSolver::Answer::UNSAT) {
            std::cerr << "Lemma is not inductive from by previous frames" << std::endl;
            ok = false;
        }
        solver.pop();
    }

    return ok;
}

PTRef TPABasic::generalize(unsigned short power, PTRef lemma) const {
    SMTSolver solver(logic, SMTSolver::WitnessProduction::ONLY_UNSAT_CORE);

    assert(checkLemma(power, lemma, false));

    const auto& candidates = TermUtils(logic).getTopLevelDisjuncts(lemma);
    vec<PTRef> assumedSources1, assumedSources2, assumedTargets;
    std::map<PTRef, PTRef> mapping;
    assumedSources1.capacity(candidates.size());
    assumedSources2.capacity(candidates.size());
    assumedTargets.capacity(candidates.size());

    /*
      bigand_i a_i     // named assumptions
      & (
         T(x, x'')     // base
         or
         (             // inductive step
           TA^n(x, x') & TA^n(x', x'')
           & bigor_i(a_i & l_i(x, x')) & // assumed sources 1
           & bigor_i(a_i & l_i(x', x'')) // assumed sources 2
         )
        )
      & bigand_i (a_i -> not l_i(x, x''))
                      // assumed targets
     */
    static std::size_t i = 0;
    for (const auto candidate : candidates) {
        std::string name = "_assume#indgen#" + std::to_string(i++);
        PTRef assumption = logic.mkBoolVar(name.c_str());
        mapping[assumption] = candidate;
        PTRef source1 = logic.mkAnd(assumption, candidate);
        PTRef source2 = logic.mkAnd(assumption, getNextVersion(candidate));
        assumedSources1.push(source1);
        assumedSources2.push(source2);
        PTRef notTarget = logic.mkNot(shiftOnlyNextVars(candidate));
        assumedTargets.push(logic.mkImpl(assumption, notTarget));

        // assert assumptions
        bool added = solver.tryAssertNamedProp(assumption, name);
        assert(added);
    }

    PTRef absTrans = getLevelTransition(power);
    PTRef inductiveStep = \
        logic.mkAnd({
                absTrans, getNextVersion(absTrans),
                logic.mkOr(assumedSources1),
                logic.mkOr(assumedSources2)
            });
    PTRef base = logic.mkOr(identity, transition);
    PTRef baseOrindStep = \
        logic.mkOr(shiftOnlyNextVars(base), inductiveStep);
    solver.assertProp(baseOrindStep);

    PTRef target = logic.mkAnd(assumedTargets);
    solver.assertProp(target);

    auto res = solver.check();
    if (res != SMTSolver::Answer::UNSAT) {
        throw std::logic_error("Error in Generalize: formula is not unsatisfiable!");
    }

    auto core = solver.getUnsatCore();
    vec<PTRef> inductiveDisjs;
    const auto& coreAssumptions = core->getTerms();
    for (auto term : coreAssumptions) { inductiveDisjs.push(mapping[term]); }
    assert(inductiveDisjs.size() > 0);
    auto newLemma = logic.mkOr(inductiveDisjs);

    TRACE(3, "==== [GENERALIZE] Old Lemma: " << logic.pp(lemma));
    TRACE(3, "==== [GENERALIZE] New Lemma: " << logic.pp(newLemma));

    assert(checkLemma(power, newLemma, true));

    return newLemma;
}

PTRef TPABasic::inductiveItp(unsigned short power, PTRef goal) const {
    PTRef level = getLevelTransition(power);
    PTRef twoAbsTrans = logic.mkAnd(level, getNextVersion(level));

    auto getVarsAt = [this](int level){ return getStateVars(level); };

    PTRef lemma = inductiveTransConflict(logic,
                                         logic.mkOr(identity, transition),
                                         twoAbsTrans, goal,
                                         getVarsAt
                                         );
    return lemma;
}

// Single hierarchy version:
TPABasic::~TPABasic() {
    clearReachabilitySolvers();
}

void TPABasic::clearReachabilitySolvers() {
    for (SolverWrapper * solver : reachabilitySolvers) {
        delete solver;
    }
    reachabilitySolvers.clear(true);
}

PTRef TPABasic::getLevelTransition(unsigned short power) const {
    assert(power < transitionHierarchy.size());
    return logic.mkAnd(transitionHierarchy[power]);
}

void TPABasic::storeLevelTransition(unsigned short power, PTRef tr) {
    TRACE(3, "Strengthening level " << power << " with " << logic.printTerm(tr));
    if (power != 0 and not isPureTransitionFormula(tr)) {
        throw std::logic_error("Transition relation has some auxiliary variables!");
    }
    for (auto i = transitionHierarchy.size(); i <= power; ++i) {
        transitionHierarchy.push_back({});
    }

    vec<PTRef> allTr = TermUtils(logic).getTopLevelConjuncts(tr);

#if PROPAGATE || INDITP
    for (auto i = 0; i <= power; ++i) {
        auto& level = transitionHierarchy[i];
        for (auto t : allTr) {
            if (std::find(level.begin(), level.end(), t) == level.end()) {
                TRACE(2, "[+] Adding " << t.x << " in TA " << i);
                transitionHierarchy[i].push(t);
            } else {
                TRACE(4, "   Trying to add the same lemma again. Skipping...");
                // TODO: skip also asserting in the solver.
            }
        }
    }
#else
    for (auto t : allTr) {
        transitionHierarchy[power].push(t);
    }
#endif

    reachabilitySolvers.growTo(power + 2, nullptr);
    PTRef nextLevelTransitionStrengthening = logic.mkAnd(tr, getNextVersion(tr));
#if PROPAGATE || INDITP
    for (auto i = 1; i <= power + 1; ++i) {
#else
    {
    auto i = power + 1;
#endif
    if (not reachabilitySolvers[i]) {
        reachabilitySolvers[i] =
            new SolverWrapperIncrementalWithRestarts(logic, nextLevelTransitionStrengthening);
        //        reachabilitySolvers[power + 1] = new SolverWrapperIncremental(logic,
        //        nextLevelTransitionStrengthening); reachabilitySolvers[power + 1] = new SolverWrapperSingleUse(logic,
        //        nextLevelTransitionStrengthening);
    } else {
        reachabilitySolvers[i]->strengthenTransition(nextLevelTransitionStrengthening);
    }
    }

}

SolverWrapper * TPABasic::getReachabilitySolver(unsigned short power) const {
    assert(reachabilitySolvers.size() > power);
    return reachabilitySolvers[power];
}

VerificationAnswer TPABasic::checkPower(unsigned short power) {
    TRACE(1, "\n----------\nChecking power " << power)
    queryCache.emplace_back();
    auto res = reachabilityQuery(init, query, power);
    if (isReachable(res)) {
        reachedStates = ReachedStates{res.refinedTarget, res.steps};
        return VerificationAnswer::UNSAFE;
    } else if (isUnreachable(res)) {
        if (verbose() > 0) { std::cout << "; System is safe up to <=2^" << power + 1 << " steps" << std::endl; }
        TRACE(1, "System is safe up to <=2^" << power + 1 << "steps.");
        // Check if we have not reached fixed point.
#if PROPAGATE
        bool fixpoint = propagateTransitions(power + 1);
        if (fixpoint) { return VerificationAnswer::SAFE; }
#endif
        bool fixedPointReached = checkLessThanFixedPoint(power + 1);
        if (fixedPointReached) { return VerificationAnswer::SAFE; }
    }
    return VerificationAnswer::UNKNOWN;
}

/*
 * Check if 'to' is reachable from 'from' (these are state formulas) in  <=2^{n+1} steps (n is 'power').
 * We do this using the n-th abstraction of the transition relation and check 2-step reachability in this abstraction.
 * If 'to' is unreachable, we interpolate over the 2 step transition to obtain 1-step transition of level n+1.
 */
TPABasic::QueryResult TPABasic::reachabilityQuery(PTRef from, PTRef to, unsigned short power) {
    //        std::cout << "Checking LEQ reachability on level " << power << " from " << logic.printTerm(from) << " to "
    //        << logic.printTerm(to) << std::endl;
    INCR_INDENT;
    TRACE(2, "[RQ] Checking LEQ reachability on level " << power << " from " << from.x << " to " << to.x)
    assert(queryCache.size() > power);
    auto it = queryCache[power].find({from, to});
    if (it != queryCache[power].end()) {
        TRACE(1, "Query found in cache: truly reachable on level " << power);
        DECR_INDENT;
        return it->second;
    }
    QueryResult result;
    PTRef goal = getNextVersion(to, 2);
    unsigned counter = 0;
    while (true) {
        TRACE(3, "... Iteration " << ++counter << " on level " << power);
        TRACE(2, "[?] Can " << from.x << " reach " << to.x << " in <=2^" << power + 1 << " steps?")
        auto solver = getReachabilitySolver(power + 1);
        assert(solver);
        auto res = solver->checkConsistent(logic.mkAnd(from, goal));
        switch (res) {
            case ReachabilityResult::REACHABLE: {
                TRACE(2, "[y] " << from.x << " reaches " << to.x << " in <=2^" << power + 1 << " steps.");
                TRACE(3, "Top level query was reachable")
                PTRef previousTransition = getLevelTransition(power);
                PTRef translatedPreviousTransition = getNextVersion(previousTransition);
                auto model = solver->lastQueryModel();
                if (power == 0) { // Base case, <=2 steps of the exact transition relation have been used
                    result.result = ReachabilityResult::REACHABLE;
                    bool firstStepTaken = model->evaluate(identity) == logic.getTerm_false();
                    bool secondStepTaken = model->evaluate(getNextVersion(identity)) == logic.getTerm_false();
                    assert(
                        (not firstStepTaken or model->evaluate(transition) == logic.getTerm_true()) and
                        (not secondStepTaken or model->evaluate(getNextVersion(transition)) == logic.getTerm_true()));
                    result.refinedTarget = refineTwoStepTarget(
                           from, logic.mkAnd(previousTransition, translatedPreviousTransition), goal, *model);
                    result.steps = firstStepTaken + secondStepTaken;
                    // MB: Refined steps are computed from the whole formula representing 0-2 steps.
                    //     It might be possible that the step count is not correct ?!
                    TRACE(2, "[!] Exact: Truly reachable states are " << result.refinedTarget.x);
                    DECR_INDENT;
                    assert(result.refinedTarget != logic.getTerm_false());
                    queryCache[power].insert({{from, to}, result});
                    return result;
                }
                // Create the three states corresponding to current, next and next-next variables from the query
                PTRef nextState = extractMidPoint(from, previousTransition, translatedPreviousTransition, goal, *model);
                //              std::cout << "Midpoint single point: " << logic.printTerm(modelMidpoint) << '\n';
                TRACE(2, "[Q] Considering MidPoint query as target: " << nextState.x)
                assert(power != 0);
                // check the reachability using lower level abstraction
                auto subQueryRes = reachabilityQuery(from, nextState, power - 1);
                if (isUnreachable(subQueryRes)) {
                    TRACE(3, "Exact: First half was unreachable, repeating...");
                    assert(getLevelTransition(power) != previousTransition);
                    continue; // We need to re-check this level with refined abstraction
                } else {
                    assert(isReachable(subQueryRes));
                    TRACE(3, "Exact: First half was reachable");
                    nextState = extractReachableTarget(subQueryRes);
                    TRACE(2, "[Q] Considering MidPoint query as source: " << nextState.x);
                    TRACE(3, "Midpoint from MBP - part 2: " << nextState.x)
                    if (nextState == PTRef_Undef) {
                        throw std::logic_error("Refined reachable target not set in subquery!");
                    }
                }
                unsigned stepsToMidpoint = extractStepsTaken(subQueryRes);
                // here the first half of the found path is feasible, check the second half
                subQueryRes = reachabilityQuery(nextState, to, power - 1);
                if (isUnreachable(subQueryRes)) {
                    TRACE(3, "Exact: Second half was unreachable, repeating...")
                    assert(getLevelTransition(power) != previousTransition);
                    continue; // We need to re-check this level with refined abstraction
                }
                assert(isReachable(subQueryRes));
                TRACE(3, "Exact: Second half was reachable, reachable states are "
                             << extractReachableTarget(subQueryRes).x)
                // both halves of the found path are feasible => this path is feasible!
                subQueryRes.steps += stepsToMidpoint;
                queryCache[power].insert({{from, to}, subQueryRes});
                TRACE(2, "[R] Query " << to.x << " was reachable");
                DECR_INDENT;
                return subQueryRes;
            }
            case ReachabilityResult::UNREACHABLE: {
                TRACE(3, "Top level query was unreachable");
                TRACE(2, "[x] " << from.x << " cannot reach " << to.x << " in <=2^" << power + 1 << " steps.");

#if INDITP || BOTH
                PTRef lemma = inductiveItp(power, logic.mkAnd(from, goal));
#if GENERALIZE
                lemma = generalize(power, lemma);
#endif
#endif

#if !INDITP || BOTH
                PTRef itp = solver->lastQueryTransitionInterpolant();
                itp = simplifyInterpolant(itp);
                itp = cleanInterpolant(itp);
#if GENERALIZE
                itp = generalize(power, itp);
#endif
#endif

#if INDITP || BOTH
                TRACE(2, "[+] Learning " << lemma.x << " in power: " << power + 1);
                TRACE(4, "Learning " << logic.pp(lemma));
                TRACE(2, "[U] Query " << to.x << " is NOT reachable");
                // If itp == logic.getTerm_true, then the error states were trivially unreachable
                if (lemma == logic.getTerm_true()) { assert(power == 0); }
                storeLevelTransition(power + 1, lemma);
#endif

#if !INDITP || BOTH
                TRACE(2, "[+] Learning " << itp.x << " in power: " << power + 1);
                TRACE(4, "Learning " << logic.pp(itp));
                TRACE(2, "[U] Query " << to.x << " is NOT reachable");
                // If itp == logic.getTerm_true, then the error states were trivially unreachable
                if (itp == logic.getTerm_true()) { assert(power == 0); }
                storeLevelTransition(power + 1, itp);
#endif

                // if (not implies(itp, lemma, logic)) {
                //     TRACE(2, "======== New ITP is stronger!");
                //     TRACE(2, "New ITP: " << logic.pp(lemma));
                // //     TRACE(2, "Old ITP: " << logic.pp(itp));
                //     itp = lemma;
                // }

                result.result = ReachabilityResult::UNREACHABLE;
                DECR_INDENT;
                return result;
            }
        }
    }
}

bool TPABasic::propagateTransitions(unsigned short power) {
    TRACE(2, "[->] Trying to propagate lemmas...")
    SMTSolver solver(logic, SMTSolver::WitnessProduction::NONE);
    for (auto i = 0; i < transitionHierarchy.size() - 1; ++i) {
        solver.push();
        auto currentLevel = getLevelTransition(i);
        solver.assertProp(currentLevel);
        solver.assertProp(getNextVersion(currentLevel));

        vec<PTRef> propagated;
        bool allPropagated = true;
        const auto& candidates = transitionHierarchy[i];
        const auto& nextLemmas = transitionHierarchy[i + 1];
        for (PTRef candidate : candidates) {
            // ANNA: todo: we can skip rightinvariant lemmas which are automatically pushed
            bool duplicate = \
                std::find(nextLemmas.begin(), nextLemmas.end(), candidate) != nextLemmas.end();
            if (duplicate) {
                continue;
            }
            // Check if AT^i(x,x') & AT^i(x', x'') -> candidate(x, x'')
            solver.push();
            auto shiftedCandidate = shiftOnlyNextVars(candidate);
            solver.assertProp(logic.mkNot(shiftedCandidate));
            if (solver.check() == SMTSolver::Answer::UNSAT) {
                TRACE(1, "[push] Propagate " << candidate.x << " to " << i + 1);
                propagated.push(candidate);
            } else {
                allPropagated = false;
            }
            solver.pop();
        }
        for (PTRef lemma : propagated) {
            // ANNA: TODO: add a flag to avoid searching it in previous levels
            storeLevelTransition(i + 1, lemma);
        }
        if (i < power and allPropagated) {
            explanation.invariantType = SafetyExplanation::TransitionInvariantType::UNRESTRICTED;
            explanation.relationType = TPAType::LESS_THAN;
            explanation.fixedPointType = SafetyExplanation::FixedPointType::RIGHT;
            explanation.inductivnessPowerExponent = 0;
            explanation.safeTransitionInvariant = getLevelTransition(i);
            return true;
        }
        solver.pop();
    }
    return false;
}

void TPABasic::resetPowers() {
    this->transitionHierarchy.clear();
    this->clearReachabilitySolvers();
    storeLevelTransition(0, logic.mkOr(identity, transition));
}

bool TPABasic::verifyPower(unsigned short power, TPAType relationType) const {
    assert(relationType == TPAType::LESS_THAN);
    (void)relationType;
    return verifyPower(power);
}

bool TPABasic::verifyPower(unsigned short level) const {
    assert(level > 0);
    SMTSolver solver(logic, SMTSolver::WitnessProduction::NONE);
    PTRef current = getLevelTransition(level);
    PTRef previous = getLevelTransition(level - 1);
    solver.assertProp(logic.mkAnd(previous, getNextVersion(previous)));
    solver.assertProp(logic.mkNot(shiftOnlyNextVars(current)));
    solver.assertProp(logic.mkNot(shiftOnlyNextVars(current)));
    auto res = solver.check();
    return res == SMTSolver::Answer::UNSAT;
}

PTRef TPABasic::getPower(unsigned short power, TPAType relationType) const {
    assert(relationType == TPAType::LESS_THAN);
    (void)relationType;
    return getLevelTransition(power);
}

void TPABasic::learnInvariant(PTRef invariant, SafetyExplanation::FixedPointType alignment) {
    TPABase::learnInvariant(invariant, alignment);
    if (alignment == SafetyExplanation::FixedPointType::RIGHT) {
        storeLevelTransition(transitionHierarchy.size(), invariant);
    }
}

} // namespace golem
