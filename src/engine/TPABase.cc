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
#include "utils/InductiveInterpolants.h"
#include "utils/SmtSolver.h"
#include <memory>

namespace golem {

int TPA_INDENT = -1;

SolverWrapperSingleUse::SolverWrapperSingleUse(Logic & logic, PTRef transition)
    : logic(logic), solver(logic, SMTSolver::WitnessProduction::MODEL_AND_INTERPOLANTS) {
    this->transition = transition;
    solver.getConfig().setSimplifyInterpolant(4);
    solver.getConfig().setLRAInterpolationAlgorithm(itp_lra_alg_decomposing_strong);
}

ReachabilityResult SolverWrapperSingleUse::checkConsistent(PTRef query) {
    solver.resetSolver();
    solver.assertProp(transition);
    solver.assertProp(query);
    lastResult = solver.check();
    if (lastResult == SMTSolver::Answer::UNSAT) {
        return ReachabilityResult::UNREACHABLE;
    } else if (lastResult == SMTSolver::Answer::SAT) {
        return ReachabilityResult::REACHABLE;
    } else {
        throw std::logic_error("Unexpected solver result in checking reachability!");
    }
}

void SolverWrapperSingleUse::strengthenTransition(PTRef nTransition) { transition = logic.mkAnd(transition, nTransition); }

std::unique_ptr<Model> SolverWrapperSingleUse::lastQueryModel() {
    if (lastResult != SMTSolver::Answer::SAT) {
        throw std::logic_error("Invalid call for obtaining a model from solver");
    }
    return solver.getModel();
}

PTRef SolverWrapperSingleUse::lastQueryTransitionInterpolant() {
    if (lastResult != SMTSolver::Answer::UNSAT) {
        throw std::logic_error("Invalid call for obtaining an interpolant from solver");
    }
    auto itpContext = solver.getInterpolationContext();
    vec<PTRef> itps;
    ipartitions_t mask = 1; // The transition was the first formula inserted
    itpContext->getSingleInterpolant(itps, mask);
    assert(itps.size() == 1);
    PTRef itp = itps[0];
    return itp;
}

SolverWrapperIncremental::SolverWrapperIncremental(Logic & logic, PTRef transition)
    : logic(logic), solver(logic, SMTSolver::WitnessProduction::MODEL_AND_INTERPOLANTS) {
    //        std::cout << "Transition: " << logic.printTerm(transition) << std::endl;
    this->transition = transition;
    solver.getConfig().setSimplifyInterpolant(4);
    solver.getConfig().setLRAInterpolationAlgorithm(itp_lra_alg_decomposing_strong);
    solver.assertProp(transition);
    opensmt::setbit(mask, allformulasInserted++);
}

ReachabilityResult SolverWrapperIncremental::checkConsistent(PTRef query) {
    //        std::cout << "Query: " << logic.printTerm(query) << std::endl;
    if (pushed) {
        solver.pop();
        pushed = false;
    }
    solver.push();
    pushed = true;
    solver.assertProp(query);
    ++allformulasInserted;
    lastResult = solver.check();
    if (lastResult == SMTSolver::Answer::UNSAT) {
        return ReachabilityResult::UNREACHABLE;
    } else if (lastResult == SMTSolver::Answer::SAT) {
        return ReachabilityResult::REACHABLE;
    } else {
        throw std::logic_error("Unexpected solver result in checking reachability!");
    }
}

void SolverWrapperIncremental::strengthenTransition(PTRef nTransition) {
    if (pushed) {
        solver.pop();
        pushed = false;
    }
    solver.push();
    solver.assertProp(nTransition);
    opensmt::setbit(mask, allformulasInserted++);
    //        std::cout << "Current number of formulas inserted: " << allformulasInserted << std::endl;
}

std::unique_ptr<Model> SolverWrapperIncremental::lastQueryModel() {
    if (lastResult != SMTSolver::Answer::SAT or not pushed) {
        throw std::logic_error("Invalid call for obtaining a model from solver");
    }
    auto model = solver.getModel();
    solver.pop();
    pushed = false;
    return model;
}

PTRef SolverWrapperIncremental::lastQueryTransitionInterpolant() {
    if (lastResult != SMTSolver::Answer::UNSAT or not pushed) {
        throw std::logic_error("Invalid call for obtaining an interpolant from solver");
    }
    auto itpContext = solver.getInterpolationContext();
    vec<PTRef> itps;
    //        std::cout << "Current mask: "  << mask << std::endl;
    itpContext->getSingleInterpolant(itps, mask);
    assert(itps.size() == 1);
    PTRef itp = itps[0];
    solver.pop();
    pushed = false;
    //        std::cout << logic.printTerm(itp) << std::endl;
    return itp;
}

void SolverWrapperIncrementalWithRestarts::rebuildSolver() {
    solver.resetSolver();
    PTRef consolidatedTransition = logic.mkAnd(transitionComponents);
    solver.assertProp(consolidatedTransition);
    levels = 0;
    allformulasInserted = 0;
    mask = 0;
    opensmt::setbit(mask, allformulasInserted++);
    transitionComponents.clear();
    transitionComponents.push(consolidatedTransition);
}

SolverWrapperIncrementalWithRestarts::SolverWrapperIncrementalWithRestarts(Logic & logic, PTRef transition)
    : SolverWrapperIncremental(logic, transition) {
    transitionComponents.push(transition);
}

ReachabilityResult SolverWrapperIncrementalWithRestarts::checkConsistent(PTRef query) {
    ++levels;
    if (levels > limit) {
        //            std::cout << "Rebuilding solver after " << levels << " pushes" << std::endl;
        rebuildSolver();
    }
    return SolverWrapperIncremental::checkConsistent(query);
}

void SolverWrapperIncrementalWithRestarts::strengthenTransition(PTRef nTransition) {
    SolverWrapperIncremental::strengthenTransition(nTransition);
    transitionComponents.push(nTransition);
    ++levels;
}

PTRef TPABase::getInit() const {
    return init;
}

PTRef TPABase::getTransitionRelation() const {
    return transition;
}

PTRef TPABase::getQuery() const {
    return query;
}

vec<PTRef> TPABase::getStateVars(int version) const {
    vec<PTRef> versioned;
    TimeMachine timeMachine(logic);
    for (PTRef var : stateVariables) {
        versioned.push(timeMachine.sendVarThroughTime(var, version));
    }
    return versioned;
}

PTRef TPABase::getNextVersion(PTRef currentVersion, int shift) const {
    auto it = versioningCache.find({currentVersion, shift});
    if (it != versioningCache.end()) { return it->second; }
    PTRef res = TimeMachine(logic).sendFlaThroughTime(currentVersion, shift);
    versioningCache.insert({{currentVersion, shift}, res});
    return res;
}

bool TPABase::isPureStateFormula(PTRef fla) const {
    auto vars = TermUtils(logic).getVars(fla);
    auto stateVars = getStateVars(0);
    return std::all_of(vars.begin(), vars.end(), [&](PTRef var) {
        return std::find(stateVars.begin(), stateVars.end(), var) != stateVars.end();
    });
}

bool TPABase::isPureTransitionFormula(PTRef fla) const {
    auto vars = TermUtils(logic).getVars(fla);
    auto stateVars = getStateVars(0);
    auto nextStateVars = getStateVars(1);
    return std::all_of(vars.begin(), vars.end(), [&](PTRef var) {
        return std::find(stateVars.begin(), stateVars.end(), var) != stateVars.end() or
               std::find(nextStateVars.begin(), nextStateVars.end(), var) != nextStateVars.end();
    });
}

PTRef TPABase::eliminateVars(PTRef fla, const vec<PTRef> & vars, Model & model) {
    if (useQE) {
        return QuantifierElimination(logic).eliminate(fla, vars);
    } else {
        return ModelBasedProjection(logic).project(fla, vars, model);
    }
}

PTRef TPABase::keepOnlyVars(PTRef fla, const vec<PTRef> & vars, Model & model) {
    if (useQE) {
        return QuantifierElimination(logic).keepOnly(fla, vars);
    } else {
        return ModelBasedProjection(logic).keepOnly(fla, vars, model);
    }
}

void TPABase::resetExplanation() {
    explanation.invariantType = SafetyExplanation::TransitionInvariantType::NONE;
    explanation.inductivnessPowerExponent = 0;
    explanation.safeTransitionInvariant = PTRef_Undef;
}

void TPABase::resetInitialStates(PTRef fla) {
    assert(isPureStateFormula(fla));
    this->init = fla;
    queryCache.clear();
    resetExplanation();
}

void TPABase::resetQueryStates(PTRef fla) {
    assert(isPureStateFormula(fla));
    this->query = fla;
    queryCache.clear();
    resetExplanation();
}

VerificationAnswer TPABase::solveTransitionSystem(TransitionSystem & system) {
    resetTransitionSystem(system);
    return solve();
}

VerificationAnswer TPABase::solve() {
    auto res = checkTrivialUnreachability();
    assert(res != VerificationAnswer::UNSAFE);
    if (res == VerificationAnswer::SAFE) { return res; }
    unsigned short power = 0;
    while (true) {
        auto res = checkPower(power);
        switch (res) {
            case VerificationAnswer::UNSAFE:
            case VerificationAnswer::SAFE:
                return res;
            case VerificationAnswer::UNKNOWN:
                ++power;
        }
    }
}

VerificationAnswer TPABase::checkTrivialUnreachability() {
    if (query == logic.getTerm_false()) {
        // TODO: Check UNSAT with solver?
        explanation.inductivnessPowerExponent = 0;
        explanation.safeTransitionInvariant = logic.getTerm_true();
        explanation.relationType = TPAType::LESS_THAN;
        explanation.invariantType = SafetyExplanation::TransitionInvariantType::RESTRICTED_TO_QUERY;
        explanation.fixedPointType = SafetyExplanation::FixedPointType::LEFT;
        return VerificationAnswer::SAFE;
    }
    if (init == logic.getTerm_false()) {
        // TODO: Check UNSAT with solver?
        explanation.inductivnessPowerExponent = 0;
        explanation.safeTransitionInvariant = logic.getTerm_true();
        explanation.relationType = TPAType::LESS_THAN;
        explanation.invariantType = SafetyExplanation::TransitionInvariantType::RESTRICTED_TO_INIT;
        explanation.fixedPointType = SafetyExplanation::FixedPointType::RIGHT;
        return VerificationAnswer::SAFE;
    }
    return VerificationAnswer::UNKNOWN;
}

PTRef TPABase::simplifyInterpolant(PTRef itp) {
    auto & laLogic = dynamic_cast<ArithLogic &>(logic);
    LATermUtils utils(laLogic);
    if (logic.isOr(itp)) {
        PTRef simplified = utils.simplifyDisjunction(itp);
        //        if (simplified != itp) {
        //            std::cout << "SImplified " << logic.pp(itp) << " to " << logic.pp(simplified) << std::endl;
        //        }
        return simplified;
    }
    return itp;
}

// TODO: unify cleanInterpolant and shiftOnlyNextVars. They are dual to each other and very similar
PTRef TPABase::cleanInterpolant(PTRef itp) const {
    TermUtils utils(logic);
    auto itpVars = utils.getVars(itp);
    auto currentVars = getStateVars(0);
    auto nextnextVars = getStateVars(2);
    assert(std::all_of(itpVars.begin(), itpVars.end(), [&](PTRef var) {
        return std::find(currentVars.begin(), currentVars.end(), var) != currentVars.end() or
               std::find(nextnextVars.begin(), nextnextVars.end(), var) != nextnextVars.end();
    }));
    auto nextVars = getStateVars(1);
    TermUtils::substitutions_map subst;
    assert(nextVars.size() == nextnextVars.size());
    for (int i = 0; i < nextVars.size(); ++i) {
        subst.insert({nextnextVars[i], nextVars[i]});
    }
    return utils.varSubstitute(itp, subst);
}

PTRef TPABase::shiftOnlyNextVars(PTRef fla) const {
    TermUtils utils(logic);
    auto vars = utils.getVars(fla);
    auto currentVars = getStateVars(0);
    auto nextVars = getStateVars(1);
    assert(std::all_of(vars.begin(), vars.end(), [&](PTRef var) {
        return std::find(currentVars.begin(), currentVars.end(), var) != currentVars.end() or
               std::find(nextVars.begin(), nextVars.end(), var) != nextVars.end();
    }));
    auto nextnextVars = getStateVars(2);
    TermUtils::substitutions_map subst;
    assert(nextVars.size() == nextnextVars.size());
    for (int i = 0; i < nextVars.size(); ++i) {
        subst.insert({nextVars[i], nextnextVars[i]});
    }
    return utils.varSubstitute(fla, subst);
}

PTRef TPABase::computeIdentity() const {
    TimeMachine timeMachine(logic);
    vec<PTRef> currentNextEqs;
    currentNextEqs.capacity(stateVariables.size());
    for (PTRef stateVar : stateVariables) {
        PTRef nextStateVar = timeMachine.sendVarThroughTime(stateVar, 1);
        currentNextEqs.push(logic.mkEq(stateVar, nextStateVar));
    }
    return logic.mkAnd(std::move(currentNextEqs));
}

void TPABase::resetTransitionSystem(TransitionSystem const & system) {
    TimeMachine timeMachine(logic);
    TermUtils utils(logic);
    this->stateVariables.clear();
    this->auxiliaryVariables.clear();
    auto stateVars = system.getStateVars();
    auto auxVars = system.getAuxiliaryVars();
    assert(std::all_of(stateVars.begin(), stateVars.end(), [&](PTRef var) {
        return timeMachine.isVersioned(var) and timeMachine.getVersionNumber(var) == 0;
    }));
    assert(std::all_of(auxVars.begin(), auxVars.end(), [&](PTRef var) {
        return timeMachine.isVersioned(var) and timeMachine.getVersionNumber(var) == 0;
    }));
    for (PTRef var : stateVars) {
        this->stateVariables.push(var);
    }
    for (PTRef var : auxVars) {
        //this->auxiliaryVariables.push(var);
        this->stateVariables.push(var);
    }
    this->init = system.getInit();
    this->init = utils.toNNF(this->init);
    if (not isPureStateFormula(init)) { throw std::logic_error("Initial states contain some non-state variable"); }
    this->query = system.getQuery();
    this->query = utils.toNNF(this->query);
    if (not isPureStateFormula(query)) { throw std::logic_error("Query states contain some non-state variable"); }
    this->transition = system.getTransition();
    this->transition = utils.toNNF(this->transition);
    //    std::cout << "Before simplifications: " << transition.x << std::endl;
    if (not logic.isAtom(this->transition)) {
        this->transition = ::rewriteMaxArityAggresive(logic, this->transition);
        //    std::cout << "After simplifications 1: " << transition.x << std::endl;
        this->transition = ::simplifyUnderAssignment_Aggressive(this->transition, logic);
        //    std::cout << "After simplifications 2: " << transition.x << std::endl;
    }
    this->identity = computeIdentity();
    resetPowers();
    //    std::cout << "Init: " << logic.printTerm(init) << std::endl;
    //    std::cout << "Transition: " << logic.printTerm(transition) << std::endl;
    //    std::cout << "Transition: "; TermUtils(logic).printTermWithLets(std::cout, transition); std::cout <<
    //    std::endl; std::cout << "Query: " << logic.printTerm(query) << std::endl;
}

PTRef TPABase::extractMidPoint(PTRef start, PTRef firstTransition, PTRef secondTransition, PTRef goal, Model & model) {
    assert(isPureStateFormula(start));
    assert(isPureTransitionFormula(firstTransition));
    assert(isPureStateFormula(getNextVersion(goal, -2)));
    assert(isPureTransitionFormula(getNextVersion(secondTransition, -1)));
    PTRef firstStep = logic.mkAnd(start, firstTransition);
    PTRef secondStep = logic.mkAnd(goal, secondTransition);
    assert(model.evaluate(firstStep) == logic.getTerm_true() and model.evaluate(secondStep) == logic.getTerm_true());
    vec<PTRef> toEliminate = getStateVars(0);
    PTRef midPointFromStart = eliminateVars(firstStep, toEliminate, model);
    toEliminate = getStateVars(2);
    PTRef midPointFromGoal = eliminateVars(secondStep, toEliminate, model);
    PTRef midPoint = getNextVersion(logic.mkAnd(midPointFromStart, midPointFromGoal), -1);
    assert(isPureStateFormula(midPoint));
    return midPoint;
}

PTRef TPABase::refineTwoStepTarget(PTRef start, PTRef twoSteptransition, PTRef goal, Model & model) {
    assert(isPureStateFormula(getNextVersion(goal, -2)));
    PTRef transitionQuery = logic.mkAnd({start, twoSteptransition, goal});
    assert(model.evaluate(transitionQuery) == logic.getTerm_true());
    auto nextnextStateVars = getStateVars(2);
    PTRef refinedGoal = keepOnlyVars(transitionQuery, nextnextStateVars, model);
    assert(refinedGoal != logic.getTerm_false());
    return getNextVersion(refinedGoal, -2);
}

void TPABase::squashInvariants(vec<PTRef> & candidates) {
    while (candidates.size() > 128) {
        int j = 0;
        for (int i = candidates.size() - 1; i >= 1 && i > j; i-- && j++) {
            PTRef n_f = logic.mkAnd(candidates[j], candidates[i]);
            candidates.pop();
            candidates[j] = n_f;
            if (candidates.size() <= 128) { break; }
        }
    }
}

void TPABase::houdiniCheck(PTRef invCandidates, PTRef transition, SafetyExplanation::FixedPointType alignment) {
    // RIGHT:
    //   rightInvariants /\ currentLevelTransition /\ getNextVersion(transition) =>
    //     shiftOnlyNextVars(currentLevelTransition);
    // LEFT:
    //   leftInvariants /\ transition /\ getNextVersion(currentLevelTransition) =>
    //     shiftOnlyNextVars(currentLevelTransition);
    SMTSolver solver(logic, SMTSolver::WitnessProduction::NONE);
    solver.push();
    auto candidates = topLevelConjuncts(logic, invCandidates);
    if (alignment == SafetyExplanation::FixedPointType::RIGHT) {
        //solver.assertProp(init);
        solver.assertProp(getNextVersion(transition));
        for (PTRef rt : rightInvariants) {
            solver.assertProp(rt);
            solver.assertProp(getNextVersion(rt));
            solver.assertProp(shiftOnlyNextVars(rt));
        }
    } else if (alignment == SafetyExplanation::FixedPointType::LEFT) {
        solver.assertProp(getNextVersion(query, 2));
        solver.assertProp(transition);
        for (PTRef lt : leftInvariants) {
            solver.assertProp(lt);
            solver.assertProp(getNextVersion(lt));
            solver.assertProp(shiftOnlyNextVars(lt));
        }
    }

    solver.push();
    squashInvariants(candidates);
    //    invCandidates.append(conjuncts);
    //    Atr(x, x') /\ tr(x', x'') => Atr(x, x'')
    //    or
    //    Atr(x', x'') /\  tr(x, x') => Atr(x, x'')
    //    Push transition once and for all
    //    While loop externally, because we may drop smth important
    PTRef goal = shiftOnlyNextVars(invCandidates);

    if (alignment == SafetyExplanation::FixedPointType::RIGHT) {
        solver.assertProp(logic.mkAnd(invCandidates, logic.mkNot(goal)));
    } else if (alignment == SafetyExplanation::FixedPointType::LEFT) {
        solver.assertProp(logic.mkAnd(getNextVersion(invCandidates), logic.mkNot(goal)));
    }
    // ANNA: this can be done in fewer iterations asking for a cti of (candidates & !candidates') and removing
    // all candidate lemmas thare are violated by the same model.
    while (solver.check() == SMTSolver::Answer::SAT) {
        for (int i = candidates.size() - 1; i >= 0; i--) {
            PTRef cand = candidates[i];
            solver.pop();
            solver.push();
            if (alignment == SafetyExplanation::FixedPointType::RIGHT) {
                solver.assertProp(logic.mkAnd(logic.mkAnd(candidates), logic.mkNot(shiftOnlyNextVars(cand))));
            } else {
                if (alignment == SafetyExplanation::FixedPointType::LEFT) {
                    solver.assertProp(
                        logic.mkAnd(getNextVersion(logic.mkAnd(candidates)), logic.mkNot(shiftOnlyNextVars(cand))));
                }
            }
            if (solver.check() == SMTSolver::Answer::SAT) {
                candidates[i] = candidates[candidates.size() - 1];
                candidates.pop();
            }
        }
        solver.pop();
        solver.push();
        goal = shiftOnlyNextVars(logic.mkAnd(candidates));
        if (alignment == SafetyExplanation::FixedPointType::RIGHT) {
            solver.assertProp(logic.mkAnd(logic.mkAnd(candidates), logic.mkNot(goal)));
        } else {
            solver.assertProp(logic.mkAnd(getNextVersion(logic.mkAnd(candidates)), logic.mkNot(goal)));
        }
    }
    // Anna: why not assume existing right/left invariants in the prev check?
    for (auto cand : candidates) {
        learnInvariant(cand, alignment);
    }
}

bool TPABase::checkLessThanFixedPoint(unsigned short power) {
    assert(verifyPower(power, TPAType::LESS_THAN));
    for (unsigned short i = 1; i <= power; ++i) {
        PTRef currentLevelTransition = getPower(i, TPAType::LESS_THAN);
        // first check if it is a fixed point with respect to the initial states
        SMTSolver solver(logic, SMTSolver::WitnessProduction::NONE);
        {
            // ANNA: asserting rightInvariants looks like restricting the assumption to the Finfinity frame.
            houdiniCheck(currentLevelTransition, transition, SafetyExplanation::FixedPointType::RIGHT);
            solver.assertProp(
                logic.mkAnd({logic.mkAnd(rightInvariants), currentLevelTransition, getNextVersion(transition),
                             logic.mkNot(shiftOnlyNextVars(currentLevelTransition))}));
            auto satres = solver.check();
            bool restrictedInvariant = false;
            if (satres != SMTSolver::Answer::UNSAT) {
                solver.push();
                solver.assertProp(init);
                satres = solver.check();
                if (satres == SMTSolver::Answer::UNSAT) { restrictedInvariant = true; }
            }
            if (satres == SMTSolver::Answer::UNSAT) {
                if (verbose() > 0) {
                    std::cout << "; Right fixed point detected in less-than relation on level " << i << " from "
                              << power << std::endl;
                    std::cout << "; Fixed point detected for "
                              << (not restrictedInvariant ? "whole transition relation"
                                                          : "transition relation restricted to init")
                              << std::endl;
                }
                TRACE(2, "[FP] Right fixpoint detected at level " << i << ". Restricted? " << restrictedInvariant);
                vec<PTRef> conjs = TermUtils(logic).getTopLevelConjuncts(currentLevelTransition);
                TRACE(2, "[FP] Fixpoint: " << std::endl; for (auto c : conjs) std::cout << c.x << std::endl; std::cout)
                explanation.invariantType = restrictedInvariant
                                                ? SafetyExplanation::TransitionInvariantType::RESTRICTED_TO_INIT
                                                : SafetyExplanation::TransitionInvariantType::UNRESTRICTED;
                explanation.relationType = TPAType::LESS_THAN;
                explanation.fixedPointType = SafetyExplanation::FixedPointType::RIGHT;
                explanation.inductivnessPowerExponent = 0;
                explanation.safeTransitionInvariant = logic.mkAnd(logic.mkAnd(rightInvariants), currentLevelTransition);
                return true;
            }
        }
        // now check if it is fixed point with respect to bad states
        {
            solver.resetSolver();
            houdiniCheck(currentLevelTransition, transition, SafetyExplanation::FixedPointType::LEFT);
            solver.assertProp(logic.mkAnd({transition, getNextVersion(logic.mkAnd(leftInvariants)),
                                           getNextVersion(currentLevelTransition),
                                           logic.mkNot(shiftOnlyNextVars(currentLevelTransition))}));
            auto satres = solver.check();
            bool restrictedInvariant = false;
            if (satres != SMTSolver::Answer::UNSAT) {
                solver.push();
                solver.assertProp(getNextVersion(query, 2));
                satres = solver.check();
                if (satres == SMTSolver::Answer::UNSAT) { restrictedInvariant = true; }
            }
            if (satres == SMTSolver::Answer::UNSAT) {
                if (verbose() > 0) {
                    std::cout << "; Left fixed point detected in less-than relation on level " << i << " from " << power
                              << std::endl;
                    std::cout << "; Fixed point detected for "
                              << (not restrictedInvariant ? "whole transition relation"
                                                          : "transition relation restricted to bad")
                              << std::endl;
                }
                TRACE(2, "[FP] Left fixpoint detected at level " << i << ". Restricted? " << restrictedInvariant)
                vec<PTRef> conjs = TermUtils(logic).getTopLevelConjuncts(currentLevelTransition);
                TRACE(2, "[FP] Fixpoint: " << std::endl; for (auto c : conjs) std::cout << c.x << std::endl; std::cout);

                explanation.invariantType = restrictedInvariant
                                                ? SafetyExplanation::TransitionInvariantType::RESTRICTED_TO_QUERY
                                                : SafetyExplanation::TransitionInvariantType::UNRESTRICTED;
                explanation.relationType = TPAType::LESS_THAN;
                explanation.fixedPointType = SafetyExplanation::FixedPointType::LEFT;
                explanation.inductivnessPowerExponent = 0;
                explanation.safeTransitionInvariant = logic.mkAnd(logic.mkAnd(leftInvariants), currentLevelTransition);
                return true;
            }
        }
        // TODO: Move this to a separate method?
        // now check the produced if transition invariants are actually safety invariants
        // ANNA: this can be done right after Houdini check.
        {
            solver.resetSolver();
            solver.assertProp(logic.mkAnd({init, logic.mkAnd(rightInvariants), getNextVersion(query)}));
            auto satres = solver.check();
            if (satres == SMTSolver::Answer::UNSAT) {
                explanation.invariantType = SafetyExplanation::TransitionInvariantType::UNRESTRICTED;
                explanation.relationType = TPAType::LESS_THAN;
                explanation.fixedPointType = SafetyExplanation::FixedPointType::RIGHT;
                explanation.inductivnessPowerExponent = 0;
                explanation.safeTransitionInvariant = logic.mkAnd(rightInvariants);

                solver.resetSolver();
                solver.assertProp(init);
                solver.assertProp(logic.mkAnd(rightInvariants));
                solver.assertProp(getNextVersion(transition));
                solver.assertProp(logic.mkNot(shiftOnlyNextVars(logic.mkAnd(rightInvariants))));
                assert(solver.check() == SMTSolver::Answer::UNSAT);

                TRACE(2, "[FP] Right Invariant is safety invariant: " << std::endl;
                      for (auto c : rightInvariants) std::cout << c.x << std::endl; std::cout)
                return true;
            }
        }
        // now check the produced if transition invariants are actually safety invariants
        {
            solver.resetSolver();
            solver.assertProp(logic.mkAnd({init, logic.mkAnd(leftInvariants), getNextVersion(query)}));
            auto satres = solver.check();
            if (satres == SMTSolver::Answer::UNSAT) {
                explanation.invariantType = SafetyExplanation::TransitionInvariantType::UNRESTRICTED;
                explanation.relationType = TPAType::LESS_THAN;
                explanation.fixedPointType = SafetyExplanation::FixedPointType::LEFT;
                explanation.inductivnessPowerExponent = 0;
                explanation.safeTransitionInvariant = logic.mkAnd(leftInvariants);


                solver.resetSolver();
                solver.assertProp(getNextVersion(getNextVersion(query)));
                solver.assertProp(transition);
                solver.assertProp(getNextVersion(logic.mkAnd(leftInvariants)));
                solver.assertProp(logic.mkNot(shiftOnlyNextVars(logic.mkAnd(leftInvariants))));
                assert(solver.check() == SMTSolver::Answer::UNSAT);

                TRACE(2, "[FP] Left Invariant is safety invariant: " << std::endl;
                      for (auto c : leftInvariants) std::cout << c.x << std::endl; std::cout)
                return true;
            }
        }
    }
    return false;
}

void TPABase::learnInvariant(PTRef invariant, SafetyExplanation::FixedPointType alignment) {
    bool right = (alignment == SafetyExplanation::FixedPointType::RIGHT);
    auto& dst = right ? rightInvariants : leftInvariants;
    if (std::find(dst.begin(), dst.end(), invariant) == dst.end()) {
        dst.push(invariant);
    }
    TRACE(2, "[inf] New lemma in " << ((right) ? "Right" : "Left") << " infinity frame " << invariant.x);
}

bool TPABase::verifyKinductiveInvariant(PTRef fla, unsigned long k) const {
    constexpr int trace_level = 1;
    TRACE(trace_level, "Verifying k-inductive invariant for k = " << k)

    { // Inductive case:

        SMTSolver solver(logic, SMTSolver::WitnessProduction::NONE);
        for (unsigned long i = 0; i < k; ++i) {
            solver.assertProp(getNextVersion(fla, i));
            solver.assertProp(getNextVersion(transition, i));
        }
        solver.assertProp(logic.mkNot(getNextVersion(fla, k)));
        auto res = solver.check();
        if (res != SMTSolver::Answer::UNSAT) {
            std::cerr << "k-induction verification failed; induction step does not hold!" << std::endl;
            return false;
        }
        TRACE(trace_level, "Inductive case succesfully verified")
    }
    { // Base cases:
        SMTSolver solver(logic, SMTSolver::WitnessProduction::NONE);
        solver.assertProp(init);
        for (unsigned long i = 0; i < k; ++i) {
            solver.push();
            solver.assertProp(logic.mkNot(getNextVersion(fla, i)));
            auto res = solver.check();
            if (res != SMTSolver::Answer::UNSAT) {
                std::cerr << "k-induction verification failed; base case " << i << " does not hold!" << std::endl;
                return false;
            }
            TRACE(trace_level, "Base case " << i << " succesfully verified")
            solver.pop();
            solver.push();
            solver.assertProp(getNextVersion(transition, i));
        }
    }
    return true;
}

PTRef TPABase::safeSupersetOfInitialStates(PTRef start, PTRef transitionInvariant, PTRef target) const {
    SMTSolver solver(logic, SMTSolver::WitnessProduction::ONLY_INTERPOLANTS);
    solver.getConfig().setLRAInterpolationAlgorithm(itp_lra_alg_decomposing_strong);
    solver.getConfig().setSimplifyInterpolant(4);
    solver.assertProp(start);
    solver.assertProp(transitionInvariant);
    solver.assertProp(target);
    auto res = solver.check();
    if (res != SMTSolver::Answer::UNSAT) { throw std::logic_error("SMT query was suppose to be unsat, but is not!"); }
    auto itpContext = solver.getInterpolationContext();
    ipartitions_t mask = (1 << 1) + (1 << 2); // This puts transition + query into the A-part
    vec<PTRef> itps;
    itpContext->getSingleInterpolant(itps, mask);
    return logic.mkNot(itps[0]);
}

PTRef TPABase::getReachedStates() const {
    return reachedStates.reachedStates;
}

unsigned TPABase::getTransitionStepCount() const {
    return reachedStates.steps;
}

/*
 * Returns superset of init that are still safe
 */
PTRef TPABase::getSafetyExplanation() const {
    if (explanation.invariantType == SafetyExplanation::TransitionInvariantType::RESTRICTED_TO_INIT) {
        // TODO: compute the safe inductive invariant and return negation of that?
        return init;
    }
    PTRef transitionInvariant = explanation.safeTransitionInvariant;
    // TODO: Currently transition invariants from TPA:Type::EQUALS are over three copies of the variables.
    //       Maybe we should use auxiliary (existentially quantified) variables for the intermediate state?
    //       And rename the variables so the final state is version 1, same as for TPAType::LESS_THAN?
    return safeSupersetOfInitialStates(
        getInit(), transitionInvariant,
        getNextVersion(getQuery(), explanation.relationType == TPAType::LESS_THAN ? 1 : 2));
}

PTRef TPABase::getInductiveInvariant() const {
    assert(explanation.invariantType != SafetyExplanation::TransitionInvariantType::NONE);
    if (explanation.relationType == TPAType::LESS_THAN) {
        PTRef transitionInvariant = explanation.safeTransitionInvariant;
        switch (explanation.fixedPointType) {
            //  TODO: Think about properties combination, can we use left and right invariants together?
            case SafetyExplanation::FixedPointType::LEFT:
                return logic.mkNot(QuantifierElimination(logic).keepOnly(
                    logic.mkAnd(transitionInvariant, getNextVersion(query)), getStateVars(0)));
            case SafetyExplanation::FixedPointType::RIGHT:
                return getNextVersion(
                    QuantifierElimination(logic).keepOnly(logic.mkAnd(init, transitionInvariant), getStateVars(1)), -1);
        }
    } else if (explanation.relationType == TPAType::EQUALS) {
        if (explanation.invariantType == SafetyExplanation::TransitionInvariantType::RESTRICTED_TO_QUERY) {
            return PTRef_Undef;
        }
        if (explanation.inductivnessPowerExponent > 10) {
            std::cerr << "; k-inductive invariant computed, but k is too large to compute 1-inductive invariant"
                      << std::endl;
            return PTRef_Undef;
        }
        return static_cast<TPASplit const *>(this)->inductiveInvariantFromEqualsTransitionInvariant();
    }
    throw std::logic_error("Unreachable!");
}

} // namespace golem
