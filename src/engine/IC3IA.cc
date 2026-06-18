/*
 * Copyright (c) 2025
 *
 * SPDX-License-Identifier: MIT
 */

#include "IC3IA.h"

#include "Common.h"
#include "TermUtils.h"
#include "TransformationUtils.h"

#include <algorithm>
#include <cassert>
#include <chrono>
#include <iostream>
#include <random>
#include <sstream>
#include <stdexcept>
#include <unordered_set>

namespace golem {

//=============================================================================
// Constructor
//=============================================================================

IC3IA::IC3IA(Logic & logic, Options const & options) : logic_(logic) {
    verbosity_ = std::stoi(options.getOrDefault(Options::VERBOSE, "0"));
    computeWitness = options.getOrDefault(Options::COMPUTE_WITNESS, "") == "true";
    useUnsatCoreGeneralization_ =
    options.getOrDefault(Options::IC3IA_USE_UNSAT_CORE_GENERALIZATION, "true") == "true";
    addInitialReset_ =
        options.getOrDefault(Options::IC3IA_ADD_INITIAL_RESET, "true") == "true";
}

//=============================================================================
// IC3 core — main loop
//=============================================================================

TransitionSystemVerificationResult IC3IA::runIC3(bool resuming) {
    if (verbosity_ > 0) { std::cout << "[IC3] " << (resuming ? "Resuming" : "Starting") << "\n"; }

    if (!resuming) {
        // Base check: Init ∧ bad SAT → immediately unsafe.
        {
            solver_->push();
            solver_->assertProp(initAct_);
            solver_->assertProp(logic_.mkNot(transAct_));
            solver_->assertProp(bad_);
            auto const res = solver_->check();
            solver_->pop();
            if (res == SMTSolver::Answer::SAT) {
                if (verbosity_ > 0) { std::cout << "[IC3] Initial states satisfy bad\n"; }
                return {VerificationAnswer::UNSAFE, 0u};
            }
        }

        pushFrame(); // depth_ = 1
    }

    while (true) {
        if (verbosity_ > 0) { std::cout << "[IC3] Depth = " << depth_ << "\n"; }

        Cube badCube;
        while (hasBadState(badCube)) {
            if (!blockObligations(Obligation{badCube, depth_, nullptr})) {
                if (verbosity_ > 0) { std::cout << "[IC3] Counterexample found\n"; }
                return {VerificationAnswer::UNSAFE, depth_};
            }
            badCube.clear();
        }

        pushFrame();

        if (propagateClauses()) {
            for (unsigned i = 1; i < depth_; ++i) {
                bool hasAtI = false;
                for (auto const & c : clauses_) {
                    if (c.level == i) { hasAtI = true; break; }
                }
                if (!hasAtI) {
                    if (verbosity_ > 0) {
                        std::cout << "[IC3] Fixpoint at level " << i << "\n";
                    }
                    return {VerificationAnswer::SAFE, buildInvariant(i)};
                }
            }
            throw std::logic_error("IC3IA: propagateClauses reported fixpoint but no empty level was found");
        }
    }
}

//=============================================================================
// IC3 core — frame management
//=============================================================================

PTRef IC3IA::getF(unsigned k) const {
    if (k == 0) { return init_; }
    vec<PTRef> parts;
    for (auto const & c : clauses_) {
        if (c.level >= k) { parts.push(c.fla); }
    }
    if (parts.size() == 0) { return logic_.getTerm_true(); }
    return logic_.mkAnd(parts);
}

void IC3IA::addClause(PTRef clauseFla, unsigned level) {
    for (auto & c : clauses_) {
        if (c.fla == clauseFla) {
            if (c.level < level) { c.level = level; }
            return;
        }
    }
    clauses_.push_back({clauseFla, level});
}

//=============================================================================
// IC3 core — formula helpers
//=============================================================================

PTRef IC3IA::cubeToFla(Cube const & cube) const {
    if (cube.empty()) { return logic_.getTerm_true(); }
    vec<PTRef> lits;
    for (PTRef lit : cube) { lits.push(lit); }
    return logic_.mkAnd(lits);
}

PTRef IC3IA::prime(PTRef fla) const {
    return shiftFormulaThroughTime(fla, 1);
}

//=============================================================================
// IC3 core — model extraction
//=============================================================================

IC3IA::Cube IC3IA::modelToCube(std::shared_ptr<Model> const & model,
                                std::vector<PTRef> const & vars) const {
    Cube cube;
    cube.reserve(vars.size());
    for (PTRef var : vars) {
        PTRef val = model->evaluate(var);
        cube.push_back(val == logic_.getTerm_true() ? var : logic_.mkNot(var));
    }
    return cube;
}

//=============================================================================
// IC3 core — queries
//=============================================================================

bool IC3IA::initIntersects(Cube const & cube) const {
    solver_->push();
    solver_->assertProp(initAct_);
    solver_->assertProp(logic_.mkNot(transAct_));
    solver_->assertProp(cubeToFla(cube));
    auto const res = solver_->check();
    solver_->pop();
    return res == SMTSolver::Answer::SAT;
}

bool IC3IA::hasBadState(Cube & outCube) const {
    // Disable the trans relation via transAct_ so the query is over a single
    // current state (label-defs still apply, giving labels their meaning).
    solver_->push();
    solver_->assertProp(logic_.mkNot(transAct_));
    solver_->assertProp(getF(depth_));
    solver_->assertProp(bad_);
    auto const res = solver_->check();
    bool const sat = res == SMTSolver::Answer::SAT;
    if (sat) { outCube = modelToCube(solver_->getModel(), stateVars_); }
    solver_->pop();
    return sat;
}

bool IC3IA::hasPredecessorUnder(PTRef frameFormula, Cube const & cube,
                                 Cube & outCTI) const {
    solver_->push();
    solver_->assertProp(transAct_);
    solver_->assertProp(frameFormula);
    solver_->assertProp(prime(cubeToFla(cube)));
    auto const res = solver_->check();
    bool const sat = res == SMTSolver::Answer::SAT;
    if (sat) { outCTI = modelToCube(solver_->getModel(), stateVars_); }
    solver_->pop();
    return sat;
}

bool IC3IA::hasPredecessor(Cube const & cube, unsigned level, Cube & outCTI) const {
    assert(level > 0);
    return hasPredecessorUnder(getF(level - 1), cube, outCTI);
}

//=============================================================================
// IC3 core — generalization
//=============================================================================

IC3IA::Cube IC3IA::generalize(Cube cube, unsigned level) const {
    if (useUnsatCoreGeneralization_) { return generalizeWithUnsatCore(std::move(cube), level); }

    assert(level > 0);
    PTRef frameFormula = getF(level - 1);
    Cube dummy;
    for (std::size_t i = 0; i < cube.size(); ) {
        if (cube.size() == 1) { break; }
        Cube attempt;
        attempt.reserve(cube.size() - 1);
        for (std::size_t j = 0; j < cube.size(); ++j) {
            if (j != i) { attempt.push_back(cube[j]); }
        }
        if (!initIntersects(attempt) &&
            !hasPredecessorUnder(frameFormula, attempt, dummy)) {
            cube = std::move(attempt);
        } else {
            ++i;
        }
    }
    return cube;
}

IC3IA::Cube IC3IA::generalizeWithUnsatCore(Cube cube, unsigned level) const {
    assert(level > 0);
    if (cube.size() <= 1) { return cube; }

    PTRef frameFormula = getF(level - 1);

    auto extractCoreLiterals = [&](std::vector<PTRef> const & literals,
                                   vec<PTRef> const & background) -> std::vector<PTRef> {
        SMTSolver solver(logic_, SMTSolver::WitnessProduction::ONLY_UNSAT_CORE);
        for (PTRef part : background) { solver.assertProp(part); }
        for (PTRef lit : literals) { solver.assertProp(lit); }

        if (solver.check() != SMTSolver::Answer::UNSAT) { return {}; }

        auto core = solver.getCoreSolver().getUnsatCore();
        std::vector<PTRef> coreTerms;
        coreTerms.reserve(core->getTerms().size());
        for (PTRef t : core->getTerms()) { coreTerms.push_back(t); }
        return coreTerms;
    };

    vec<PTRef> initBackground;
    initBackground.push(init_);
    auto initCore = extractCoreLiterals(cube, initBackground);

    std::vector<PTRef> primedCube;
    primedCube.reserve(cube.size());
    for (PTRef lit : cube) { primedCube.push_back(prime(lit)); }

    vec<PTRef> predBackground;
    predBackground.push(frameFormula);
    predBackground.push(trans_);
    auto predCore = extractCoreLiterals(primedCube, predBackground);

    Cube reduced;
    reduced.reserve(cube.size());
    for (std::size_t i = 0; i < cube.size(); ++i) {
        if (std::find(initCore.begin(), initCore.end(), cube[i]) != initCore.end() ||
            std::find(predCore.begin(), predCore.end(), primedCube[i]) != predCore.end()) {
            reduced.push_back(cube[i]);
        }
    }

    Cube dummy;
    if (!initIntersects(reduced) && !hasPredecessorUnder(frameFormula, reduced, dummy)) {
        return reduced;
    }
    return cube;
}

//=============================================================================
// IC3 core — blocking loop
//=============================================================================

bool IC3IA::blockObligations(Obligation seed) {
    using PQ = std::priority_queue<Obligation,
                                   std::vector<Obligation>,
                                   std::greater<Obligation>>;
    PQ pq;
    pq.push(std::move(seed));

    while (!pq.empty()) {
        Obligation obl = pq.top();
        pq.pop();

        // Sanity check: skip obligations whose cube is no longer reachable
        // in F[level] (e.g., already blocked by a pushed clause).
        {
            solver_->push();
            solver_->assertProp(logic_.mkNot(transAct_));
            solver_->assertProp(getF(obl.level));
            solver_->assertProp(cubeToFla(obl.cube));
            auto const res = solver_->check();
            solver_->pop();
            if (res == SMTSolver::Answer::UNSAT) { continue; }
        }

        if (obl.level == 0) {
            // reaching level 0 means we have a counterexample.
            cexTrace_.clear();
            Obligation const * cur = &obl;
            while (cur) {
                cexTrace_.push_back(cur->cube);
                cur = cur->successor.get();
            }
            return false;
        }

        Cube cti;
        if (hasPredecessor(obl.cube, obl.level, cti)) {
            auto oblPtr = std::make_shared<Obligation>(obl);
            pq.push(Obligation{std::move(cti), obl.level - 1, std::move(oblPtr)});
            pq.push(std::move(obl));
        } else {
            Cube gen = generalize(obl.cube, obl.level);
            PTRef clause = logic_.mkNot(cubeToFla(gen));
            addClause(clause, obl.level);
            if (verbosity_ > 1) {
                std::cout << "[IC3] Blocked at level " << obl.level
                          << ", clause literals = " << gen.size() << "\n";
            }
        }
    }
    return true;
}

//=============================================================================
// IC3 core — clause propagation
//=============================================================================

bool IC3IA::propagateClauses() {
    for (unsigned i = 1; i < depth_; ++i) {
        for (auto & c : clauses_) {
            if (c.level != i) { continue; }
            PTRef negClausePrimed = prime(logic_.mkNot(c.fla));
            solver_->push();
            solver_->assertProp(transAct_);
            solver_->assertProp(getF(i));
            solver_->assertProp(negClausePrimed);
            auto const res = solver_->check();
            solver_->pop();
            if (res == SMTSolver::Answer::UNSAT) {
                c.level = i + 1;
            }
        }
        bool hasAtI = false;
        for (auto const & c : clauses_) {
            if (c.level == i) { hasAtI = true; break; }
        }
        if (!hasAtI) { return true; }
    }
    return false;
}

//=============================================================================
// IC3 core — invariant construction
//=============================================================================

PTRef IC3IA::buildInvariant(unsigned fixpointLevel) const {
    return getF(fixpointLevel);
}

//=============================================================================
// IC3IA top-level solve
//=============================================================================

TransitionSystemVerificationResult IC3IA::solve(TransitionSystem const & system) {
    concreteInit_         = system.getInit();
    concreteTrans_        = system.getTransition();
    concreteBad_          = system.getQuery();
    concreteStateVars_    = system.getStateVars();
    concreteNextStateVars_= system.getNextStateVars();

    if (addInitialReset_) {
        applyInitialReset();
    }

    predicates_.clear();
    predLabels_.clear();
    predLabelsNext_.clear();

    initializePredicates();

    if (verbosity_ > 0) {
        std::cout << "[IC3IA] Initial predicates: " << predicates_.size() << "\n";
    }

    initializeAbstractSystem();

    for (unsigned iter = 0; ; ++iter) {
        // Resume after the first iteration: keep frames, depth, and learned
        // clauses across CEGAR refinements. 
        auto result = runIC3(/*resuming=*/iter > 0);

        if (result.answer == VerificationAnswer::SAFE) {
            PTRef abstractInv = std::get<PTRef>(result.witness);
            PTRef concreteInv = concreteInvariant(abstractInv);
            if (addInitialReset_) {
                // Substitute reset → false to eliminate the internal reset variable.
                // In all reachable states of the original system, reset is always false.
                TimeMachine tm{logic_};
                PTRef resetVar = tm.getVarVersionZero("ic3ia_reset", logic_.getSort_bool());
                TermUtils::substitutions_map subst;
                subst[resetVar] = logic_.getTerm_false();
                concreteInv = TermUtils(logic_).varSubstitute(concreteInv, subst);
            }
            return {VerificationAnswer::SAFE, concreteInv};
        }

        if (result.answer == VerificationAnswer::UNSAFE) {
            std::size_t realDepth = 0;
            if (checkAndRefine(realDepth)) {
                // The reset transformation adds one extra step at the front; subtract it.
                if (addInitialReset_ && realDepth > 0) { --realDepth; }
                return {VerificationAnswer::UNSAFE, realDepth};
            }
            if (verbosity_ > 0) {
                std::cout << "[IC3IA] Spurious CEX at depth "
                          << std::get<std::size_t>(result.witness)
                          << "; predicates now: " << predicates_.size() << "\n";
            }
            extendAbstractSystem();
            cexTrace_.clear();
            continue;
        }

        return result;
    }
}

//=============================================================================
// IC3IA — predicate management
//=============================================================================

void IC3IA::collectVars(PTRef fla, std::vector<PTRef> & vars) const {
    if (logic_.isVar(fla)) {
        if (std::find(vars.begin(), vars.end(), fla) == vars.end()) {
            vars.push_back(fla);
        }
        return;
    }

    Pterm const & t = logic_.getPterm(fla);
    for (int i = 0; i < t.size(); ++i) {
        collectVars(t[i], vars);
    }
}

PTRef IC3IA::shiftFormulaThroughTime(PTRef fla, int steps) const {
    if (steps == 0) { return fla; }

    TimeMachine tm{logic_};
    std::vector<PTRef> stack;
    collectVars(fla, stack);

    TermUtils::substitutions_map substitutions;
    for (PTRef var : stack) {
        if (tm.isVersioned(var)) {
            substitutions[var] = tm.sendVarThroughTime(var, steps);
        }
    }

    if (substitutions.empty()) { return fla; }
    return TermUtils(logic_).varSubstitute(fla, substitutions);
}

void IC3IA::collectAtoms(PTRef fla, std::vector<PTRef> & atoms) const {
    if (logic_.isTrue(fla) || logic_.isFalse(fla)) { return; }

    if (logic_.isAtom(fla)) {
        if (std::find(atoms.begin(), atoms.end(), fla) == atoms.end()) {
            atoms.push_back(fla);
        }
        return;
    }

    // Boolean connective: descend into all children.
    Pterm const & t = logic_.getPterm(fla);
    for (int i = 0; i < t.size(); ++i) { collectAtoms(t[i], atoms); }
}

std::vector<PTRef> IC3IA::minimizeRefinementPredicateSet(std::vector<PTRef> candidates,
                                                         std::vector<PTRef> const & unshiftedInterpolants,
                                                         std::size_t depth) const {
    if (candidates.size() <= 1 || unshiftedInterpolants.empty()) { return candidates; }

    constexpr int maxIter = 5;
    constexpr int maxFail = 2;
    std::mt19937 rng(0xC0FFEEu);
    int failures = 0;

    for (int iter = 0; iter < maxIter; ++iter) {
        if (iter > 0) { std::shuffle(candidates.begin(), candidates.end(), rng); }

        SMTSolver solver(logic_, SMTSolver::WitnessProduction::ONLY_UNSAT_CORE);
        solver.assertProp(concreteInit_);
        for (std::size_t i = 0; i < depth; ++i) {
            solver.assertProp(atTime(concreteTrans_, static_cast<unsigned>(i)));
        }
        solver.assertProp(atTime(concreteBad_, static_cast<unsigned>(depth)));

        TermUtils::substitutions_map subst;
        std::vector<PTRef> activationLiterals;
        std::vector<PTRef> abstractionLabels;
        std::vector<PTRef> guardedDefinitions;
        activationLiterals.reserve(candidates.size());
        abstractionLabels.reserve(candidates.size());
        guardedDefinitions.reserve(candidates.size());

        for (std::size_t i = 0; i < candidates.size(); ++i) {
            std::string suffix = std::to_string(i);
            PTRef act = logic_.mkBoolVar((".ic3ia_refpred_act_" + suffix).c_str());
            PTRef lbl = logic_.mkBoolVar((".ic3ia_refpred_lbl_" + suffix).c_str());
            activationLiterals.push_back(act);
            abstractionLabels.push_back(lbl);
            subst[candidates[i]] = lbl;
            subst[logic_.mkNot(candidates[i])] = logic_.mkNot(lbl);
        }

        TermUtils termUtils(logic_);
        for (std::size_t i = 0; i < unshiftedInterpolants.size(); ++i) {
            PTRef abstractedInterpolant = termUtils.varSubstitute(unshiftedInterpolants[i], subst);
            solver.assertProp(atTime(abstractedInterpolant, static_cast<unsigned>(i + 1)));
        }

        for (std::size_t i = 0; i < candidates.size(); ++i) {
            vec<PTRef> eqs;
            for (std::size_t step = 0; step < unshiftedInterpolants.size(); ++step) {
                eqs.push(logic_.mkEq(atTime(abstractionLabels[i], static_cast<unsigned>(step + 1)),
                                     atTime(candidates[i], static_cast<unsigned>(step + 1))));
            }
            PTRef definition = eqs.size() == 1 ? eqs[0] : logic_.mkAnd(eqs);
            PTRef guarded = logic_.mkOr(logic_.mkNot(activationLiterals[i]), definition);
            guardedDefinitions.push_back(guarded);
            solver.assertProp(guarded);
            solver.assertProp(activationLiterals[i]);
        }

        if (solver.check() != SMTSolver::Answer::UNSAT) { return candidates; }

        auto core = solver.getCoreSolver().getUnsatCore();
        std::unordered_set<uint32_t> coreSet;
        for (PTRef t : core->getTerms()) { coreSet.insert(t.x); }

        std::vector<PTRef> kept;
        kept.reserve(candidates.size());
        for (std::size_t i = 0; i < candidates.size(); ++i) {
            if (coreSet.count(activationLiterals[i].x) || coreSet.count(guardedDefinitions[i].x)) {
                kept.push_back(candidates[i]);
            }
        }

        if (kept.empty()) { return candidates; }
        if (kept.size() >= candidates.size()) {
            if (++failures >= maxFail) { return candidates; }
            continue;
        }
        candidates = std::move(kept);
    }

    return candidates;
}

bool IC3IA::addPredicate(PTRef pred) {
    if (std::find(predicates_.begin(), predicates_.end(), pred) != predicates_.end()) {
        return false;
    }

    predicates_.push_back(pred);

    TimeMachine tm{logic_};
    std::ostringstream ss;
    ss << "ic3ia_pred_" << (predicates_.size() - 1);
    std::string baseName = ss.str();

    PTRef lCurr = tm.getVarVersionZero(baseName, logic_.getSort_bool());
    PTRef lNext = tm.sendVarThroughTime(lCurr, 1);

    predLabels_.push_back(lCurr);
    predLabelsNext_.push_back(lNext);
    return true;
}

void IC3IA::applyInitialReset() {
    TimeMachine tm{logic_};
    PTRef reset = tm.getVarVersionZero("ic3ia_reset", logic_.getSort_bool());
    PTRef resetNext = tm.sendVarThroughTime(reset, 1);

    PTRef oldInit = concreteInit_;
    PTRef oldTrans = concreteTrans_;
    PTRef oldBad = concreteBad_;

    concreteInit_ = reset;
    vec<PTRef> transParts;
    transParts.push(logic_.mkNot(resetNext));
    transParts.push(logic_.mkOr(logic_.mkNot(reset), atTime(oldInit, 1)));
    transParts.push(logic_.mkOr(reset, oldTrans));
    concreteTrans_ = logic_.mkAnd(transParts);
    concreteBad_ = logic_.mkAnd(logic_.mkNot(reset), oldBad);
    concreteStateVars_.push_back(reset);
    concreteNextStateVars_.push_back(resetNext);

    if (verbosity_ > 0) {
        std::cout << "[IC3IA] Added initial reset state\n";
    }
}

void IC3IA::initializePredicates() {
    std::vector<PTRef> atoms;
    collectAtoms(concreteInit_, atoms);
    collectAtoms(concreteBad_,  atoms);

    for (PTRef a : atoms) {
        addPredicate(a);
    }
}

//=============================================================================
// IC3IA — abstract system construction
//=============================================================================

PTRef IC3IA::abstractFormula(PTRef fla) const {
    if (logic_.isTrue(fla) || logic_.isFalse(fla)) { return fla; }

    for (std::size_t i = 0; i < predicates_.size(); ++i) {
        if (fla == predicates_[i])               { return predLabels_[i]; }
        if (fla == logic_.mkNot(predicates_[i])) { return logic_.mkNot(predLabels_[i]); }
    }

    Pterm const & t = logic_.getPterm(fla);

    if (logic_.isAnd(fla)) {
        vec<PTRef> args;
        for (int i = 0; i < t.size(); ++i) { args.push(abstractFormula(t[i])); }
        return logic_.mkAnd(args);
    }
    if (logic_.isOr(fla)) {
        vec<PTRef> args;
        for (int i = 0; i < t.size(); ++i) { args.push(abstractFormula(t[i])); }
        return logic_.mkOr(args);
    }
    if (logic_.isNot(fla)) {
        return logic_.mkNot(abstractFormula(t[0]));
    }

    return fla;
}

void IC3IA::initializeAbstractSystem() {
    assert(!predicates_.empty());

    init_  = concreteInit_;
    bad_   = concreteBad_;
    trans_ = concreteTrans_;
    stateVars_.clear();
    nextStateVars_.clear();
    numAssertedPreds_ = 0;

    solver_ = std::make_unique<SMTSolver>(logic_, SMTSolver::WitnessProduction::ONLY_MODEL);
    initAct_  = logic_.mkBoolVar(".ic3ia_init_act");
    transAct_ = logic_.mkBoolVar(".ic3ia_trans_act");
    solver_->assertProp(logic_.mkOr(logic_.mkNot(initAct_),  concreteInit_));
    solver_->assertProp(logic_.mkOr(logic_.mkNot(transAct_), concreteTrans_));

    extendAbstractSystem();
}

void IC3IA::extendAbstractSystem() {
    if (numAssertedPreds_ == predicates_.size()) { return; }

    vec<PTRef> newLabelDefParts;
    vec<PTRef> newNextDefParts;
    for (std::size_t i = numAssertedPreds_; i < predicates_.size(); ++i) {
        newLabelDefParts.push(logic_.mkEq(predLabels_[i], predicates_[i]));
        PTRef pNext = shiftFormulaThroughTime(predicates_[i], 1);
        newNextDefParts.push(logic_.mkEq(predLabelsNext_[i], pNext));
    }
    PTRef newLabelDefs =
        newLabelDefParts.size() == 1 ? newLabelDefParts[0] : logic_.mkAnd(newLabelDefParts);

    init_ = abstractFormula(concreteInit_);
    bad_  = abstractFormula(concreteBad_);

    vec<PTRef> transParts;
    transParts.push(trans_);
    transParts.push(newLabelDefs);
    for (int i = 0; i < newNextDefParts.size(); ++i) { transParts.push(newNextDefParts[i]); }
    trans_ = logic_.mkAnd(transParts);

    // Mirror the new conjuncts into the persistent query solver.
    solver_->assertProp(newLabelDefs);
    for (int i = 0; i < newNextDefParts.size(); ++i) {
        solver_->assertProp(newNextDefParts[i]);
    }

    stateVars_     = predLabels_;
    nextStateVars_ = predLabelsNext_;

    numAssertedPreds_ = predicates_.size();
}

PTRef IC3IA::concreteInvariant(PTRef abstractInv) const {
    TermUtils::substitutions_map subst;
    for (std::size_t i = 0; i < predicates_.size(); ++i) {
        subst[predLabels_[i]]               = predicates_[i];
        subst[logic_.mkNot(predLabels_[i])] = logic_.mkNot(predicates_[i]);
    }
    return TermUtils(logic_).varSubstitute(abstractInv, subst);
}

//=============================================================================
// IC3IA — concrete CEGAR check
//=============================================================================

PTRef IC3IA::atTime(PTRef fla, unsigned steps) const {
    return shiftFormulaThroughTime(fla, static_cast<int>(steps));
}

bool IC3IA::checkAndRefine(std::size_t & outDepth) {
    // cexTrace_ contains depth_+1 cubes: cexTrace_[i] is a guide for time i,
    // and cexTrace_.back() is the original bad-state cube (top of the
    // obligation chain). Number of transitions is one less than the number of
    // time points.
    std::size_t const k = cexTrace_.empty() ? depth_ : cexTrace_.size() - 1;
    auto const refineStart = std::chrono::steady_clock::now();

    if (verbosity_ > 1) {
        std::cout << "[IC3IA] Checking concrete trace of length " << k << "\n";
    }

    SMTSolver solver(logic_, SMTSolver::WitnessProduction::MODEL_AND_INTERPOLANTS);

    solver.getConfig().setSimplifyInterpolant(4);

    auto guideAt = [&](std::size_t index) -> PTRef {
        if (cexTrace_.empty() || index >= cexTrace_.size()) { return logic_.getTerm_true(); }
        return atTime(concreteInvariant(cubeToFla(cexTrace_[index])), static_cast<unsigned>(index));
    };

    for (std::size_t i = 0; i < k; ++i) {
        vec<PTRef> parts;
        if (i == 0) { parts.push(concreteInit_); }
        PTRef g = guideAt(i);
        if (g != logic_.getTerm_true()) { parts.push(g); }
        parts.push(atTime(concreteTrans_, static_cast<unsigned>(i)));
        solver.assertProp(parts.size() == 1 ? parts[0] : logic_.mkAnd(parts));
    }

    {
        PTRef bg = guideAt(k);
        if (bg == logic_.getTerm_true()) {
            solver.assertProp(atTime(concreteBad_, static_cast<unsigned>(k)));
        } else {
            solver.assertProp(bg);
        }
    }

    auto const solveStart = std::chrono::steady_clock::now();
    auto res = solver.check();
    auto const solveEnd = std::chrono::steady_clock::now();
    if (res == SMTSolver::Answer::SAT) {
        outDepth = k;
        if (verbosity_ > 1) {
            auto solveMs = std::chrono::duration_cast<std::chrono::milliseconds>(solveEnd - solveStart).count();
            std::cout << "[IC3IA] Concrete check SAT in " << solveMs << " ms\n";
        }
        return true;
    }
    if (res != SMTSolver::Answer::UNSAT) {
        outDepth = k;
        if (verbosity_ > 1) {
            auto solveMs = std::chrono::duration_cast<std::chrono::milliseconds>(solveEnd - solveStart).count();
            std::cout << "[IC3IA] Concrete check returned UNKNOWN in " << solveMs << " ms\n";
        }
        return true;
    }

    auto itpCtx = solver.getInterpolationContext();
    auto const interpolationStart = std::chrono::steady_clock::now();

    std::vector<PTRef> unshiftedInterpolants;
    unshiftedInterpolants.reserve(k);
    std::vector<PTRef> candidatePredicates;

    auto untimeToZero = [&](PTRef fla) -> PTRef {
        TimeMachine tm{logic_};
        std::vector<PTRef> vars;
        collectVars(fla, vars);
        TermUtils::substitutions_map subst;
        for (PTRef v : vars) {
            if (!tm.isVersioned(v)) { continue; }
            int ver = tm.getVersionNumber(v);
            if (ver == 0) { continue; }
            subst[v] = tm.sendVarThroughTime(v, -ver);
        }
        if (subst.empty()) { return fla; }
        return TermUtils(logic_).varSubstitute(fla, subst);
    };
    std::unordered_set<uint32_t> candidateSet;
    auto absorbAtomsFrom = [&](PTRef itp) {
        std::vector<PTRef> atoms;
        collectAtoms(itp, atoms);
        for (PTRef a : atoms) {
            if (candidateSet.insert(a.x).second) {
                candidatePredicates.push_back(a);
            }
        }
    };
    {
        std::vector<ipartitions_t> masks;
        masks.reserve(k);
        ipartitions_t mask = 0;
        for (std::size_t i = 0; i < k; ++i) {
            opensmt::setbit(mask, static_cast<unsigned>(i));
            masks.push_back(mask);
        }
        vec<PTRef> itps;
        itpCtx->getPathInterpolants(itps, masks);
        for (int i = 0; i < itps.size(); ++i) {
            PTRef untimed = untimeToZero(itps[i]);
            unshiftedInterpolants.push_back(untimed);
            absorbAtomsFrom(untimed);
        }
    }
    auto const interpolationEnd = std::chrono::steady_clock::now();

    {
        auto minimized = minimizeRefinementPredicateSet(candidatePredicates, unshiftedInterpolants, k);
        if (verbosity_ > 0 && minimized.size() < candidatePredicates.size()) {
            std::cout << "[IC3IA] Minimized refinement predicates from "
                      << candidatePredicates.size() << " to " << minimized.size() << "\n";
        }
        candidatePredicates = std::move(minimized);
    }

    unsigned newPreds = 0;
    for (PTRef pred : candidatePredicates) {
        if (addPredicate(pred)) { ++newPreds; }
    }

    if (verbosity_ > 0) {
        std::cout << "[IC3IA] Added " << newPreds << " new predicates\n";
    }

    if (newPreds == 0) {
        std::cerr << "[IC3IA] refinement extracted 0 new predicates. k=" << k
                  << ", existing predicates=" << predicates_.size() << "\n";
        throw std::runtime_error(
            "IC3IA refinement failure: no new predicates extracted from "
            "interpolants of a spurious counterexample");
    }

    if (verbosity_ > 1) {
        auto solveMs = std::chrono::duration_cast<std::chrono::milliseconds>(solveEnd - solveStart).count();
        auto interpolationMs =
            std::chrono::duration_cast<std::chrono::milliseconds>(interpolationEnd - interpolationStart).count();
        auto totalMs = std::chrono::duration_cast<std::chrono::milliseconds>(
            std::chrono::steady_clock::now() - refineStart).count();
        std::cout << "[IC3IA] Refinement timings (ms): solve=" << solveMs
                  << ", interpolation=" << interpolationMs
                  << ", total=" << totalMs << "\n";
    }

    return false;
}

} // namespace golem
