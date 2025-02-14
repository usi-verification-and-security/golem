/*
 * Copyright (c) 2021-2023, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "TPA.h"

#include "Common.h"
#include "ModelBasedProjection.h"
#include "QuantifierElimination.h"
#include "TermUtils.h"
#include "TransformationUtils.h"
#include "TransitionSystem.h"
#include "Witnesses.h"
#include "transformers/BasicTransformationPipelines.h"
#include "transformers/NestedLoopTransformation.h"
#include "transformers/SingleLoopTransformation.h"
#include "utils/SmtSolver.h"

#define TRACE_LEVEL 0

#define TRACE(l, m)                                                                                                    \
    if (TRACE_LEVEL >= l) { std::cout << m << std::endl; }

const std::string TPAEngine::TPA = "tpa";
const std::string TPAEngine::SPLIT_TPA = "split-tpa";

bool TPAEngine::shouldComputeWitness() const {
    return options.getOrDefault(Options::COMPUTE_WITNESS, "") == "true";
}

std::unique_ptr<TPABase> TPAEngine::mkSolver() {
    switch (coreAlgorithm) {
        case TPACore::BASIC:
            return std::make_unique<TPABasic>(logic, options);
        case TPACore::SPLIT:
            return std::make_unique<TPASplit>(logic, options);
    }
    throw std::logic_error("UNREACHABLE");
}

VerificationResult TPAEngine::solve(ChcDirectedHyperGraph const & graph) {
    auto pipeline = Transformations::towardsTransitionSystems();
    auto transformationResult = pipeline.transform(std::make_unique<ChcDirectedHyperGraph>(graph));
    auto transformedGraph = std::move(transformationResult.first);
    auto translator = std::move(transformationResult.second);
    if (transformedGraph->isNormalGraph()) {
        auto normalGraph = transformedGraph->toNormalGraph();
        auto res = solve(*normalGraph);
        return shouldComputeWitness() ? translator->translate(std::move(res)) : std::move(res);
    }
    return VerificationResult(VerificationAnswer::UNKNOWN);
}

VerificationResult TPAEngine::solve(const ChcDirectedGraph & graph) {
    if (isTrivial(graph)) { return solveTrivial(graph); }
    if (isTransitionSystem(graph)) {
        auto ts = toTransitionSystem(graph);
        auto solver = mkSolver();
        auto res = solver->solveTransitionSystem(*ts);
        if (not shouldComputeWitness()) { return VerificationResult(res); }
        switch (res) {
            case VerificationAnswer::UNSAFE:
                return VerificationResult(res, computeInvalidityWitness(graph, solver->getTransitionStepCount()));
            case VerificationAnswer::SAFE: {
                PTRef inductiveInvariant = solver->getInductiveInvariant();
                if (inductiveInvariant == PTRef_Undef) { return VerificationResult(res); }
                // std::cout << "TS invariant: " << logic.printTerm(inductiveInvariant) << std::endl;
                return VerificationResult(res, computeValidityWitness(graph, *ts, inductiveInvariant));
            }
            case VerificationAnswer::UNKNOWN:
            default:
                assert(false);
                throw std::logic_error("Unreachable!");
        }
    } else if (not options.hasOption(Options::FORCE_TS)) {
        if (options.hasOption(Options::SIMPLIFY_NESTED)) {
            NestedLoopTransformation transformation;
            auto [transformedGraph, preTranslator] = transformation.transform(graph);
            assert(isTransitionSystemDAG(*transformedGraph));
            auto res = solveTransitionSystemGraph(*transformedGraph);
            return preTranslator->translate(res);
        } else {
            return solveTransitionSystemGraph(graph);
        }
    }
    // Translate CHCGraph into transition system
    SingleLoopTransformation transformation;
    auto [ts, backtranslator] = transformation.transform(graph);
    assert(ts);
    auto solver = mkSolver();
    auto res = solver->solveTransitionSystem(*ts);
    if (not shouldComputeWitness()) { return VerificationResult(res); }
    switch (res) {
        case VerificationAnswer::UNSAFE:
            return backtranslator->translate({res, solver->getTransitionStepCount()});
        case VerificationAnswer::SAFE: {
            PTRef inductiveInvariant = solver->getInductiveInvariant();
            if (inductiveInvariant == PTRef_Undef) { return VerificationResult(res); }
            return backtranslator->translate({res, inductiveInvariant});
        }
        case VerificationAnswer::UNKNOWN:
        default:
            assert(false);
            throw std::logic_error("Unreachable!");
    }
}

class SolverWrapperSingleUse : public SolverWrapper {
    Logic & logic;
    SMTSolver solver;
    SMTSolver::Answer lastResult = SMTSolver::Answer::UNKNOWN;

public:
    SolverWrapperSingleUse(Logic & logic, PTRef transition)
        : logic(logic), solver(logic, SMTSolver::WitnessProduction::MODEL_AND_INTERPOLANTS) {
        this->transition = transition;
        solver.getConfig().setSimplifyInterpolant(4);
        solver.getConfig().setLRAInterpolationAlgorithm(itp_lra_alg_decomposing_strong);
    }

    ReachabilityResult checkConsistent(PTRef query) override {
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

    void strengthenTransition(PTRef nTransition) override { transition = logic.mkAnd(transition, nTransition); }

    std::unique_ptr<Model> lastQueryModel() override {
        if (lastResult != SMTSolver::Answer::SAT) {
            throw std::logic_error("Invalid call for obtaining a model from solver");
        }
        return solver.getModel();
    }

    PTRef lastQueryTransitionInterpolant() override {
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
};

class SolverWrapperIncremental : public SolverWrapper {
protected:
    Logic & logic;
    SMTSolver solver;
    SMTSolver::Answer lastResult = SMTSolver::Answer::UNKNOWN;

    unsigned allformulasInserted = 0;
    ipartitions_t mask = 0;
    bool pushed = false;

public:
    SolverWrapperIncremental(Logic & logic, PTRef transition)
        : logic(logic), solver(logic, SMTSolver::WitnessProduction::MODEL_AND_INTERPOLANTS) {
        //        std::cout << "Transition: " << logic.printTerm(transition) << std::endl;
        this->transition = transition;
        solver.getConfig().setSimplifyInterpolant(4);
        solver.getConfig().setLRAInterpolationAlgorithm(itp_lra_alg_decomposing_strong);
        solver.assertProp(transition);
        opensmt::setbit(mask, allformulasInserted++);
    }

    ReachabilityResult checkConsistent(PTRef query) override {
        //        std::cout << "Query: " << logic.printTerm(query) << std::endl;
        assert(not pushed);
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

    void strengthenTransition(PTRef nTransition) override {
        assert(not pushed);
        solver.push();
        solver.assertProp(nTransition);
        opensmt::setbit(mask, allformulasInserted++);
        //        std::cout << "Current number of formulas inserted: " << allformulasInserted << std::endl;
    }

    std::unique_ptr<Model> lastQueryModel() override {
        if (lastResult != SMTSolver::Answer::SAT or not pushed) {
            throw std::logic_error("Invalid call for obtaining a model from solver");
        }
        auto model = solver.getModel();
        solver.pop();
        pushed = false;
        return model;
    }

    PTRef lastQueryTransitionInterpolant() override {
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
};

class SolverWrapperIncrementalWithRestarts : public SolverWrapperIncremental {
    vec<PTRef> transitionComponents;
    const unsigned limit = 100;
    unsigned levels = 0;

    void rebuildSolver() {
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

public:
    SolverWrapperIncrementalWithRestarts(Logic & logic, PTRef transition)
        : SolverWrapperIncremental(logic, transition) {
        transitionComponents.push(transition);
    }

    ReachabilityResult checkConsistent(PTRef query) override {
        ++levels;
        if (levels > limit) {
            //            std::cout << "Rebuilding solver after " << levels << " pushes" << std::endl;
            rebuildSolver();
        }
        return SolverWrapperIncremental::checkConsistent(query);
    }

    void strengthenTransition(PTRef nTransition) override {
        SolverWrapperIncremental::strengthenTransition(nTransition);
        transitionComponents.push(nTransition);
        ++levels;
    }
};

TPASplit::~TPASplit() {
    for (SolverWrapper * solver : reachabilitySolvers) {
        delete solver;
    }
}

PTRef TPABase::getInit() const {
    return init;
}

PTRef TPABase::getTransitionRelation() const {
    return transition;
}


PTRef TPABase::getIdentity() const {
    return identity;
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
    assert(transition != logic.getTerm_false());
    if (query == logic.getTerm_false()) {
        // TODO: Check UNSAT with solver?
        explanation.inductivnessPowerExponent = 0;
        explanation.safeTransitionInvariant = logic.getTerm_true();
        explanation.relationType = TPAType::LESS_THAN;
        explanation.invariantType = SafetyExplanation::TransitionInvariantType::RESTRICTED_TO_QUERY;
        explanation.safetyExplanation = query;
        explanation.fixedPointType = SafetyExplanation::FixedPointType::LEFT;
        return VerificationAnswer::SAFE;
    }
    if (init == logic.getTerm_false()) {
        // TODO: Check UNSAT with solver?
        explanation.inductivnessPowerExponent = 0;
        explanation.safeTransitionInvariant = logic.getTerm_true();
        explanation.relationType = TPAType::LESS_THAN;
        explanation.invariantType = SafetyExplanation::TransitionInvariantType::RESTRICTED_TO_INIT;
        explanation.safetyExplanation = init;
        explanation.fixedPointType = SafetyExplanation::FixedPointType::RIGHT;
        return VerificationAnswer::SAFE;
    }
    return VerificationAnswer::UNKNOWN;
}

VerificationAnswer TPASplit::checkPower(unsigned short power) {
    TRACE(1, "Checking power " << power)
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
PTRef TPABase::cleanInterpolant(PTRef itp) {
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
        this->auxiliaryVariables.push(var);
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

void TPASplit::resetPowers() {
    this->exactPowers.clear();
    this->lessThanPowers.clear();
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
        solver.assertProp(getNextVersion(transition));
    } else {
        if (alignment == SafetyExplanation::FixedPointType::LEFT) { solver.assertProp(transition); }
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
    for (auto cand : candidates) {
        if (alignment == SafetyExplanation::FixedPointType::RIGHT) {
            if (std::find(rightInvariants.begin(), rightInvariants.end(), cand) != rightInvariants.end()) { continue; }
            rightInvariants.push(cand);
        } else {
            if (std::find(leftInvariants.begin(), leftInvariants.end(), cand) != leftInvariants.end()) { continue; }
            leftInvariants.push(cand);
        }
    }
}

bool TPABase::checkLessThanFixedPoint(unsigned short power) {
    assert(verifyPower(power, TPAType::LESS_THAN));
    for (unsigned short i = 1; i <= power; ++i) {
        PTRef currentLevelTransition = getPower(i, TPAType::LESS_THAN);
        // first check if it is a fixed point with respect to the initial states
        SMTSolver solver(logic, SMTSolver::WitnessProduction::ONLY_INTERPOLANTS);
        {
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
                explanation.invariantType = restrictedInvariant
                                                ? SafetyExplanation::TransitionInvariantType::RESTRICTED_TO_INIT
                                                : SafetyExplanation::TransitionInvariantType::UNRESTRICTED;
                explanation.relationType = TPAType::LESS_THAN;
                if(restrictedInvariant) {
                    auto itpContext = solver.getInterpolationContext();
                    ipartitions_t mask = (1 << 1); // This puts init into the A-part
                    // ipartitions_t mask = (1 << 0) + (1 << 2); // This puts init into the A-part
                    vec<PTRef> itps;
                    itpContext->getSingleInterpolant(itps, mask);
                    explanation.safetyExplanation = itps[0];
                    // explanation.safetyExplanation = logic.mkNot(itps[0]);
                }
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
                explanation.invariantType = restrictedInvariant
                                                ? SafetyExplanation::TransitionInvariantType::RESTRICTED_TO_QUERY
                                                : SafetyExplanation::TransitionInvariantType::UNRESTRICTED;
                explanation.relationType = TPAType::LESS_THAN;
                if(restrictedInvariant) {
                    auto itpContext = solver.getInterpolationContext();
                    ipartitions_t mask = (1 << 1); // This puts query into the A-part
                    // ipartitions_t mask = (1 << 0) + (1 << 2); // This puts init into the A-part
                    vec<PTRef> itps;
                    itpContext->getSingleInterpolant(itps, mask);
                    explanation.safetyExplanation = itps[0];
                    // explanation.safetyExplanation = logic.mkNot(itps[0]);
                }
                explanation.fixedPointType = SafetyExplanation::FixedPointType::LEFT;
                explanation.inductivnessPowerExponent = 0;
                explanation.safeTransitionInvariant = logic.mkAnd(logic.mkAnd(leftInvariants), currentLevelTransition);
                return true;
            }
        }
        // TODO: Move this to a separate method?
        // now check the produced if transition invariants are actually safety invariants
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
                return true;
            }
        }
    }
    return false;
}

bool TPASplit::checkExactFixedPoint(unsigned short power) {
    assert(power == 0 or verifyExactPower(power));
    for (unsigned short i = 1; i <= power; ++i) {
        PTRef currentLevelTransition = getExactPower(i);
        PTRef currentTwoStep = logic.mkAnd(currentLevelTransition, getNextVersion(currentLevelTransition));
        PTRef shifted = shiftOnlyNextVars(currentLevelTransition);
        SMTSolver solver(logic, SMTSolver::WitnessProduction::ONLY_INTERPOLANTS);
        solver.assertProp(logic.mkAnd({currentTwoStep, logic.mkNot(shifted)}));
        auto satres = solver.check();
        char restrictedInvariant = 0;
        if (satres != SMTSolver::Answer::UNSAT) {
            solver.push();
            solver.assertProp(getNextVersion(init, -1));
            solver.assertProp(getNextVersion(getLessThanPower(i), -1));
            satres = solver.check();
            if (satres == SMTSolver::Answer::UNSAT) { restrictedInvariant = 1; }
        }
        if (satres != SMTSolver::Answer::UNSAT) {
            solver.pop();
            solver.push();
            solver.assertProp(getNextVersion(query, 3));
            solver.assertProp(getNextVersion(getLessThanPower(i), 2));
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
            if(restrictedInvariant) {
                auto itpContext = solver.getInterpolationContext();
                // ipartitions_t mask = (1 << 0) + (1 << 2); // This puts query into the A-part
                ipartitions_t mask = (1 << 1); // This puts query into the A-part
                vec<PTRef> itps;
                itpContext->getSingleInterpolant(itps, mask);
                if (restrictedInvariant == 1) {
                    // explanation.safetyExplanation = logic.mkNot(getNextVersion(itps[0],1));
                    explanation.safetyExplanation = getNextVersion(itps[0],1);
                } else {
                    // explanation.safetyExplanation = logic.mkNot(getNextVersion(itps[0],-1));
                    explanation.safetyExplanation = getNextVersion(itps[0],-1);
                }
            }
            explanation.inductivnessPowerExponent = i;
            explanation.safeTransitionInvariant =
                logic.mkOr(shiftOnlyNextVars(getPower(i, TPAType::LESS_THAN)),
                           logic.mkAnd(getPower(i, TPAType::LESS_THAN), getNextVersion(getPower(i, TPAType::EQUALS))));
            return true;
        }
    }
    return false;
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

// Single hierarchy version:
TPABasic::~TPABasic() {
    for (SolverWrapper * solver : reachabilitySolvers) {
        delete solver;
    }
}

PTRef TPABasic::getLevelTransition(unsigned short power) const {
    assert(power < transitionHierarchy.size());
    return transitionHierarchy[power];
}

void TPABasic::storeLevelTransition(unsigned short power, PTRef tr) {
    //    std::cout << "Strengthening exact reachability on level " << power << " with " << logic.printTerm(tr) <<
    //    std::endl;
    if (power != 0 and not isPureTransitionFormula(tr)) {
        throw std::logic_error("Transition relation has some auxiliary variables!");
    }
    transitionHierarchy.growTo(power + 1, PTRef_Undef);
    PTRef current = transitionHierarchy[power];
    PTRef toStore = current == PTRef_Undef ? tr : TermUtils(logic).conjoin(tr, current);
    transitionHierarchy[power] = toStore;

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

SolverWrapper * TPABasic::getReachabilitySolver(unsigned short power) const {
    assert(reachabilitySolvers.size() > power);
    return reachabilitySolvers[power];
}

VerificationAnswer TPABasic::checkPower(unsigned short power) {
    TRACE(1, "Checking power " << power)
    queryCache.emplace_back();
    auto res = reachabilityQuery(init, query, power);
    if (isReachable(res)) {
        reachedStates = ReachedStates{res.refinedTarget, res.steps};
        return VerificationAnswer::UNSAFE;
    } else if (isUnreachable(res)) {
        if (verbose() > 0) { std::cout << "; System is safe up to <=2^" << power + 1 << " steps" << std::endl; }
        // Check if we have not reached fixed point.
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
    TRACE(2, "Checking LEQ reachability on level " << power << " from " << from.x << " to " << to.x)
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
        auto solver = getReachabilitySolver(power + 1);
        assert(solver);
        auto res = solver->checkConsistent(logic.mkAnd(from, goal));
        switch (res) {
            case ReachabilityResult::REACHABLE: {
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
                    TRACE(3, "Exact: Truly reachable states are " << result.refinedTarget.x)
                    assert(result.refinedTarget != logic.getTerm_false());
                    queryCache[power].insert({{from, to}, result});
                    return result;
                }
                // Create the three states corresponding to current, next and next-next variables from the query
                PTRef nextState = extractMidPoint(from, previousTransition, translatedPreviousTransition, goal, *model);
                //              std::cout << "Midpoint single point: " << logic.printTerm(modelMidpoint) << '\n';
                TRACE(3, "Midpoint from MBP: " << nextState.x)
                assert(power != 0);
                // check the reachability using lower level abstraction
                auto subQueryRes = reachabilityQuery(from, nextState, power - 1);
                if (isUnreachable(subQueryRes)) {
                    TRACE(3, "Exact: First half was unreachable, repeating...")
                    assert(getLevelTransition(power) != previousTransition);
                    continue; // We need to re-check this level with refined abstraction
                } else {
                    assert(isReachable(subQueryRes));
                    TRACE(3, "Exact: First half was reachable")
                    nextState = extractReachableTarget(subQueryRes);
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
                // If itp == logic.getTerm_true, then the error states were trivially unreachable
                if (itp == logic.getTerm_true()) { assert(power == 0); }
                storeLevelTransition(power + 1, itp);
                result.result = ReachabilityResult::UNREACHABLE;
                return result;
            }
        }
    }
}

void TPABasic::resetPowers() {
    this->transitionHierarchy.clear();
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


enum class NodeState { PRE, POST };
struct Entry {
    NodeState state;
    SymRef node;
    std::optional<EId> incomingEdge; // Edge used to get into this node, valid only for PRE state
    std::optional<std::vector<Entry>> subPath; // Edge used to get into this node, valid only for PRE state
    std::optional<size_t> iteration_num; // Edge used to get into this node, valid only for PRE state
    PTRef reached;
};

using Path = std::vector<Entry>;

/*
 * Extension for DAG of transition systems
 */
class TransitionSystemNetworkManager {
    TPAEngine & owner;
    Logic & logic;
    ChcDirectedGraph const & graph;
    AdjacencyListsGraphRepresentation adjacencyRepresentation;


public:
    TransitionSystemNetworkManager(TPAEngine & owner, ChcDirectedGraph const & graph)
        : owner(owner), logic(owner.logic), graph(graph),
          adjacencyRepresentation(AdjacencyListsGraphRepresentation::from(graph)) {}

    VerificationResult solve() &&;

private:
    struct NetworkNode {
        std::unique_ptr<TPABase> solver{nullptr};
        PTRef preSafe{PTRef_Undef};
        PTRef preSafeLoop{PTRef_Undef};
        PTRef preTemp{PTRef_Undef};
        PTRef preSafeLoopW{PTRef_Undef};
        // TODO: preSafe and postSafe are being overwritten during solving
        //       ideally we would create Network nodes as we discover graph
        PTRef postSafe{PTRef_Undef};
        PTRef postSafeLoop{PTRef_Undef};
        PTRef postTemp{PTRef_Undef};
        PTRef postSafeLoopW{PTRef_Undef};
        PTRef loopSafe{PTRef_Undef};
        std::size_t blocked_children{0};
        std::vector<EId> children;
        std::vector<PTRef> blockedReason;
        std::vector<std::vector<EId>> loops;
        std::set<EId> loopEdges;
        std::vector<PTRef> loopTransitions;
        PTRef loopInvariant{PTRef_Undef};
        PTRef transitionInvariant{PTRef_Undef};
    };

    std::unordered_map<SymRef, NetworkNode, SymRefHash> networkMap;

    struct QueryResult {
        ReachabilityResult reachabilityResult;
        PTRef explanation;
        std::optional<Path> subpath;
    };

    [[nodiscard]] static bool reachable(ReachabilityResult res) { return res == ReachabilityResult::REACHABLE; }

    void initNetwork();

    [[nodiscard]] std::unique_ptr<TPABase> mkSolver() const { return owner.mkSolver(); }

    [[nodiscard]] TransitionSystem constructTransitionSystemFor(SymRef vid) const;

    [[nodiscard]] NetworkNode & getNode(SymRef vid) { return networkMap.at(vid); }
    [[nodiscard]] NetworkNode const & getNode(SymRef vid) const { return networkMap.at(vid); }

    [[nodiscard]] vec<SymRef> getGraphStarts() const {
        vec<SymRef> graphStarts;
        for (auto outgoingEdge : adjacencyRepresentation.getOutgoingEdgesFor(graph.getEntry())) {
            graphStarts.push(graph.getTarget(outgoingEdge));
        }
        return graphStarts;
    }

    [[nodiscard]] vec<SymRef> getGraphEnds() const {
        vec<SymRef> graphEnds;
        for (auto incomingEdge : adjacencyRepresentation.getIncomingEdgesFor(graph.getExit())) {
            graphEnds.push(graph.getSource(incomingEdge));
        }
        return graphEnds;
    }

    [[nodiscard]] QueryResult queryEdge(EId eid, PTRef sourceCondition, PTRef targetCondition) const;

    [[nodiscard]] QueryResult queryTransitionSystem(NetworkNode const & node, PTRef sourceCondition,
                                                    PTRef targetCondition) const;

    [[nodiscard]] QueryResult queryLoops(NetworkNode & node, PTRef sourceCondition, PTRef targetCondition) ;

    [[nodiscard]] Path produceExactReachedStates(NetworkNode & node, TPABase const & solver, std::vector<std::vector<EId>> const & loops) ;

    [[nodiscard]] witness_t computeInvalidityWitness(Path const & path) const;

    [[nodiscard]] std::vector<EId> extractPath(Path const & path) const;

    [[nodiscard]] PTRef produceUnrolling(int depth, PTRef vars) const;

    [[nodiscard]] std::tuple <PTRef, std::unique_ptr<SystemType>> produceMergedTransition(NetworkNode & node, std::vector<std::vector<EId>> const & loops) const;

    [[nodiscard]] witness_t computeValidityWitness();
};

VerificationResult TPAEngine::solveTransitionSystemGraph(const ChcDirectedGraph & graph) {
    return TransitionSystemNetworkManager(*this, graph).solve();
}

void TransitionSystemNetworkManager::initNetwork() {
    assert(networkMap.empty());
    for (auto vid : graph.getVertices()) {
        auto [it, _] = networkMap.insert({vid, NetworkNode()});
        auto & node = it->second;
        node.preSafe = logic.getTerm_false();
        node.postSafe = logic.getTerm_false();
        node.preSafeLoop = logic.getTerm_false();
        node.postSafeLoop = logic.getTerm_false();
        node.preSafeLoopW = logic.getTerm_false();
        node.postSafeLoopW = logic.getTerm_false();
        node.loopSafe = logic.getTerm_false();
        node.transitionInvariant = logic.getTerm_true();
        node.blocked_children = 0;
        if (vid == graph.getEntry() or vid == graph.getExit()) { continue; }
        node.solver = mkSolver();
        TransitionSystem ts = constructTransitionSystemFor(vid);
        node.solver->resetTransitionSystem(ts);
        node.loops = {};
        node.loopTransitions = {};
    }
    // Connect the network
    auto isSelfLoop = [this](EId eid) { return graph.getSource(eid) == graph.getTarget(eid); };
    // TODO: no need for reverse post order, better to process outgoing edges
    for (auto vid : reversePostOrder(graph, adjacencyRepresentation)) {
        if (vid != graph.getEntry()) {
            auto incomingEdges = adjacencyRepresentation.getIncomingEdgesFor(vid);
            for (auto edge : incomingEdges) {
                if (isSelfLoop(edge)) { continue; }
                getNode(graph.getSource(edge)).children.push_back(edge);
                getNode(graph.getSource(edge)).blockedReason.push_back(PTRef_Undef);
            }
        }
    }
}



VerificationResult TransitionSystemNetworkManager::solve() && {
    initNetwork();
    Path path;
    path.push_back({NodeState::POST, graph.getEntry(), std::nullopt, std::nullopt, std::nullopt, logic.getTerm_true()});
    while (not path.empty()) {
        auto const & [state, node, eid, subpath, iterations, reached] = path.back();
        auto & networkNode = getNode(node);
        switch (state) {
            case NodeState::PRE: // Traverse loop
            {
                PTRef start = reached;
                if(subpath.has_value()){
                    start = subpath.value().back().reached;
                }
                auto res = queryTransitionSystem(networkNode, start, logic.mkNot(networkNode.postSafe));
                if (res.reachabilityResult == ReachabilityResult::REACHABLE) {
                    path.push_back({NodeState::POST, node, std::nullopt, std::nullopt, networkNode.solver->getTransitionStepCount(), res.explanation});
                } else {
                    networkNode.preSafe = logic.mkOr(networkNode.preSafe, res.explanation);

                    if(networkNode.solver->getRestricted()){
                        networkNode.transitionInvariant = logic.mkAnd(networkNode.transitionInvariant, logic.mkOr(logic.mkAnd(networkNode.solver->getRestrictedExpl(), networkNode.solver->getTransitionInvariant()), logic.mkNot(networkNode.solver->getRestrictedExpl())));
                    } else {
                        networkNode.transitionInvariant = logic.mkAnd(networkNode.transitionInvariant, networkNode.solver->getTransitionInvariant());
                    }
                    if(networkNode.loopEdges.empty()) {
                        networkNode.preSafeLoopW = networkNode.preSafe;
                    }
                    if(!networkNode.loops.empty()) {
                        //TODO: Nested loops handling
                        res = queryLoops(networkNode, reached, logic.mkNot(networkNode.preSafe));
                        if(res.reachabilityResult == ReachabilityResult::REACHABLE) {
                            assert(res.subpath.has_value());
                            path.pop_back();
                            path.push_back({NodeState::PRE, node, eid, res.subpath, std::nullopt, reached});
                            continue;
                        } else {
                            networkNode.loopSafe = logic.mkOr(networkNode.loopSafe, res.explanation);
                            networkNode.preSafe = networkNode.loopSafe;
                            //TODO: I need to return both trInv for the loop (for further analysis) and state invariant
                            //TODO: to block incoming states
                        }
                    }
                    if(!networkNode.loopEdges.empty()) {getNode(graph.getSource(eid.value())).loopEdges.insert(eid.value());}
                    path.pop_back();
                }
                break;
            }
            case NodeState::POST: // Traverse bridge
            {
                if (networkNode.blocked_children == networkNode.children.size()) { // No way out
                    PTRef blocked = logic.mkAnd(networkNode.blockedReason);
                    networkNode.postSafe = logic.mkOr(networkNode.postSafe, blocked);
                    if(networkNode.loopEdges.empty()) {networkNode.postSafeLoopW = networkNode.postSafe;}
                    path.pop_back();
                    for (PTRef & reason : networkNode.blockedReason) {
                        reason = PTRef_Undef;
                    }
                    networkNode.blocked_children = 0;
                } else { // Try continuing with the next edge
                    assert(networkNode.blocked_children < networkNode.children.size());
                    auto childIndex = networkNode.blocked_children;
                    EId nextEdge = networkNode.children[childIndex];
                    auto target = graph.getTarget(nextEdge);
                    // Check if we have a nested loop in the structure
                    // If we do, save the nested loop to the source of this nested loop and try to find other paths
                    auto loophead = std::find_if(path.begin(), path.end(), [target](auto step)
                                                 {return step.node == target;});
                    if (loophead != path.end()) {
                        // We should ignore first node (it is PRE of entry to the loop)
                        if(std::find(networkNode.loopEdges.begin(), networkNode.loopEdges.end(), nextEdge) == networkNode.loopEdges.end()) {
                            loophead += 1;
                            getNode(target).loops.push_back({});
                            while (loophead != path.end()) {
                                if (loophead->incomingEdge.has_value()) {
                                    getNode(target).loops.back().push_back(loophead->incomingEdge.value());
                                }
                                loophead++;
                            }
                            getNode(target).loops.back().push_back(nextEdge);
                            networkNode.loopEdges.insert(nextEdge);
                        }
                        networkNode.blockedReason[childIndex] = logic.getTerm_true();
                        ++networkNode.blocked_children;
                        continue;
                    }
                    auto res = queryEdge(nextEdge, reached, logic.mkNot(getNode(target).preSafe));
                    if (res.reachabilityResult == ReachabilityResult::REACHABLE) {
                        path.push_back({NodeState::PRE, target, nextEdge, std::nullopt,  std::nullopt, res.explanation});
                        if (target == graph.getExit()) {
                            witness_t witness = owner.shouldComputeWitness()
                                                    ? computeInvalidityWitness(path)
                                                    : NoWitness{};
                            return {VerificationAnswer::UNSAFE, std::move(witness)};
                        }
                    } else {
                        networkNode.blockedReason[childIndex] = res.explanation;
                        ++networkNode.blocked_children;
                    }
                }
                break;
            }
        }
    }
    witness_t witness = owner.shouldComputeWitness() ? computeValidityWitness() : NoWitness{};
    return {VerificationAnswer::SAFE, std::move(witness)};
}

std::vector<EId> TransitionSystemNetworkManager::extractPath(Path const & path) const {
    std::vector<EId> res;
    for (auto const & entry : path) {
        if (entry.state == NodeState::PRE) {
            res.push_back(entry.incomingEdge.value());
            if(entry.subPath.has_value()){
                auto subpath = extractPath(entry.subPath.value());
                res.insert(res.end(), subpath.begin(), subpath.end());
            }
        } else {
            if(entry.iteration_num.has_value()){
                auto steps = entry.iteration_num.value();
                res.insert(res.end(), steps, getSelfLoopFor(entry.node, graph, adjacencyRepresentation).value());
            }
        }
    }
    return res;
}


witness_t TransitionSystemNetworkManager::computeInvalidityWitness(Path const & path) const {
    std::vector<EId> errorPath = extractPath(path);

//    for (EId edge : path) {
//        errorPath.push_back(edge);
//        SymRef target = graph.getTarget(edge);
//        if (target != graph.getExit()) {
//            auto steps = getNode(target).solver->getTransitionStepCount();
//            errorPath.insert(errorPath.end(), steps, getSelfLoopFor(target, graph, adjacencyRepresentation).value());
//        }
//    }
    return InvalidityWitness::fromErrorPath(ErrorPath{std::move(errorPath)}, graph);
}

witness_t TransitionSystemNetworkManager::computeValidityWitness() {
    assert(isTransitionSystemDAG(graph));
    TermUtils utils(logic);
    TimeMachine timeMachine(logic);
    ValidityWitness::definitions_t definitions;

    for (auto vertex : graph.getVertices()) {
        if (vertex == graph.getEntry() || vertex == graph.getExit()) continue;
        auto & node = getNode(vertex);

        auto graphVars = utils.predicateArgsInOrder(graph.getStateVersion(vertex));
        vec<PTRef> unversionedVars;
        auto systemVars = node.solver->getStateVars(0);

        TermUtils::substitutions_map subs;
        for (std::size_t i = 0; i < graphVars.size(); ++i) {
            unversionedVars.push(timeMachine.getUnversioned(graphVars[i]));
            subs.insert({systemVars[i], unversionedVars.last()});
        }
        auto [res, explanation, subpath] = queryTransitionSystem(node, node.preSafe, logic.mkNot(node.postSafe));
        assert(res == ReachabilityResult::UNREACHABLE);
        if (res == ReachabilityResult::UNREACHABLE) {
            PTRef graphInvariant = utils.varSubstitute(node.solver->getInductiveInvariant(), subs);
            PTRef unversionedPredicate = logic.mkUninterpFun(vertex, std::move(unversionedVars));
            definitions[unversionedPredicate] = graphInvariant;
        } else {
            return NoWitness("Unexpected situation occurred during witness computation in TPA engine");
        }
    }
    return ValidityWitness(std::move(definitions));
}

TransitionSystem TransitionSystemNetworkManager::constructTransitionSystemFor(SymRef vid) const {
    EId loopEdge = getSelfLoopFor(vid, graph, adjacencyRepresentation).value();
    auto edgeVars = getVariablesFromEdge(logic, graph, loopEdge);
    auto systemType = std::make_unique<SystemType>(edgeVars.stateVars, edgeVars.auxiliaryVars, logic);
    PTRef loopLabel = graph.getEdgeLabel(loopEdge);
    PTRef transitionFla = transitionFormulaInSystemType(*systemType, edgeVars, loopLabel, logic);
    return TransitionSystem(logic, std::move(systemType), logic.getTerm_true(), transitionFla, logic.getTerm_true());
}


[[nodiscard]] std::tuple <PTRef, std::unique_ptr<SystemType>> TransitionSystemNetworkManager::produceMergedTransition(NetworkNode & node, std::vector<std::vector<EId>> const & loops) const {
    assert(!loops.empty());
    TimeMachine timeMachine(logic);
    TermUtils utils(logic);
    PTRef generalMTr = logic.getTerm_false();
    auto edgeVars = getVariablesFromEdge(
        logic, graph, getSelfLoopFor(graph.getSource(loops[0][0]), graph, adjacencyRepresentation).value());
    vec<PTRef> coreVars;
    for(auto var: edgeVars.stateVars){
        coreVars.push(var);
        coreVars.push(timeMachine.sendFlaThroughTime(var, 1));
    }

    for (const auto& loop: loops) {
        assert(loop.size() > 1);
        PTRef loopMTr = logic.getTerm_true();
        int n = 0;
        for (int i = 0; i < loop.size(); i++) {
            auto const & source = getNode(graph.getSource(loop[i]));
            PTRef nestedLoopTrInv = source.loopInvariant == PTRef_Undef || i == 0 ? logic.getTerm_false() : logic.mkAnd(timeMachine.sendFlaThroughTime(source.loopInvariant, n), timeMachine.sendFlaThroughTime(source.transitionInvariant, n+2));
            // PTRef loopTrInv = source.solver->getTransitionInvariant() == PTRef_Undef ? logic.getTerm_true() : timeMachine.sendFlaThroughTime(source.solver->getTransitionInvariant(), n);

            PTRef loopTrInv = timeMachine.sendFlaThroughTime(source.transitionInvariant, n);
            PTRef loopInv = nestedLoopTrInv == logic.getTerm_false() ? loopTrInv : nestedLoopTrInv;
            n = nestedLoopTrInv == logic.getTerm_false() ? n + 2 : n + 4;
            // if (nestedLoopTrInv != logic.getTerm_false()) {
                // loopTrInv = logic.mkAnd({loopTrInv, timeMachine.sendFlaThroughTime(node.solver->getIdentity(),n),  timeMachine.sendFlaThroughTime(node.solver->getIdentity(),n+1)});
                // n+=2;
            // }
            PTRef label = timeMachine.sendFlaThroughTime(graph.getEdgeLabel(loop[i]), n++);
            loopMTr = logic.mkAnd({loopMTr, loopInv, label});
//            loopMTr = logic.mkAnd({loopMTr, loopTrInv, label});
        }
        std::unordered_map<PTRef, PTRef, PTRefHash> subMap;
        for(auto var: edgeVars.stateVars){
            subMap.insert(std::make_pair(timeMachine.sendVarThroughTime(var,1), timeMachine.sendVarThroughTime(var,n)));
            subMap.insert(std::make_pair(timeMachine.sendVarThroughTime(var,n), timeMachine.sendVarThroughTime(var,1)));
        }
        loopMTr = utils.varSubstitute(loopMTr, subMap);
        PTRef form = QuantifierElimination(logic).keepOnly(loopMTr, coreVars);
        node.loopTransitions.push_back(form);
        generalMTr = logic.mkOr(generalMTr, form);
    }
    auto systemType = std::make_unique<SystemType>(edgeVars.stateVars, edgeVars.auxiliaryVars, logic);
    PTRef transitionFla = transitionFormulaInSystemType(*systemType, edgeVars, generalMTr, logic);
    return {transitionFla, std::move(systemType)};
}

TransitionSystemNetworkManager::QueryResult TransitionSystemNetworkManager::queryEdge(EId eid, PTRef sourceCondition,
                                                                                      PTRef targetCondition) const {
    SMTSolver solver(logic, SMTSolver::WitnessProduction::MODEL_AND_INTERPOLANTS);
    solver.getConfig().setLRAInterpolationAlgorithm(itp_lra_alg_decomposing_strong);
    solver.getConfig().setSimplifyInterpolant(4);
    PTRef label = graph.getEdgeLabel(eid);
    TRACE(1, "Querying edge " << eid.id << " with label " << logic.pp(label) << "\n\tsource is "
                              << logic.pp(sourceCondition) << "\n\ttarget is " << logic.pp(targetCondition))
    PTRef target = TimeMachine(logic).sendFlaThroughTime(targetCondition, 1);
    solver.assertProp(sourceCondition);
    solver.assertProp(label);
    solver.assertProp(target);
    auto res = solver.check();
    if (res == SMTSolver::Answer::SAT) {
        auto model = solver.getModel();
        ModelBasedProjection mbp(logic);
        PTRef query = logic.mkAnd({sourceCondition, label});
        auto targetVars = TermUtils(logic).predicateArgsInOrder(graph.getNextStateVersion(graph.getTarget(eid)));
        PTRef eliminated = mbp.keepOnly(query, targetVars, *model);
        eliminated = TimeMachine(logic).sendFlaThroughTime(eliminated, -1);
        TRACE(1, "Propagating along the edge " << logic.pp(eliminated))
        return {ReachabilityResult::REACHABLE, eliminated};
    } else if (res == SMTSolver::Answer::UNSAT) {
        auto itpContext = solver.getInterpolationContext();
        ipartitions_t mask = (1 << 1) + (1 << 2); // This puts label + target into the A-part

        vec<PTRef> itps;
        itpContext->getSingleInterpolant(itps, mask);
        assert(itps.size() == 1);
        PTRef explanation = logic.mkNot(itps[0]);
        TRACE(1, "Blocking edge with " << logic.pp(explanation))
        return {ReachabilityResult::UNREACHABLE, explanation};
    }
    throw std::logic_error("Error in the underlying SMT solver");
}

TransitionSystemNetworkManager::QueryResult
TransitionSystemNetworkManager::queryTransitionSystem(NetworkNode const & node, PTRef sourceCondition,
                                                      PTRef targetCondition) const {
    node.solver->resetInitialStates(sourceCondition);
    node.solver->resetQueryStates(targetCondition);
    auto res = node.solver->solve();
    assert(res != VerificationAnswer::UNKNOWN);
    switch (res) {
        case VerificationAnswer::UNSAFE: {
            PTRef reachedPostStates = node.solver->getReachedStates();
            assert(reachedPostStates != PTRef_Undef);
            TRACE(1, "TS propagates reachable states to " << logic.pp(reachedPostStates))
            return {ReachabilityResult::REACHABLE, reachedPostStates};
        }
        case VerificationAnswer::SAFE: {
            PTRef explanation = node.solver->getSafetyExplanation();
            assert(explanation != PTRef_Undef);
            TRACE(1, "TS blocks " << logic.pp(explanation))
            return {ReachabilityResult::UNREACHABLE, explanation};
        }
        default:
            assert(false);
            throw std::logic_error("Unreachable");
    }
}

TransitionSystemNetworkManager::QueryResult
TransitionSystemNetworkManager::queryLoops(NetworkNode & node, PTRef sourceCondition, PTRef targetCondition) {
    while(true) {
        auto [mergedTransition, systemType] = produceMergedTransition(node, node.loops);
        std::unique_ptr<TPABase> solver{nullptr};
        solver = mkSolver();
        solver->resetTransitionSystem(
            TransitionSystem(logic, std::move(systemType), sourceCondition, mergedTransition, targetCondition));
        auto res = solver->solve();
        assert(res != VerificationAnswer::UNKNOWN);
        switch (res) {
            case VerificationAnswer::SAFE: {
                PTRef explanation = solver->getSafetyExplanation();
                PTRef trInv = solver->getTransitionInvariant();
                if (solver->getRestricted()) {
                    trInv = logic.mkOr(logic.mkAnd(trInv, solver->getRestrictedExpl()), logic.mkNot(solver->getRestrictedExpl()));
                }
                node.loopInvariant = node.loopInvariant == PTRef_Undef ? trInv : logic.mkAnd(node.loopInvariant, trInv);
                assert(explanation != PTRef_Undef);
                node.loopTransitions = {};
                TRACE(1, "TS blocks " << logic.pp(explanation))
                return {ReachabilityResult::UNREACHABLE, explanation, {}};
            }
            case VerificationAnswer::UNSAFE: {
                if (solver->getTransitionStepCount() == 0) {
                    return {ReachabilityResult::REACHABLE, sourceCondition, {}};
                }
                Path states = produceExactReachedStates(node, *solver, node.loops);
                node.loopTransitions = {};
                if (states.empty()) { continue;}
                return {ReachabilityResult::REACHABLE, states.back().reached, states};
            }
            default:
                assert(false);
                throw std::logic_error("Unreachable");
        }
    }
}

Path TransitionSystemNetworkManager::produceExactReachedStates(NetworkNode & node, TPABase const & solver, std::vector<std::vector<EId>> const & loops) {
    PTRef reached = solver.getReachedStates();
    PTRef transition = solver.getTransitionRelation();
    PTRef init = solver.getInit();
    uint transitions = solver.getTransitionStepCount();
    PTRef query = logic.mkAnd(init, TimeMachine(logic).sendFlaThroughTime(reached, transitions));
    for(int i=0; i < transitions; i++){
        query = logic.mkAnd(query, TimeMachine(logic).sendFlaThroughTime(transition, i));
    }
    PTRef reachedRefined = init;
    auto edgeVars = getVariablesFromEdge(
        logic, graph, getSelfLoopFor(graph.getSource(loops[0][0]), graph, adjacencyRepresentation).value());
    Path subPath;
    for(int i=0; i < transitions; i++){
        vec<PTRef> coreVars;
        for(auto var: edgeVars.stateVars){
            coreVars.push(TimeMachine(logic).sendVarThroughTime(var, i+1));
        }
        PTRef subquery = TimeMachine(logic).sendFlaThroughTime(QuantifierElimination(logic).keepOnly(query, coreVars), -(i+1));
        SMTSolver smtSolver(logic, SMTSolver::WitnessProduction::NONE);

        for(int j = 0; j < node.loopTransitions.size(); j++){
            if (!subPath.empty()) {
                reachedRefined = subPath.back().reached;
            }
            smtSolver.assertProp(reachedRefined);
            smtSolver.assertProp(node.loopTransitions[j]);
            smtSolver.assertProp(TimeMachine(logic).sendFlaThroughTime(subquery,1));
            auto res = smtSolver.check();
            smtSolver.resetSolver();
            bool save = true;
            if(res == SMTSolver::Answer::SAT) {

                uint preSize = subPath.size();
                for(auto edge : node.loops[j]){
                    auto & networkNode = getNode(graph.getSource(edge));
                    networkNode.preSafeLoop = networkNode.preSafeLoopW;
                    networkNode.postSafeLoop = networkNode.postSafeLoopW;
                }

                for(int l = 0; l < node.loops[j].size()*2;){
                    if (!subPath.empty()) {
                        reachedRefined = subPath.back().reached;
                    } else {
                        reachedRefined = init;
                    }
                    int k = l/2;
                    auto edge = node.loops[j][k];
                    auto & networkNode = getNode(graph.getSource(edge));
                    if ( l%2 == 0 ) {
                        if (!subPath.empty() && subPath.back().subPath.has_value()) {
                            reachedRefined = subPath.back().subPath.value().back().reached;
                        }
                        auto res = queryTransitionSystem(networkNode, reachedRefined, logic.mkNot(networkNode.postSafeLoop));
                        if (res.reachabilityResult == ReachabilityResult::REACHABLE) {
                            subPath.push_back({NodeState::POST, graph.getSource(edge), std::nullopt, std::nullopt, networkNode.solver->getTransitionStepCount(), res.explanation});
                            l++;
                        } else {
                            if(networkNode.solver->getRestricted()){
                                networkNode.transitionInvariant = logic.mkAnd(networkNode.transitionInvariant, logic.mkOr(logic.mkAnd(networkNode.solver->getRestrictedExpl(), networkNode.solver->getTransitionInvariant()), logic.mkNot(networkNode.solver->getRestrictedExpl())));
                            } else {
                                networkNode.transitionInvariant = logic.mkAnd(networkNode.transitionInvariant, networkNode.solver->getTransitionInvariant());
                            }
                            networkNode.preSafeLoop = logic.mkOr(networkNode.preSafeLoop, res.explanation);
                            if(l == 0) {
                                if (save) {
                                    networkNode.preSafeLoopW = networkNode.preSafeLoop;
                                    networkNode.postSafeLoopW = networkNode.postSafeLoop;
                                }
                                if(j < node.loopTransitions.size() - 1){
                                    break;
                                }
                                return {};
                            }
                            if (!networkNode.loops.empty()) {
                                for(auto loop : networkNode.loops) {
                                    for (auto edge: loop) {
                                        auto & networkNode = getNode(graph.getSource(edge));
                                        networkNode.preTemp = networkNode.preSafeLoop;
                                        networkNode.postTemp = networkNode.postSafeLoop;
                                    }
                                }
                                auto res = queryLoops(networkNode, subPath.back().reached, logic.mkNot(networkNode.preSafeLoop));
                                for(auto loop : networkNode.loops) {
                                    for (auto edge: loop) {
                                        auto & networkNode = getNode(graph.getSource(edge));
                                        networkNode.preSafeLoop = networkNode.preTemp;
                                        networkNode.postSafeLoop = networkNode.postTemp;
                                    }
                                }
                                if (res.reachabilityResult == ReachabilityResult::REACHABLE) {
                                    PTRef temp = subPath.back().reached;
                                    subPath.pop_back();
                                    subPath.push_back(
                                        {NodeState::PRE, graph.getSource(edge), edge, res.subpath,  std::nullopt, temp});
                                } else {
                                    // networkNode.preSafeLoop = logic.mkOr(networkNode.preSafeLoop, res.explanation);
                                    // res = queryLoops(networkNode, reached, logic.mkNot(networkNode.preSafe));
                                    // if(res.reachabilityResult == ReachabilityResult::REACHABLE) {
                                        // assert(res.subpath.has_value());
                                        // subPath.pop_back();
                                        // subPath.push_back({NodeState::PRE, graph.getSource(edge), edge, res.subpath, std::nullopt, reached});
                                        // continue;
                                    // }
                                    // networkNode.loopSafe = res.explanation;
                                    networkNode.loopSafe = logic.mkOr(networkNode.loopSafe, res.explanation);
                                    networkNode.preSafeLoop = res.explanation;
                                    // TODO: I need to return both trInv for the loop (for further analysis) and state invariant
                                    // TODO: to block incoming states
                                    subPath.pop_back();
                                    l--;
                                }
                            } else {
                                subPath.pop_back();
                                l--;
                            }
                        }
                    } else {
                        auto target = graph.getTarget(edge);
                        TransitionSystemNetworkManager::QueryResult res;
                        if (l == node.loops[j].size()*2-1 ) {
                            res = queryEdge(edge, reachedRefined, logic.mkNot(getNode(target).preSafe));
                            //TODO: Figure out why this thing is necessary!!!
                            if (res.reachabilityResult == ReachabilityResult::REACHABLE) {
                                subPath.push_back({NodeState::PRE, target, edge, std::nullopt,  std::nullopt, res.explanation});
                                return subPath;
                            }
                            save = false;
                            res = queryEdge(edge, reachedRefined, logic.mkAnd(logic.mkNot(getNode(target).preSafeLoop), subquery));
                        } else {
                            res = queryEdge(edge, reachedRefined, logic.mkNot(getNode(target).preSafeLoop));
                        }
                        if (res.reachabilityResult == ReachabilityResult::REACHABLE) {
                            subPath.push_back({NodeState::PRE, target, edge, std::nullopt,  std::nullopt, res.explanation});
                            l++;
                        } else {
                            networkNode.postSafeLoop = logic.mkOr(networkNode.postSafeLoop, res.explanation);
                            subPath.pop_back();
                            l--;
                        }
                    }
                    if (save) {
                        networkNode.preSafeLoopW = networkNode.preSafeLoop;
                        networkNode.postSafeLoopW = networkNode.postSafeLoop;
                    }
                }

                if (preSize < subPath.size()){
                    break;
                }
            } else {
                if (j == node.loopTransitions.size() - 1){
                    return {};
                }
            }
        }
    }
    return subPath;
}

PTRef TPASplit::getPower(unsigned short power, TPAType relationType) const {
    if (relationType == TPAType::LESS_THAN) { return getLessThanPower(power); }
    assert(relationType == TPAType::EQUALS);
    return getExactPower(power);
}

PTRef TPABasic::getPower(unsigned short power, TPAType relationType) const {
    assert(relationType == TPAType::LESS_THAN);
    (void)relationType;
    return getLevelTransition(power);
}

PTRef TPABase::getReachedStates() const {
    return reachedStates.reachedStates;
}

unsigned TPABase::getTransitionStepCount() const {
    return reachedStates.steps;
}

PTRef TPABase::getTransitionInvariant() const {
    if(explanation.relationType == TPAType::LESS_THAN) {
            return shiftOnlyNextVars(explanation.safeTransitionInvariant);
    } else {
        return explanation.safeTransitionInvariant;
    }
}

PTRef TPABase::getRestrictedExpl() const {
//    if(explanation.invariantType == SafetyExplanation::TransitionInvariantType::RESTRICTED_TO_QUERY){
//        return shiftOnlyNextVars(explanation.safeTransitionInvariant);
//    }
    return explanation.safetyExplanation;
}

bool TPABase::getRestricted() const {
    if(explanation.invariantType == SafetyExplanation::TransitionInvariantType::UNRESTRICTED) {
        return false;
    } else {
        return true;
    }
}


/*
 * Returns superset of init that are still safe
 */
PTRef TPABase::getSafetyExplanation() const {
    if (explanation.invariantType == SafetyExplanation::TransitionInvariantType::RESTRICTED_TO_INIT) {
        // TODO: compute the safe inductive invariant and return negation of that?
        // return explanation.safetyExplanation;
        // return getInductiveInvariant();
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

InvalidityWitness TPAEngine::computeInvalidityWitness(ChcDirectedGraph const & graph, unsigned steps) const {
    return InvalidityWitness::fromTransitionSystem(graph, steps);
}

ValidityWitness TPAEngine::computeValidityWitness(ChcDirectedGraph const & graph, TransitionSystem const & ts,
                                                  PTRef inductiveInvariant) const {
    return ValidityWitness::fromTransitionSystem(logic, graph, ts, inductiveInvariant);
}