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
#include "transformers/BasicTransformationPipelines.h"

#define TRACE_LEVEL 0

#define TRACE(l, m)                                                                                                    \
    if (TRACE_LEVEL >= l) { std::cout << m << std::endl; }

const std::string TPAEngine::TPA = "tpa";
const std::string TPAEngine::SPLIT_TPA = "split-tpa";

std::unique_ptr<TPABase> TPAEngine::mkSolver() {
    assert(options.hasOption(Options::ENGINE));
    auto val = options.getOption(Options::ENGINE);
    if (val == SPLIT_TPA) {
        return std::unique_ptr<TPABase>(new TPASplit(logic, options));
    } else if (val == TPA) {
        return std::unique_ptr<TPABase>(new TPABasic(logic, options));
    }
    std::string tmp;
    std::stringstream ss(options.getOption(Options::ENGINE));
    while (getline(ss, tmp, ',')) {
        if (tmp == SPLIT_TPA) {
            return std::unique_ptr<TPABase>(new TPASplit(logic, options));
        } else if (tmp == TPA) {
            return std::unique_ptr<TPABase>(new TPABasic(logic, options));
        }
    }

    throw std::logic_error("Unexpected situation");
}

VerificationResult TPAEngine::solve(ChcDirectedHyperGraph const & graph) {
    auto pipeline = Transformations::towardsTransitionSystems();
    auto transformationResult = pipeline.transform(std::make_unique<ChcDirectedHyperGraph>(graph));
    auto transformedGraph = std::move(transformationResult.first);
    auto translator = std::move(transformationResult.second);
    if (transformedGraph->isNormalGraph()) {
        auto normalGraph = transformedGraph->toNormalGraph();
        auto res = solve(*normalGraph);
        return options.hasOption(Options::COMPUTE_WITNESS) ? translator->translate(std::move(res)) : std::move(res);
    }
    return VerificationResult(VerificationAnswer::UNKNOWN);
}

VerificationResult TPAEngine::solve(const ChcDirectedGraph & graph) {
    if (isTrivial(graph)) { return solveTrivial(graph); }
    if (isTransitionSystem(graph)) {
        auto ts = toTransitionSystem(graph);
        auto solver = mkSolver();
        auto res = solver->solveTransitionSystem(*ts);
        if (not options.hasOption(Options::COMPUTE_WITNESS)) { return VerificationResult(res); }
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
    } else if (isTransitionSystemDAG(graph)) {
        return solveTransitionSystemGraph(graph);
    }
    return VerificationResult(VerificationAnswer::UNKNOWN);
}

class SolverWrapperSingleUse : public SolverWrapper {
    Logic & logic;
    SMTConfig config;
    sstat lastResult = s_Undef;
    std::unique_ptr<MainSolver> solver;

public:
    SolverWrapperSingleUse(Logic & logic, PTRef transition) : logic(logic) {
        this->transition = transition;
        const char * msg = "ok";
        config.setOption(SMTConfig::o_produce_models, SMTOption(true), msg);
        config.setOption(SMTConfig::o_produce_inter, SMTOption(true), msg);
        config.setSimplifyInterpolant(4);
        config.setLRAInterpolationAlgorithm(itp_lra_alg_decomposing_strong);
    }

    ReachabilityResult checkConsistent(PTRef query) override {
        solver.reset(new MainSolver(logic, config, "Reachability checker"));
        solver->insertFormula(transition);
        solver->insertFormula(query);
        lastResult = solver->check();
        if (lastResult == s_False) {
            return ReachabilityResult::UNREACHABLE;
        } else if (lastResult == s_True) {
            return ReachabilityResult::REACHABLE;
        } else {
            throw std::logic_error("Unexpected solver result in checking reachability!");
        }
    }

    void strengthenTransition(PTRef nTransition) override { transition = logic.mkAnd(transition, nTransition); }

    std::unique_ptr<Model> lastQueryModel() override {
        if (not solver or lastResult != s_True) {
            throw std::logic_error("Invalid call for obtaining a model from solver");
        }
        return solver->getModel();
    }

    PTRef lastQueryTransitionInterpolant() override {
        if (not solver or lastResult != s_False) {
            throw std::logic_error("Invalid call for obtaining an interpolant from solver");
        }
        auto itpContext = solver->getInterpolationContext();
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
    SMTConfig config;
    sstat lastResult = s_Undef;
    std::unique_ptr<MainSolver> solver;

    unsigned allformulasInserted = 0;
    ipartitions_t mask = 0;
    bool pushed = false;

public:
    SolverWrapperIncremental(Logic & logic, PTRef transition) : logic(logic) {
        //        std::cout << "Transition: " << logic.printTerm(transition) << std::endl;
        this->transition = transition;
        const char * msg = "ok";
        config.setOption(SMTConfig::o_produce_models, SMTOption(true), msg);
        config.setOption(SMTConfig::o_produce_inter, SMTOption(true), msg);
        config.setSimplifyInterpolant(4);
        config.setLRAInterpolationAlgorithm(itp_lra_alg_decomposing_strong);
        solver.reset(new MainSolver(logic, config, "incremental reachability checker"));
        solver->insertFormula(transition);
        opensmt::setbit(mask, allformulasInserted++);
    }

    ReachabilityResult checkConsistent(PTRef query) override {
        //        std::cout << "Query: " << logic.printTerm(query) << std::endl;
        assert(not pushed);
        solver->push();
        pushed = true;
        solver->insertFormula(query);
        ++allformulasInserted;
        lastResult = solver->check();
        if (lastResult == s_False) {
            return ReachabilityResult::UNREACHABLE;
        } else if (lastResult == s_True) {
            return ReachabilityResult::REACHABLE;
        } else {
            throw std::logic_error("Unexpected solver result in checking reachability!");
        }
    }

    void strengthenTransition(PTRef nTransition) override {
        assert(not pushed);
        solver->push();
        solver->insertFormula(nTransition);
        opensmt::setbit(mask, allformulasInserted++);
        //        std::cout << "Current number of formulas inserted: " << allformulasInserted << std::endl;
    }

    std::unique_ptr<Model> lastQueryModel() override {
        if (lastResult != s_True or not pushed) {
            throw std::logic_error("Invalid call for obtaining a model from solver");
        }
        auto model = solver->getModel();
        solver->pop();
        pushed = false;
        return model;
    }

    PTRef lastQueryTransitionInterpolant() override {
        if (lastResult != s_False or not pushed) {
            throw std::logic_error("Invalid call for obtaining an interpolant from solver");
        }
        auto itpContext = solver->getInterpolationContext();
        vec<PTRef> itps;
        //        std::cout << "Current mask: "  << mask << std::endl;
        itpContext->getSingleInterpolant(itps, mask);
        assert(itps.size() == 1);
        PTRef itp = itps[0];
        solver->pop();
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
        solver.reset(new MainSolver(logic, config, "incremental reachability checker"));
        PTRef consolidatedTransition = logic.mkAnd(transitionComponents);
        solver->insertFormula(consolidatedTransition);
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

void TPABase::updateQueryStates(PTRef fla) {
    assert(isPureStateFormula(fla));
    this->query = logic.mkAnd(fla, this->query);
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

TPABase::QueryResult TPABase::reachabilityExactOneStep(PTRef from, PTRef to) {
    // TODO: this solver can be persistent and used incrementally
    QueryResult result;
    SMTConfig config;
    const char * msg = "ok";
    config.setOption(SMTConfig::o_produce_models, SMTOption(true), msg);
    MainSolver solver(logic, config, "1-step checker");
    PTRef goal = getNextVersion(to);
    PTRef smtQuery = logic.mkAnd({from, transition, goal});
    solver.insertFormula(smtQuery);
    auto res = solver.check();
    if (res == s_True) {
        { // TODO: refactor this out
            auto nextStateVars = getStateVars(1);
            PTRef refinedGoal = keepOnlyVars(smtQuery, nextStateVars, *solver.getModel());
            result.refinedTarget = getNextVersion(refinedGoal, -1);
            result.steps = 1;
        }
        result.result = ReachabilityResult::REACHABLE;
        return result;
    } else if (res == s_False) {
        result.result = ReachabilityResult::UNREACHABLE;
        return result;
    }
    throw std::logic_error("TPA: Unexpected situation checking reachability");
}

TPABase::QueryResult TPABase::reachabilityExactZeroStep(PTRef from, PTRef to) {
    QueryResult result;
    SMTConfig config;
    const char * msg = "ok";
    config.setOption(SMTConfig::o_produce_models, SMTOption(true), msg);
    MainSolver solver(logic, config, "0-step checker");
    PTRef intersection = logic.mkAnd(from, to);
    solver.insertFormula(intersection);
    auto res = solver.check();
    if (res == s_True) {
        result.result = ReachabilityResult::REACHABLE;
        assert(isPureStateFormula(intersection));
        result.refinedTarget = intersection;
        result.steps = 0;
        return result;
    } else if (res == s_False) {
        result.result = ReachabilityResult::UNREACHABLE;
        return result;
    }
    throw std::logic_error("TPA: Unexpected situation checking reachability");
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
        TRACE(3, "Less-than: Iteration " << ++counter << " on level " << power)
        SMTConfig config;
        const char * msg = "ok";
        //        config.setOption(SMTConfig::o_verbosity, SMTOption(1), msg);
        config.setReduction(1);
        config.setOption(SMTConfig::o_produce_inter, SMTOption(true), msg);
        config.setSimplifyInterpolant(4);
        config.setLRAInterpolationAlgorithm(itp_lra_alg_decomposing_strong);
        MainSolver solver(logic, config, "Less-than reachability checker");
        // Tr^{<n} or (Tr^{<n} concat Tr^{=n})
        PTRef previousLessThanTransition = getLessThanPower(power);
        PTRef translatedExactTransition = getNextVersion(getExactPower(power));
        PTRef currentToNextNextPreviousLessThanTransition = shiftOnlyNextVars(previousLessThanTransition);
        PTRef twoStepTransition = logic.mkOr(currentToNextNextPreviousLessThanTransition,
                                             logic.mkAnd(previousLessThanTransition, translatedExactTransition));
        // TODO: assert from and to are current-state formulas
        solver.insertFormula(twoStepTransition);
        solver.insertFormula(logic.mkAnd(from, goal));
        auto res = solver.check();
        if (res == s_False) {
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
        } else if (res == s_True) {
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
            throw std::logic_error("Accelerated BMC: Unexpected situation checking reachability");
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
    SMTConfig config;
    MainSolver solver(logic, config, "");
    PTRef current = getLessThanPower(power);
    PTRef previous = getLessThanPower(power - 1);
    PTRef previousExact = getExactPower(power - 1);
    //    std::cout << "Previous exact: " << logic.printTerm(previousExact) << std::endl;
    // check that previous or previousExact concatenated with previous implies current
    solver.insertFormula(logic.mkOr(shiftOnlyNextVars(previous), logic.mkAnd(previous, getNextVersion(previousExact))));
    solver.insertFormula(logic.mkNot(shiftOnlyNextVars(current)));
    auto res = solver.check();
    return res == s_False;
}

bool TPASplit::verifyExactPower(unsigned short power) const {
    assert(power >= 1);
    if (power > 1) {
        bool previousRes = verifyExactPower(power - 1);
        if (not previousRes) { return false; }
    }
    SMTConfig config;
    MainSolver solver(logic, config, "");
    PTRef current = getExactPower(power);
    PTRef previous = getExactPower(power - 1);
    //    std::cout << "Exact on level " << power << " : " << logic.printTerm(current) << std::endl;
    //    std::cout << "Exact on level " << power - 1 << " : " << logic.printTerm(previous) << std::endl;
    // check that previous or previousExact concatenated with previous implies current
    solver.insertFormula(logic.mkAnd(previous, getNextVersion(previous)));
    solver.insertFormula(logic.mkNot(shiftOnlyNextVars(current)));
    auto res = solver.check();
    return res == s_False;
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
    SMTConfig config;
    MainSolver solver(logic, config, "Fixed-point checker");
    solver.push();
    auto candidates = topLevelConjuncts(logic, invCandidates);
    if (alignment == SafetyExplanation::FixedPointType::RIGHT) {
        solver.insertFormula(getNextVersion(transition));
    } else {
        if (alignment == SafetyExplanation::FixedPointType::LEFT) { solver.insertFormula(transition); }
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
        solver.insertFormula(logic.mkAnd(invCandidates, logic.mkNot(goal)));
    } else if (alignment == SafetyExplanation::FixedPointType::LEFT) {
        solver.insertFormula(logic.mkAnd(getNextVersion(invCandidates), logic.mkNot(goal)));
    }
    while (solver.check() == s_True) {
        for (int i = candidates.size() - 1; i >= 0; i--) {
            PTRef cand = candidates[i];
            solver.pop();
            solver.push();
            if (alignment == SafetyExplanation::FixedPointType::RIGHT) {
                solver.insertFormula(logic.mkAnd(logic.mkAnd(candidates), logic.mkNot(shiftOnlyNextVars(cand))));
            } else {
                if (alignment == SafetyExplanation::FixedPointType::LEFT) {
                    solver.insertFormula(
                        logic.mkAnd(getNextVersion(logic.mkAnd(candidates)), logic.mkNot(shiftOnlyNextVars(cand))));
                }
            }
            if (solver.check() == s_True) {
                candidates[i] = candidates[candidates.size() - 1];
                candidates.pop();
            }
        }
        solver.pop();
        solver.push();
        goal = shiftOnlyNextVars(logic.mkAnd(candidates));
        if (alignment == SafetyExplanation::FixedPointType::RIGHT) {
            solver.insertFormula(logic.mkAnd(logic.mkAnd(candidates), logic.mkNot(goal)));
        } else {
            solver.insertFormula(logic.mkAnd(getNextVersion(logic.mkAnd(candidates)), logic.mkNot(goal)));
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
        SMTConfig config;
        {
            houdiniCheck(currentLevelTransition, transition, SafetyExplanation::FixedPointType::RIGHT);
            MainSolver solver(logic, config, "Fixed-point checker");
            solver.insertFormula(
                logic.mkAnd({logic.mkAnd(rightInvariants), currentLevelTransition, getNextVersion(transition),
                             logic.mkNot(shiftOnlyNextVars(currentLevelTransition))}));
            auto satres = solver.check();
            bool restrictedInvariant = false;
            if (satres != s_False) {
                solver.push();
                solver.insertFormula(init);
                satres = solver.check();
                if (satres == s_False) { restrictedInvariant = true; }
            }
            if (satres == s_False) {
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
                explanation.fixedPointType = SafetyExplanation::FixedPointType::RIGHT;
                explanation.inductivnessPowerExponent = 0;
                explanation.safeTransitionInvariant = logic.mkAnd(logic.mkAnd(rightInvariants), currentLevelTransition);
                return true;
            }
        }
        // now check if it is fixed point with respect to bad states
        {
            houdiniCheck(currentLevelTransition, transition, SafetyExplanation::FixedPointType::LEFT);
            MainSolver solver(logic, config, "Fixed-point checker");
            solver.insertFormula(logic.mkAnd({transition, getNextVersion(logic.mkAnd(leftInvariants)),
                                              getNextVersion(currentLevelTransition),
                                              logic.mkNot(shiftOnlyNextVars(currentLevelTransition))}));
            auto satres = solver.check();
            bool restrictedInvariant = false;
            if (satres != s_False) {
                solver.push();
                solver.insertFormula(getNextVersion(query, 2));
                satres = solver.check();
                if (satres == s_False) { restrictedInvariant = true; }
            }
            if (satres == s_False) {
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
                explanation.fixedPointType = SafetyExplanation::FixedPointType::LEFT;
                explanation.inductivnessPowerExponent = 0;
                explanation.safeTransitionInvariant = logic.mkAnd(logic.mkAnd(leftInvariants), currentLevelTransition);
                return true;
            }
        }
        // TODO: Move this to a separate method?
        // now check the produced if transition invariants are actually safety invariants
        {
            MainSolver solver(logic, config, "Fixed-point checker");
            solver.insertFormula(logic.mkAnd({init, logic.mkAnd(rightInvariants), getNextVersion(query)}));
            auto satres = solver.check();
            if (satres == s_False) {
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
            MainSolver solver(logic, config, "Fixed-point checker");
            solver.insertFormula(logic.mkAnd({init, logic.mkAnd(leftInvariants), getNextVersion(query)}));
            auto satres = solver.check();
            if (satres == s_False) {
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
        SMTConfig config;
        MainSolver solver(logic, config, "Fixed-point checker");
        solver.insertFormula(logic.mkAnd({currentTwoStep, logic.mkNot(shifted)}));
        sstat satres = solver.check();
        char restrictedInvariant = 0;
        if (satres != s_False) {
            solver.push();
            solver.insertFormula(getNextVersion(logic.mkAnd(init, getLessThanPower(i)), -1));
            satres = solver.check();
            if (satres == s_False) { restrictedInvariant = 1; }
        }
        if (satres != s_False) {
            solver.pop();
            solver.push();
            solver.insertFormula(logic.mkAnd(getNextVersion(getLessThanPower(i), 2), getNextVersion(query, 3)));
            satres = solver.check();
            if (satres == s_False) { restrictedInvariant = 2; }
        }
        if (satres == s_False) {
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

bool TPABase::verifyKinductiveInvariant(PTRef fla, unsigned long k) const {
    constexpr int trace_level = 1;
    TRACE(trace_level, "Verifying k-inductive invariant for k = " << k)

    { // Inductive case:
        SMTConfig config;
        MainSolver solver(logic, config, "k-induction inductive step checker");
        for (unsigned long i = 0; i < k; ++i) {
            solver.insertFormula(getNextVersion(fla, i));
            solver.insertFormula(getNextVersion(transition, i));
        }
        solver.insertFormula(logic.mkNot(getNextVersion(fla, k)));
        auto res = solver.check();
        if (res != s_False) {
            std::cerr << "k-induction verification failed; induction step does not hold!" << std::endl;
            return false;
        }
        TRACE(trace_level, "Inductive case succesfully verified")
    }
    { // Base cases:
        SMTConfig config;
        MainSolver solver(logic, config, "k-induction base checker");
        solver.insertFormula(init);
        for (unsigned long i = 0; i < k; ++i) {
            solver.push();
            solver.insertFormula(logic.mkNot(getNextVersion(fla, i)));
            auto res = solver.check();
            if (res != s_False) {
                std::cerr << "k-induction verification failed; base case " << i << " does not hold!" << std::endl;
                return false;
            }
            TRACE(trace_level, "Base case " << i << " succesfully verified")
            solver.pop();
            solver.push();
            solver.insertFormula(getNextVersion(transition, i));
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
    SMTConfig config;
    MainSolver solver(logic, config, "");
    PTRef current = getLevelTransition(level);
    PTRef previous = getLevelTransition(level - 1);
    solver.insertFormula(logic.mkAnd(previous, getNextVersion(previous)));
    solver.insertFormula(logic.mkNot(shiftOnlyNextVars(current)));
    solver.insertFormula(logic.mkNot(shiftOnlyNextVars(current)));
    auto res = solver.check();
    return res == s_False;
}

PTRef TPABase::safeSupersetOfInitialStates(PTRef start, PTRef transitionInvariant, PTRef target) const {
    SMTConfig config;
    const char * msg = "ok";
    config.setOption(SMTConfig::o_produce_models, SMTOption(false), msg);
    config.setOption(SMTConfig::o_produce_inter, SMTOption(true), msg);
    config.setLRAInterpolationAlgorithm(itp_lra_alg_decomposing_strong);
    config.setSimplifyInterpolant(4);
    MainSolver solver(logic, config, "Unsafe initial states computation");
    solver.insertFormula(start);
    solver.insertFormula(transitionInvariant);
    solver.insertFormula(target);
    auto res = solver.check();
    if (res != s_False) { throw std::logic_error("SMT query was suppose to be unsat, but is not!"); }
    auto itpContext = solver.getInterpolationContext();
    ipartitions_t mask = (1 << 1) + (1 << 2); // This puts transition + query into the A-part
    vec<PTRef> itps;
    itpContext->getSingleInterpolant(itps, mask);
    return logic.mkNot(itps[0]);
}

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
        PTRef trulyReached{PTRef_Undef};
        PTRef trulySafe{PTRef_Undef};
        PTRef accumulatedRestrictions;
        vec<EId> children;
        int blocked_children;
        vec<EId> parents;
    };

    vec<EId> activePath;

    std::unordered_map<SymRef, NetworkNode, SymRefHash> networkMap;

    struct QueryResult {
        ReachabilityResult reachabilityResult;
        PTRef explanation;
    };

    bool reachable(ReachabilityResult res) { return res == ReachabilityResult::REACHABLE; }

    void initNetwork();

    std::unique_ptr<TPABase> mkSolver() const { return owner.mkSolver(); }

    TransitionSystem constructTransitionSystemFor(SymRef vid) const;

    NetworkNode & getNode(SymRef vid) { return networkMap.at(vid); }
    NetworkNode const & getNode(SymRef vid) const { return networkMap.at(vid); }

    vec<SymRef> getGraphStarts() const {
        vec<SymRef> graphStarts;
        for (auto outgoingEdge : adjacencyRepresentation.getOutgoingEdgesFor(graph.getEntry())) {
            graphStarts.push(graph.getTarget(outgoingEdge));
        }
        return graphStarts;
    }

    vec<SymRef> getGraphEnds() const {
        vec<SymRef> graphEnds;
        for (auto incomingEdge : adjacencyRepresentation.getIncomingEdgesFor(graph.getExit())) {
            graphEnds.push(graph.getSource(incomingEdge));
        }
        return graphEnds;
    }

    EId getIncomingEdge(SymRef vid, int id) const { return getNode(vid).parents[id]; }

    const vec<EId> & getIncomingEdges(SymRef vid) const { return getNode(vid).parents; }

    EId getOutgoingEdge(SymRef vid, int id) const { return getNode(vid).children[id]; }

    const vec<EId> & getOutgoingEdges(SymRef vid) const { return getNode(vid).children; }

    PTRef getInitialStates(SymRef vid) const { return networkMap.at(vid).solver->getInit(); }

    PTRef getQueryStates(SymRef vid) const { return networkMap.at(vid).solver->getQuery(); }

    QueryResult queryEdge(EId eid, PTRef sourceCondition, PTRef targetCondition);

    QueryResult queryTransitionSystem(NetworkNode & node);

    InvalidityWitness computeInvalidityWitness() const;

    void addRestrictions(SymRef node, PTRef fla);

    void updateRestrictions(SymRef node);
};

void TransitionSystemNetworkManager::addRestrictions(SymRef node, PTRef fla) {
    getNode(node).accumulatedRestrictions = logic.mkAnd(fla, getNode(node).accumulatedRestrictions);
}

void TransitionSystemNetworkManager::updateRestrictions(SymRef node) {
    getNode(node).solver->updateQueryStates(getNode(node).accumulatedRestrictions);
    getNode(node).accumulatedRestrictions = logic.getTerm_true();
}

VerificationResult TPAEngine::solveTransitionSystemGraph(const ChcDirectedGraph & graph) {
    return TransitionSystemNetworkManager(*this, graph).solve();
}

void TransitionSystemNetworkManager::initNetwork() {
    assert(networkMap.empty());
    for (auto vid : graph.getVertices()) {
        if (vid == graph.getEntry() or vid == graph.getExit()) {
            networkMap.insert({vid, NetworkNode()});
            continue;
        }
        networkMap.insert({vid, NetworkNode()});
        auto & node = networkMap.at(vid);
        node.solver = mkSolver();
        node.blocked_children = 0;
        TransitionSystem ts = constructTransitionSystemFor(vid);
        node.solver->resetTransitionSystem(ts);
        node.trulySafe = logic.getTerm_false();
    }
    TimeMachine tm(logic);
    for (EId eid : adjacencyRepresentation.getOutgoingEdgesFor(graph.getEntry())) {
        auto target = graph.getTarget(eid);
        getNode(target).solver->resetInitialStates(logic.getTerm_true());
    }
    for (EId eid : adjacencyRepresentation.getIncomingEdgesFor(graph.getExit())) {
        auto source = graph.getSource(eid);
        networkMap.at(source).solver->updateQueryStates(logic.getTerm_true());
    }
    // Connect the network
    for (auto vid : reversePostOrder(graph, adjacencyRepresentation)) {
        if (vid != graph.getExit()) {
            auto outGoingEdges = adjacencyRepresentation.getOutgoingEdgesFor(vid);
            outGoingEdges.erase(
                std::remove_if(outGoingEdges.begin(), outGoingEdges.end(),
                               [this](EId eid) { return graph.getSource(eid) == graph.getTarget(eid); }),
                outGoingEdges.end());
            for (auto edge : outGoingEdges) {
                getNode(graph.getTarget(edge)).parents.push(edge);
            }
        }
        if (vid != graph.getEntry()) {
            auto incomingEdges = adjacencyRepresentation.getIncomingEdgesFor(vid);
            incomingEdges.erase(
                std::remove_if(incomingEdges.begin(), incomingEdges.end(),
                               [this](EId eid) { return graph.getSource(eid) == graph.getTarget(eid); }),
                incomingEdges.end());
            for (auto edge : incomingEdges) {
                getNode(graph.getSource(edge)).children.push(edge);
            }
        }
    }
}

VerificationResult TransitionSystemNetworkManager::solve() && {
    initNetwork();
    auto current = graph.getEntry();
    activePath.clear();
    while (true) {
        if (getNode(current).blocked_children == getNode(current).children.size()) {
            if (current == graph.getEntry()) {
                // TODO: Compute witness
                return {VerificationAnswer::SAFE, NoWitness{"Unable to compute witness from TPA for DAG of TSs yet"}};
            }
            getNode(current).trulyReached = PTRef_Undef;
            getNode(current).blocked_children = 0;
            updateRestrictions(current);
        }
        if (current == graph.getEntry()) {
            getNode(current).trulyReached = logic.getTerm_true();
            while (getNode(current).blocked_children < getNode(current).children.size()) {
                EId nextEdge = getOutgoingEdge(current, getNode(current).blocked_children);
                PTRef nextConditions = logic.getTerm_true();
                if (graph.getTarget(nextEdge) != graph.getExit()) {
                    nextConditions = logic.mkNot(getNode(graph.getTarget(nextEdge)).trulySafe);
                }
                auto [edgeRes, edgeExplanation] = queryEdge(nextEdge, logic.getTerm_true(), nextConditions);
                getNode(current).blocked_children++;
                if (reachable(edgeRes)) { // Edge propagates forward
                    if (graph.getTarget(nextEdge) == graph.getExit()) {
                        return {VerificationAnswer::UNSAFE, computeInvalidityWitness()};
                    }
                    auto next = graph.getTarget(nextEdge);
                    networkMap.at(next).solver->resetInitialStates(edgeExplanation);
                    activePath.push(nextEdge);
                    current = next;
                    break; // Information has been propagated to the next node, switch to the new node

                } else { // Edge cannot propagate forward
                    addRestrictions(current, logic.mkNot(edgeExplanation));
                    continue; // Repeat the query for the same TS with stronger query
                }
            }
            continue;
        }
        auto [res, explanation] = queryTransitionSystem(networkMap.at(current));
        if (reachable(res)) {
            getNode(current).trulyReached = explanation;
            while (getNode(current).blocked_children < getNode(current).children.size()) {
                EId nextEdge = getOutgoingEdge(current, getNode(current).blocked_children);
                PTRef nextConditions = logic.getTerm_true();
                if (graph.getTarget(nextEdge) != graph.getExit()) {
                    nextConditions = logic.mkNot(getNode(graph.getTarget(nextEdge)).trulySafe);
                }
                auto [edgeRes, edgeExplanation] = queryEdge(nextEdge, explanation, nextConditions);
                getNode(current).blocked_children++;
                if (reachable(edgeRes)) { // Edge propagates forward
                    if (graph.getTarget(nextEdge) == graph.getExit()) {
                        return {VerificationAnswer::UNSAFE, computeInvalidityWitness()};
                    }
                    auto next = graph.getTarget(nextEdge);
                    networkMap.at(next).solver->resetInitialStates(edgeExplanation);
                    activePath.push(nextEdge);
                    current = next;
                    break; // Information has been propagated to the next node, switch to the new node

                } else { // Edge cannot propagate forward
                    addRestrictions(current, logic.mkNot(edgeExplanation));
                    continue; // Repeat the query for the same TS with stronger query
                }
            }
        } else { // TS cannot propagate forward
            assert(getNode(current).trulySafe != PTRef_Undef);
            getNode(current).trulySafe = logic.mkOr(getNode(current).trulySafe, explanation);
            auto previousEdge = activePath.last();
            auto & previousNode = getNode(graph.getSource(previousEdge));
            assert(previousNode.trulyReached != PTRef_Undef);
            PTRef updatedConditions = logic.mkNot(getNode(current).trulySafe);
            auto [edgeRes, edgeExplanation] = queryEdge(previousEdge, previousNode.trulyReached, updatedConditions);
            if (reachable(edgeRes)) { // New reached, not refuted yet, states
                getNode(current).solver->resetInitialStates(edgeExplanation);
                continue; // Repeat the query for the same TS with new initial states
            } else {      // Cannot continue from currently computed truly reached states
                previousNode.trulyReached = PTRef_Undef;
                addRestrictions(graph.getSource(previousEdge), logic.mkNot(edgeExplanation));
                activePath.pop();
                current = graph.getSource(previousEdge);
                continue; // Blocked states have been propagated to the previous node, repeat the query there.
            }
        }
    }
    throw std::logic_error("Unreachable!");
}

InvalidityWitness TransitionSystemNetworkManager::computeInvalidityWitness() const {
    std::vector<EId> errorPath;
    SymRef current;
    auto graphEnds = getGraphEnds();
    for (int i = 0; i < activePath.size(); i++) {
        EId next = activePath[i];
        errorPath.push_back(next);
        current = graph.getTarget(next);
        auto steps = getNode(current).solver->getTransitionStepCount();
        errorPath.insert(errorPath.end(), steps, getSelfLoopFor(current, graph, adjacencyRepresentation).value());
    }
    for (auto node : getNode(current).children) {
        if (graph.getTarget(node) == graph.getExit()) { errorPath.push_back(node); }
    }
    InvalidityWitness witness;
    ErrorPath path(std::move(errorPath));
    return InvalidityWitness::fromErrorPath(path, graph);
}

TransitionSystem TransitionSystemNetworkManager::constructTransitionSystemFor(SymRef vid) const {
    EId loopEdge = getSelfLoopFor(vid, graph, adjacencyRepresentation).value();
    auto edgeVars = getVariablesFromEdge(logic, graph, loopEdge);
    auto systemType = std::make_unique<SystemType>(edgeVars.stateVars, edgeVars.auxiliaryVars, logic);
    PTRef loopLabel = graph.getEdgeLabel(loopEdge);
    PTRef transitionFla = transitionFormulaInSystemType(*systemType, edgeVars, loopLabel, logic);
    return TransitionSystem(logic, std::move(systemType), logic.getTerm_true(), transitionFla, logic.getTerm_true());
}

TransitionSystemNetworkManager::QueryResult TransitionSystemNetworkManager::queryEdge(EId eid, PTRef sourceCondition,
                                                                                      PTRef targetCondition) {
    SMTConfig config;
    const char * msg = "ok";
    config.setOption(SMTConfig::o_produce_models, SMTOption(true), msg);
    config.setOption(SMTConfig::o_produce_inter, SMTOption(true), msg);
    config.setLRAInterpolationAlgorithm(itp_lra_alg_decomposing_strong);
    config.setSimplifyInterpolant(4);
    MainSolver solver(logic, config, "Edge query solver");
    PTRef label = graph.getEdgeLabel(eid);
    TRACE(1, "Querying edge " << eid.id << " with label " << logic.pp(label) << "\n\tsource is "
                              << logic.pp(sourceCondition) << "\n\ttarget is " << logic.pp(targetCondition))
    PTRef target = TimeMachine(logic).sendFlaThroughTime(targetCondition, 1);
    solver.insertFormula(sourceCondition);
    solver.insertFormula(label);
    solver.insertFormula(target);
    auto res = solver.check();
    if (res == s_True) {
        auto model = solver.getModel();
        ModelBasedProjection mbp(logic);
        PTRef query = logic.mkAnd({sourceCondition, label, target});
        auto targetVars = TermUtils(logic).predicateArgsInOrder(graph.getNextStateVersion(graph.getTarget(eid)));
        PTRef eliminated = mbp.keepOnly(query, targetVars, *model);
        eliminated = TimeMachine(logic).sendFlaThroughTime(eliminated, -1);
        TRACE(1, "Propagating along the edge " << logic.pp(eliminated))
        return {ReachabilityResult::REACHABLE, eliminated};
    } else if (res == s_False) {
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

TransitionSystemNetworkManager::QueryResult TransitionSystemNetworkManager::queryTransitionSystem(NetworkNode & node) {
    auto res = node.solver->solve();
    assert(res != VerificationAnswer::UNKNOWN);
    switch (res) {
        case VerificationAnswer::UNSAFE: {
            PTRef explanation = node.solver->getReachedStates();
            assert(explanation != PTRef_Undef);
            TRACE(1, "TS propagates reachable states to " << logic.pp(explanation))
            return {ReachabilityResult::REACHABLE, explanation};
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
                    logic.mkAnd({transitionInvariant, getNextVersion(query)}), getStateVars(0)));
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