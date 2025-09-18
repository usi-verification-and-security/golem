/*
 * Copyright (c) 2025, Konstantin Britikov <konstantin.britikov@usi.ch>
 *
 * SPDX-License-Identifier: MIT
 */

#include "ReachabilityTerm.h"

#include "ChcSystem.h"
#include "TermUtils.h"
#include "engine/EngineFactory.h"
#include "engine/TPA.h"
#include "engine/Common.h"
#include "TransformationUtils.h"
#include "transformers/SingleLoopTransformation.h"
#include "ModelBasedProjection.h"
#include "QuantifierElimination.h"

namespace golem::termination {

    PTRef eliminateVars(PTRef fla, const vec<PTRef> & vars, Model & model, bool useQE, Logic logic) {
        if (useQE) {
            return QuantifierElimination(logic).eliminate(fla, vars);
        } else {
            return ModelBasedProjection(logic).project(fla, vars, model);
        }
    }

ReachabilityTerm::Answer ReachabilityTerm::nontermination(ChcDirectedHyperGraph const & system) {
    ArithLogic & logic = dynamic_cast<ArithLogic &>(system.getLogic());
    TermUtils utils {logic};

    assert(system.isNormalGraph());
    auto graph = system.toNormalGraph();
    if (isTrivial(*graph)) {
        auto res = solveTrivial(*graph);
        switch (res.getAnswer()) {
            case VerificationAnswer::SAFE:
                return Answer::NO;
            case VerificationAnswer::UNKNOWN:
                return Answer::UNKNOWN;
            case VerificationAnswer::UNSAFE:
                return Answer::UNKNOWN;
        }
    }
    auto ts = [&]() -> std::unique_ptr<TransitionSystem> {
        if (isTransitionSystem(*graph)) { return toTransitionSystem(*graph, false); }
        auto [ts, bt] = SingleLoopTransformation{}.transform(*graph);
        return std::move(ts);
    }();
    // auto engine = EngineFactory(logic, options).getEngine(options.getOrDefault(Options::ENGINE, "spacer"));
    //     engine->solve();
    auto solver = std::make_unique<TPASplit>(logic, options);
    solver->resetTransitionSystem(*ts);
    PTRef init  = solver->getInit();
    PTRef transition = solver -> getTransitionRelation();
    PTRef query = solver -> getQuery();
    // auto vars = solver -> getStateVars(0);
    auto next_vars = solver -> getStateVars(1);
    auto disjuncts = utils.getTopLevelDisjuncts(transition);
    bool nondet = false;
    std::unordered_set<PTRef, PTRefHash> nondet_juncts;
    for (auto & junct : disjuncts) {
        auto junct_vars = utils.getVars(junct);
        for (auto & var : next_vars) {
            if (std::find(junct_vars.begin(), junct_vars.end(), var) == junct_vars.end()) {
                nondet = true;
                nondet_juncts.insert(junct);
                break;
            }
        }
    }
    PTRef transitionConstraint = logic.getTerm_true();
    PTRef initConstraint = logic.getTerm_true();

    if (std::stoi(options.getOrDefault(Options::VERBOSE, "0")) > 0) { std::cout << "; Searching for nontermination!\n"; }
    auto res = solver->solve();
    while(res == VerificationAnswer::UNSAFE) {
        PTRef reached  = solver->getReachedStates();
        uint num = solver->getTransitionStepCount();
        std::vector formulas {init, TimeMachine(logic).sendFlaThroughTime(reached, num)};
        SMTSolver SMTsolver(logic, SMTSolver::WitnessProduction::ONLY_MODEL);
        for(int j=0; j < num; j++){
            formulas.push_back(TimeMachine(logic).sendFlaThroughTime(transition, j));
        }
        PTRef transitions = logic.mkAnd(formulas);
        SMTsolver.assertProp(transitions);
        auto resSMT = SMTsolver.check();
        assert(resSMT == SMTSolver::Answer::SAT);
        auto model = SMTsolver.getModel();
        bool detected = false;
        for (int j = num; j > 0; j--) {
            for (auto & disjunct : disjuncts) {
                SMTSolver smt_solver(logic, SMTSolver::WitnessProduction::NONE);
                smt_solver.assertProp(model->evaluate(TimeMachine(logic).sendFlaThroughTime(disjunct, j-1)));
                if (smt_solver.check() == SMTSolver::Answer::SAT) {
                    if (nondet_juncts.contains(disjunct)) {
                        transitions = TimeMachine(logic).sendFlaThroughTime(QuantifierElimination(logic).keepOnly(transitions, solver->getStateVars(j)), -j+1);
                        detected = true;
                    }
                    break;
                }
            }
            if (detected) { break; }
            // vec<PTRef> toEliminate = solver->getStateVars(j);
            // transitions = ModelBasedProjection(logic).project(transitions, toEliminate, *model);

        }
        if (detected) {
            transitionConstraint = logic.mkAnd(transitionConstraint, logic.mkNot(transitions));
            solver->resetTransitionSystem(TransitionSystem(logic,
                std::make_unique<SystemType>(ts->getStateVars(), ts->getAuxiliaryVars(), logic),
                logic.mkAnd(init, initConstraint),
                    logic.mkAnd(transition, transitionConstraint),
                    query));
        } else {
            transitions = QuantifierElimination(logic).keepOnly(transitions, solver->getStateVars(0));
            initConstraint = logic.mkAnd(initConstraint, logic.mkNot(transitions));
            solver->resetInitialStates(logic.mkAnd(init, initConstraint));
        }
        res = solver->solve();
    }
    SMTSolver SMTsolver(logic, SMTSolver::WitnessProduction::NONE);
    SMTsolver.resetSolver();
    SMTsolver.assertProp(logic.mkAnd(solver->getInit(), solver->getTransitionRelation()));
    auto resSMT = SMTsolver.check();
    if (resSMT == SMTSolver::Answer::UNSAT) {
        return Answer::YES;
    }

    switch (res) {
        case VerificationAnswer::SAFE:
            return Answer::NO;
        case VerificationAnswer::UNKNOWN:
            return Answer::UNKNOWN;
    }
    assert(false && "Unreachable!");
    return Answer::ERROR;
}

} // namespace golem::termination
