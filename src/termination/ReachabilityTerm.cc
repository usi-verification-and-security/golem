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
    auto solver = std::make_unique<TPASplit>(logic, options);
    solver->resetTransitionSystem(*ts);
    if (std::stoi(options.getOrDefault(Options::VERBOSE, "0")) > 0) { std::cout << "; Searching for nontermination!\n"; }
    auto res = solver->solve();
    while(res == VerificationAnswer::UNSAFE) {
        PTRef init  = solver->getInit();
        PTRef reached  = solver->getReachedStates();
        PTRef transition = solver->getTransitionRelation();
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
        for (int j = num; j > 0; j--) {
            vec<PTRef> toEliminate = solver->getStateVars(j);
            transitions = ModelBasedProjection(logic).project(transitions, toEliminate, *model);
        }
        solver->resetInitialStates(logic.mkAnd(init, logic.mkNot(transitions)));
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
