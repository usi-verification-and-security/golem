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

    // TODO: think what to do with negation
    PTRef  dnfize(PTRef input, Logic & logic) {
        TermUtils utils {logic};
        if (logic.isAnd(input)) {
            auto juncts = utils.getTopLevelConjuncts(input);

            for (int i = 0; i < (int)juncts.size(); i++) {
                PTRef after_junct = dnfize(juncts[0], logic);
                if (logic.isOr(after_junct)) {
                    auto subjuncts = utils.getTopLevelDisjuncts(after_junct);
                    vec<PTRef> postprocessJuncts(subjuncts.size());
                    juncts[i] = juncts.last();
                    juncts.pop();
                    for (auto subjunct: subjuncts) {
                        postprocessJuncts.push(logic.mkAnd(logic.mkAnd(juncts), subjunct));
                    }
                    return dnfize(logic.mkOr(postprocessJuncts), logic);
                }
                i++;
            }
        } else if (logic.isOr(input)) {
            auto juncts = utils.getTopLevelDisjuncts(input);
            vec<PTRef> postprocessJuncts(juncts.size());

            for (int i = 0; i < (int)juncts.size(); i++) {
                PTRef after_junct = dnfize(juncts[i], logic);
                if (logic.isOr(after_junct)) {
                    postprocessJuncts[i] = juncts.last();
                    postprocessJuncts.pop();
                    auto subjuncts = utils.getTopLevelDisjuncts(after_junct);
                    for (auto subjunct: subjuncts) {
                        postprocessJuncts.push(subjunct);
                    }
                } else {
                    postprocessJuncts.push(after_junct);
                }
            }
            return logic.mkOr(postprocessJuncts);
        } else if (logic.isNot(input)) {
            PTRef rev = logic.mkNot(input);
            if (logic.isAnd(rev)) {
                auto subjuncts = utils.getTopLevelConjuncts(rev);
                vec<PTRef> postprocessJuncts(subjuncts.size());
                for (int i = 0; i < (int)subjuncts.size(); i++) {
                    postprocessJuncts.push(logic.mkNot(subjuncts[i]));
                }
                return dnfize(logic.mkOr(postprocessJuncts), logic);
            } else if (logic.isOr(rev)) {
                auto subjuncts = utils.getTopLevelDisjuncts(input);
                vec<PTRef> postprocessJuncts(subjuncts.size());
                for (int i = 0; i < (int)subjuncts.size(); i++) {
                    postprocessJuncts.push(logic.mkNot(subjuncts[i]));
                }
                return dnfize(logic.mkAnd(postprocessJuncts), logic);
            }
        }
        return input;
    }

ReachabilityTerm::Answer ReachabilityTerm::nontermination(ChcDirectedGraph const & graph) {
    ArithLogic & logic = dynamic_cast<ArithLogic &>(graph.getLogic());
    TermUtils utils {logic};

    if (isTrivial(graph)) {
        return Answer::YES;
    }
    auto ts = [&]() -> std::unique_ptr<TransitionSystem> {
        if (isTransitionSystem(graph)) { return toTransitionSystem(graph, false); }
        auto [ts, bt] = SingleLoopTransformation{}.transform(graph);
        return std::move(ts);
    }();
    auto engine = EngineFactory(logic, options).getEngine(options.getOrDefault(Options::ENGINE, "spacer"));
    // engine->solve();
    auto solver = std::make_unique<TPASplit>(logic, options);
    solver->resetTransitionSystem(*ts);
    PTRef init  = solver->getInit();
    PTRef transition = solver -> getTransitionRelation();
    PTRef query = solver -> getQuery();
    std::cout<<"Init: " << logic.pp(init) << std::endl;
    std::cout<<"Transition: " << logic.pp(transition) << std::endl;
    std::cout<<"Query: " << logic.pp(query) << std::endl;
    // auto vars = solver -> getStateVars(0);
    auto next_vars = solver -> getStateVars(1);
    auto disjuncts = utils.getTopLevelDisjuncts(transition);
    std::unordered_set<PTRef, PTRefHash> nondet_juncts;
    for (auto & junct : disjuncts) {
        auto junct_vars = utils.getVars(junct);
        for (auto & var : next_vars) {
            if (std::find(junct_vars.begin(), junct_vars.end(), var) == junct_vars.end()) {
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
                uint k = 0;
                SMTSolver smt_solver(logic, SMTSolver::WitnessProduction::NONE);
                std::cout<<"Junct: " << logic.pp(disjunct) << std::endl;
                smt_solver.assertProp(model->evaluate(TimeMachine(logic).sendFlaThroughTime(disjunct, j-1)));
                if (smt_solver.check() == SMTSolver::Answer::SAT) {
                    k+=1;
                    if (nondet_juncts.contains(disjunct) || k == 2) {
                        auto preVars = solver->getStateVars(j);
                        transitions = TimeMachine(logic).sendFlaThroughTime(QuantifierElimination(logic).keepOnly(transitions, preVars), -j+1);
                        std::cout<<"Block: " << logic.pp(transitions) << std::endl;
                        smt_solver.resetSolver();
                        smt_solver.assertProp(logic.mkAnd(logic.mkNot(transitions), disjunct));
                        if (smt_solver.check() == SMTSolver::Answer::UNSAT) {
                            nondet_juncts.erase(disjunct);
                        };
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
            solver = std::make_unique<TPASplit>(logic, options);
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
    SMTsolver.assertProp(logic.mkAnd({solver->getInit(), solver->getTransitionRelation(), transitionConstraint}));
    auto resSMT = SMTsolver.check();
    if (resSMT == SMTSolver::Answer::UNSAT) {
        return Answer::YES;
    }

    switch (res) {
        case VerificationAnswer::SAFE:
            return Answer::NO;
        case VerificationAnswer::UNKNOWN:
            return Answer::UNKNOWN;
        case VerificationAnswer::UNSAFE:
            return Answer::ERROR;
    }
    // assert(false && "Unreachable!");
    // return Answer::ERROR;
}

} // namespace golem::termination
