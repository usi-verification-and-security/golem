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
    PTRef dnfize(PTRef input, Logic & logic) {
        TermUtils utils {logic};
        if (logic.isAnd(input)) {
            auto juncts = utils.getTopLevelConjuncts(input);

            for (int i = 0; i < (int)juncts.size(); i++) {
                PTRef after_junct = dnfize(juncts[i], logic);
                if (logic.isOr(after_junct)) {
                    auto subjuncts = utils.getTopLevelDisjuncts(after_junct);
                    vec<PTRef> postprocessJuncts;
                    juncts[i] = juncts.last();
                    juncts.pop();
                    for (auto subjunct: subjuncts) {
                        postprocessJuncts.push(logic.mkAnd(logic.mkAnd(juncts), subjunct));
                    }
                    return dnfize(logic.mkOr(postprocessJuncts), logic);
                }
            }
        } else if (logic.isOr(input)) {
            auto juncts = utils.getTopLevelDisjuncts(input);
            vec<PTRef> postprocessJuncts;
            for (int i = 0; i < (int)juncts.size(); i++) {
                PTRef after_junct = dnfize(juncts[i], logic);
                if (logic.isOr(after_junct)) {
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
                vec<PTRef> postprocessJuncts;
                for (int i = 0; i < (int)subjuncts.size(); i++) {
                    postprocessJuncts.push(logic.mkNot(subjuncts[i]));
                }
                return dnfize(logic.mkOr(postprocessJuncts), logic);
            } else if (logic.isOr(rev)) {
                auto subjuncts = utils.getTopLevelDisjuncts(input);
                vec<PTRef> postprocessJuncts;
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
    PTRef init  = ts->getInit();
    std::cout<<"Transition pre-dnfize: " << logic.pp(ts->getTransition()) << std::endl;
    PTRef transition = dnfize(ts->getTransition(),logic);
    PTRef query = ts->getQuery();
    solver->resetTransitionSystem(TransitionSystem(logic,
                    std::make_unique<SystemType>(ts->getStateVars(), ts->getAuxiliaryVars(), logic),
                    init,
                        transition,
                        query));
    std::cout<<"Init: " << logic.pp(init) << std::endl;
    std::cout<<"Transition: " << logic.pp(transition) << std::endl;
    std::cout<<"Query: " << logic.pp(query) << std::endl;
    auto vars = solver -> getStateVars(0);
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
            uint k = 0;
            PTRef base = logic.getTerm_true();
            for (auto var: vars) {
                PTRef ver = TimeMachine(logic).sendFlaThroughTime(var, j-1);
                base = logic.mkAnd(base, logic.mkEq(ver, model->evaluate(ver)));
            }
            // PTRef base = model->evaluate(TimeMachine(logic).sendFlaThroughTime(transition, j-1));
            for (auto & disjunct : disjuncts) {
                SMTsolver.resetSolver();
                std::cout<<"Base: " << logic.pp(base) << std::endl;
                SMTsolver.assertProp(logic.mkAnd(base, TimeMachine(logic).sendFlaThroughTime(disjunct,j-1)));
            // uint k = 0;
            // for (auto & disjunct : disjuncts) {
            //     SMTSolver smt_solver(logic, SMTSolver::WitnessProduction::NONE);
            //     std::cout<<"Junct: " << logic.pp(disjunct) << std::endl;
            //     smt_solver.assertProp(model->evaluate(TimeMachine(logic).sendFlaThroughTime(disjunct, j-1)));
                // Example, what is the solution
                // Why it is hard
                // how it is solved in my approach (invariants, auxiliary properties, trace analysis)
                // Idea is to make it interesting
                if (SMTsolver.check() == SMTSolver::Answer::SAT) {
                    k+=1;
                    if (nondet_juncts.contains(disjunct) || k == 2) {
                        auto preVars = solver->getStateVars(j);
                        transitions = TimeMachine(logic).sendFlaThroughTime(QuantifierElimination(logic).keepOnly(transitions, preVars), -j+1);
                        // std::cout<<"Block: " << logic.pp(transitions) << std::endl;
                        SMTsolver.resetSolver();
                        SMTsolver.assertProp(logic.mkAnd(logic.mkNot(transitions), disjunct));
                        if (SMTsolver.check() == SMTSolver::Answer::UNSAT) {
                            nondet_juncts.erase(disjunct);
                        };
                        detected = true;
                        break;
                    }
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
        // Give linear templates of vars, and check them for preconds to cover benchmarks...
    SMTSolver SMTsolver(logic, SMTSolver::WitnessProduction::NONE);
    SMTsolver.resetSolver();
    SMTsolver.assertProp(logic.mkAnd({solver->getInit(), solver->getTransitionRelation(), transitionConstraint}));
    auto resSMT = SMTsolver.check();
    if (resSMT == SMTSolver::Answer::UNSAT) {
        return Answer::YES;
    }

    switch (res) {
        case VerificationAnswer::SAFE: {
            PTRef inv = solver->getInductiveInvariant();
            SMTsolver.resetSolver();
            SMTsolver.assertProp(logic.mkAnd({inv, logic.mkAnd(transition, transitionConstraint), logic.mkNot(TimeMachine(logic).sendFlaThroughTime(inv, 1))}));
            auto ans_1 = SMTsolver.check();
            SMTsolver.resetSolver();
            SMTsolver.assertProp(logic.mkAnd(inv, logic.mkNot(QuantifierElimination(logic).keepOnly(logic.mkAnd(transition, transitionConstraint), solver->getStateVars(0)))));
            auto ans_2 = SMTsolver.check();

            std::cout<<"Invariant: " << logic.pp(inv) << std::endl;
            std::cout<<"Transition: " << logic.pp(transition) << std::endl;
            std::cout<<"Transition Constraint: " << logic.pp(transitionConstraint) << std::endl;
            std::cout<<"Comp: " << logic.pp(QuantifierElimination(logic).keepOnly(logic.mkAnd(transition, transitionConstraint), solver->getStateVars(0))) << std::endl;
            if (ans_1== SMTSolver::Answer::UNSAT && ans_2 == SMTSolver::Answer::UNSAT) {
                return Answer::NO;
            }
            // else {
            //     SMTsolver.resetSolver();
            //     SMTsolver.assertProp(logic.mkAnd(transition, transitionConstraint));
            //     if (SMTsolver.check() == SMTSolver::Answer::UNSAT) {
            //         return Answer::YES;
            //     }
            //     return Answer::UNKNOWN;
            // }
        }
        case VerificationAnswer::UNKNOWN:
            return Answer::UNKNOWN;
        case VerificationAnswer::UNSAFE:
            return Answer::ERROR;
    }
    // assert(false && "Unreachable!");
    // return Answer::ERROR;
}

} // namespace golem::termination
