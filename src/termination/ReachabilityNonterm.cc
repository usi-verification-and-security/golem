/*
 * Copyright (c) 2025, Konstantin Britikov <konstantin.britikov@usi.ch>
 *
 * SPDX-License-Identifier: MIT
 */

#include "ReachabilityNonterm.h"

#include "ChcSystem.h"
#include "TermUtils.h"
#include "engine/EngineFactory.h"
#include "engine/TPA.h"
#include "engine/Common.h"
#include "TransformationUtils.h"
#include "ModelBasedProjection.h"
#include "QuantifierElimination.h"
#include "utils/SmtSolver.h"

namespace golem::termination {

    // TODO: think what to do with negation
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

ReachabilityNonterm::Answer ReachabilityNonterm::nontermination(TransitionSystem const & ts) {

    ArithLogic & logic = dynamic_cast<ArithLogic &>(ts.getLogic());
    auto solver = std::make_unique<TPASplit>(logic, options);
    PTRef init  = ts.getInit();
    PTRef transition = dnfize(ts.getTransition(),logic);
    PTRef query = logic.mkNot(QuantifierElimination(logic).keepOnly(transition, ts.getStateVars()));
    solver->resetTransitionSystem(TransitionSystem(logic,
                    std::make_unique<SystemType>(ts.getStateVars(), ts.getAuxiliaryVars(), logic),
                    init,
                        transition,
                        query));
    std::cout<<"Init: " << logic.pp(init) << std::endl;
    std::cout<<"Transition: " << logic.pp(transition) << std::endl;
    std::cout<<"Query: " << logic.pp(query) << std::endl;
    if (query == logic.getTerm_false()) {
        std::cout<<"; (Trivial nontermination)" << std::endl;
        return Answer::NO;
    }
    auto vars = solver -> getStateVars(0);
    PTRef transitionConstraint = logic.getTerm_true();
    PTRef initConstraint = logic.getTerm_true();

    auto res = solver->solve();
    while(res == VerificationAnswer::UNSAFE) {
        PTRef reached  = solver->getReachedStates();
        PTRef solverTransition = solver->getTransitionRelation();
        uint num = solver->getTransitionStepCount();
        std::vector formulas {init, TimeMachine(logic).sendFlaThroughTime(logic.mkAnd(reached,query), num)};
        SMTSolver SMTsolver(logic, SMTSolver::WitnessProduction::ONLY_MODEL);
        for(int j=0; j < num; j++){
            formulas.push_back(TimeMachine(logic).sendFlaThroughTime(solverTransition, j));
        }
        PTRef transitions = logic.mkAnd(formulas);
        SMTsolver.assertProp(transitions);
        auto resSMT = SMTsolver.check();
        assert(resSMT == SMTSolver::Answer::SAT);
        auto model = SMTsolver.getModel();
        bool detected = false;
        for (int j = num; j > 0; j--) {
            vec<PTRef> base;
            vec<PTRef> results;
            for (auto var: vars) {
                PTRef ver = TimeMachine(logic).sendFlaThroughTime(var, j-1);
                PTRef nxt = TimeMachine(logic).sendFlaThroughTime(var, j);
                base.push(logic.mkEq(ver, model->evaluate(ver)));
                results.push(logic.mkEq(nxt, model->evaluate(nxt)));
            }
            vec<PTRef> nondet_vars;
            vec<PTRef> det_vars;
            uint i = 0;
            SMTsolver.resetSolver();
            SMTsolver.assertProp(logic.mkAnd(logic.mkAnd(base), TimeMachine(logic).sendFlaThroughTime(solverTransition,j-1)));
            std::cout<<"***********CHECK*************\n";
            std::cout<<"Base: " << logic.pp(logic.mkAnd(base)) << std::endl;
            std::cout<<"Result: " << logic.pp(logic.mkAnd(results)) << std::endl;
            std::cout<<"Check: " << logic.pp(TimeMachine(logic).sendFlaThroughTime(solverTransition,j-1)) << std::endl;
            std::cout<<"*****************************\n";
            for(auto result:results) {
                SMTsolver.push();
                SMTsolver.assertProp(logic.mkNot(result));
                if (SMTsolver.check() == SMTSolver::Answer::SAT) {
                    detected = true;
                    nondet_vars.push(TimeMachine(logic).sendFlaThroughTime(vars[i],j));
                } else {
                    det_vars.push(results[i]);
                }
                i++;
                SMTsolver.pop();
            }
            SMTsolver.resetSolver();
            if (detected) {
                PTRef block = TimeMachine(logic).sendFlaThroughTime(QuantifierElimination(logic).keepOnly(logic.mkAnd(logic.mkAnd(det_vars), transitions), nondet_vars), -j+1);
                std::cout<<"Block: " << logic.pp(block) << std::endl;
                if (block == logic.getTerm_true()) {
                    detected = false;
                    SMTsolver.resetSolver();
                    continue;
                } else {
                    SMTsolver.resetSolver();
                    SMTsolver.assertProp(logic.mkAnd(transition, logic.mkAnd(transitionConstraint, logic.mkNot(block))));
                    if (SMTsolver.check() == SMTSolver::Answer::UNSAT) {
                        detected = false;
                        SMTsolver.resetSolver();
                        continue;
                    } else {
                        transitionConstraint = logic.mkAnd(transitionConstraint, logic.mkNot(block));
                    }
                }
            }
            if (detected) { break; }
        }
        if (detected) {
            solver = std::make_unique<TPASplit>(logic, options);
            solver->resetTransitionSystem(TransitionSystem(logic,
                std::make_unique<SystemType>(ts.getStateVars(), ts.getAuxiliaryVars(), logic),
                    logic.mkAnd(init, initConstraint),
                logic.mkAnd(transition, transitionConstraint),
                     query));
        } else {
            transitions = QuantifierElimination(logic).keepOnly(transitions, vars);
            initConstraint = logic.mkAnd(initConstraint, logic.mkNot(transitions));
            std::cout<<"Init block: " << logic.pp(initConstraint) << std::endl;
            solver->resetInitialStates(logic.mkAnd(init, initConstraint));
        }
        res = solver->solve();
    }
        // Give linear templates of vars, and check them for preconds to cover benchmarks...
    SMTSolver SMTsolver(logic, SMTSolver::WitnessProduction::NONE);
    SMTsolver.resetSolver();

    std::cout<<"Transition block: " << logic.pp(transitionConstraint) << std::endl;
    std::cout<<"Init: " << logic.pp(solver->getInit()) << std::endl;
    SMTsolver.assertProp(logic.mkAnd({solver->getInit(), solver->getTransitionRelation()}));
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
            SMTsolver.assertProp(logic.mkAnd({inv, logic.mkAnd(transition, transitionConstraint), logic.mkOr(TimeMachine(logic).sendFlaThroughTime(
                query, 1), logic.mkNot(transitionConstraint))}));
            auto ans_2 = SMTsolver.check();

            // std::cout<<"Invariant: " << logic.pp(inv) << std::endl;
            // std::cout<<"Transition: " << logic.pp(transition) << std::endl;
            // std::cout<<"Transition Constraint: " << logic.pp(transitionConstraint) << std::endl;
            // std::cout<<"Comp: " << logic.pp(QuantifierElimination(logic).keepOnly(logic.mkAnd(transition, transitionConstraint), solver->getStateVars(0))) << std::endl;
            if (ans_1 == SMTSolver::Answer::UNSAT && ans_2 == SMTSolver::Answer::UNSAT) {
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
