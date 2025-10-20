/*
 * Copyright (c) 2025, Konstantin Britikov <konstantin.britikov@usi.ch>
 *
 * SPDX-License-Identifier: MIT
 */

#include "ReachabilityNonterm.h"

#include "ChcSystem.h"
#include "TermUtils.h"
#include "engine/TPA.h"
#include "engine/Common.h"
#include "TransformationUtils.h"
#include "ModelBasedProjection.h"
#include "QuantifierElimination.h"
#include "itehandler/IteToSwitch.h"
#include "utils/SmtSolver.h"
#include <queue>

#include "common/numbers/NumberUtils.h"
#include "engine/EngineFactory.h"
#include "graph/ChcGraphBuilder.h"

namespace golem::termination {

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

    PTRef generateReachabilityQuery(ArithLogic &logic, PTRef query, std::vector<PTRef>& vars) {
        enum TypeOfQuery {LT, GT, LTC, GTC, EQ, NEQ};
        PTRef constr;
        SMTSolver solver(logic, SMTSolver::WitnessProduction::ONLY_MODEL);
        do {
            int j = rand() % vars.size(),k = rand() % vars.size();
            while (!logic.isNumVar(vars[j])) { j = rand() % vars.size(); }
            while (!logic.isNumVar(vars[k])) { k = rand() % vars.size(); }
            int i = rand() % 6;
            switch (i) {
                case LT: {
                    if (logic.isNumVar(vars[j]) && logic.isNumVar(vars[k])) {
                        constr = logic.mkLt(vars[j], vars[k]);
                    }
                }
                case GT: {
                    if (logic.isNumVar(vars[j]) && logic.isNumVar(vars[k])) {
                        constr = logic.mkGt(vars[j], vars[k]);
                    }
                }
                case LTC: {
                    if (logic.isNumVar(vars[j]) ) {
                        constr = logic.mkLt(vars[j], logic.mkIntConst(rand()));
                    }
                }
                case GTC: {
                    if (logic.isNumVar(vars[j]) ) {
                        constr = logic.mkGt(vars[j], logic.mkIntConst(rand()));
                    }
                }
                case EQ: {
                    if (logic.isNumVar(vars[j]) && logic.isNumVar(vars[k])) {
                        constr = logic.mkEq(vars[j], vars[k]);
                    }
                }
                case NEQ: {
                    if (logic.isNumVar(vars[j]) && logic.isNumVar(vars[k])) {
                        constr = logic.mkNot(logic.mkEq(vars[j], vars[k]));
                    }
                }
            }
            solver.resetSolver();
            solver.assertProp(logic.mkAnd(query, constr));
        } while (solver.check() == SMTSolver::Answer::UNSAT);
        return constr;
    }

    bool checkDisjunctiveWellfoundness (Logic &logic, PTRef relation, std::vector<PTRef>& vars) {
        TermUtils utils {logic};
        TimeMachine machine {logic};
        std::vector<PTRef> identity;
        // auto disjuncts = utils.getTopLevelDisjuncts(dnfize(relation, logic));
        vec<PTRef> primedVars;
        for (auto var: vars) {
            identity.push_back(logic.mkEq(var, machine.sendVarThroughTime(var, 1)));
            primedVars.push(machine.sendVarThroughTime(var, 1));
        }
        TermUtils::substitutions_map varSubstitutions;
        for (uint32_t i = 0u; i < vars.size(); ++i) {
            varSubstitutions.insert({ primedVars[i], vars[i]});
        }
        PTRef inv = logic.mkAnd(logic.mkNot(logic.mkAnd(identity)), relation);
        PTRef irreflexiveCheck = utils.varSubstitute(inv, varSubstitutions);
        SMTSolver SMTsolver(logic, SMTSolver::WitnessProduction::ONLY_MODEL);
        SMTsolver.assertProp(irreflexiveCheck);
        assert (SMTsolver.check() != SMTSolver::Answer::SAT);
        varSubstitutions.clear();
        for (uint32_t i = 0u; i < vars.size(); ++i) {
            varSubstitutions.insert({ primedVars[i], machine.sendVarThroughTime(primedVars[i], 1)});
        }
        PTRef transitionBack = utils.varSubstitute(inv, varSubstitutions);
        varSubstitutions.clear();
        for (uint32_t i = 0u; i < vars.size(); ++i) {
            varSubstitutions.insert({ vars[i], primedVars[i]});
            varSubstitutions.insert({ machine.sendVarThroughTime(primedVars[i], 1), vars[i]});
        }
        transitionBack = utils.varSubstitute(transitionBack, varSubstitutions);
        PTRef totalOrder = logic.mkAnd(inv, transitionBack);
        SMTsolver.resetSolver();
        SMTsolver.assertProp(totalOrder);
        if (SMTsolver.check() == SMTSolver::Answer::SAT) {
            return false;
        } else {
            return true;
        }
        // TODO: disjunctive well-foundness
    }

    // bool checkWellFoundness (Logic logic, PTRef relation, vec<PTRef>& vars) {
    //     PTRef constraints = QuantifierElimination(logic).keepOnly(relation, vars);
    //     if (constraints == logic.getTerm_true()) {
    //         return false;
    //     } else {
    //
    //     }
    // }

std::unique_ptr<ChcDirectedHyperGraph> constructHyperGraph(PTRef const init, PTRef const transition, PTRef const query, Logic& logic, std::vector<PTRef> vars) {
        ChcSystem chcs;

        // Adding an uninterpreted predicate P
        SymRef predicate = [&]() -> SymRef {
            vec<SRef> argSorts;
            for (PTRef var : vars) {
                argSorts.push(logic.getSortRef(var));
            }
            return logic.declareFun("P", logic.getSort_bool(), std::move(argSorts));
        }();

        chcs.addUninterpretedPredicate(predicate);

        // creating P(x_1, x_2, ..., x_n)
        auto pred = [&]() -> PTRef {
            vec<PTRef> args;
            for (PTRef var : vars) {
                args.push(var);
            }
            return logic.mkUninterpFun(predicate, std::move(args));
        }();
        // creating P(x_1', x_2', ..., x_n')
        auto pred_next = [&]() -> PTRef {
            vec<PTRef> args;
            TimeMachine tm(logic);
            for (PTRef var : vars) {
                args.push(tm.sendVarThroughTime(var, 1));
            }
            return logic.mkUninterpFun(predicate, std::move(args));
        }();
        // adding clauses to CHC system
        chcs.addClause(ChcHead{UninterpretedPredicate{pred}}, ChcBody{InterpretedFla{init}, {}});
        chcs.addClause(ChcHead{UninterpretedPredicate{pred_next}},
                       ChcBody{InterpretedFla{transition}, {UninterpretedPredicate{pred}}});
        chcs.addClause(ChcHead{UninterpretedPredicate{logic.getTerm_false()}},
                       ChcBody{InterpretedFla{query}, {UninterpretedPredicate{pred}}});
        Normalizer normalizer(logic);
        auto normalizedSystem = normalizer.normalize(chcs);
        auto hypergraph = ChcGraphBuilder(logic).buildGraph(normalizedSystem);
        assert(hypergraph->isNormalGraph());
        return hypergraph;
}

ReachabilityNonterm::Answer ReachabilityNonterm::nontermination(TransitionSystem const & ts) {

    ArithLogic & logic = dynamic_cast<ArithLogic &>(ts.getLogic());
    PTRef init  = ts.getInit();
    PTRef transition = dnfize(ts.getTransition(),logic);
    PTRef query = logic.mkNot(QuantifierElimination(logic).keepOnly(transition, ts.getStateVars()));
    auto vars = ts.getStateVars();
    if (query == logic.getTerm_false()) {
        std::cout<<"; (Trivial nontermination)" << std::endl;
        return Answer::NO;
    }

    enum JobType {TERM, NONTERM};
    struct QueueJob {
        TransitionSystem ts;
        JobType type;
    };

    std::queue<QueueJob> jobs;
    jobs.push({TransitionSystem(logic,
                        std::make_unique<SystemType>(ts.getStateVars(), ts.getAuxiliaryVars(), logic),
                        init,
                            transition,
                            query), NONTERM});

    PTRef transitionConstraint = logic.getTerm_true();
    PTRef initConstraint = logic.getTerm_true();
    while (!jobs.empty()) {
        // auto solver = std::make_unique<TPASplit>(logic, options);
        auto [job, type] = std::move(jobs.front());
        jobs.pop();

        auto graph = constructHyperGraph(job.getInit(), job.getTransition(), job.getQuery(), logic, job.getStateVars());
        // Solving constructed CHC system
        Options noptions = options;
        noptions.addOption(options.COMPUTE_WITNESS, "true");
        auto engine = EngineFactory(logic, noptions).getEngine(options.getOrDefault(Options::ENGINE, "spacer"));
        auto res = engine->solve(*graph);
        // // std::cout << "Type: " << ((type == TERM) ? "term" : "nonterm") << std::endl;
        std::cout << "Init: " << logic.pp(job.getInit()) << std::endl;
        std::cout << "Transition: " << logic.pp(job.getTransition()) << std::endl;
        std::cout << "Query: " << logic.pp(job.getQuery()) << std::endl;
        if (res.getAnswer() == VerificationAnswer::UNSAFE) {
            PTRef solverTransition = job.getTransition();
            uint num = res.getInvalidityWitness().getDerivation().size() - 3;
            std::vector formulas {job.getInit(), TimeMachine(logic).sendFlaThroughTime(job.getQuery(), num)};
            SMTSolver SMTsolver(logic, SMTSolver::WitnessProduction::ONLY_MODEL);
            for(int j=0; j < num; j++){
                formulas.push_back(TimeMachine(logic).sendFlaThroughTime(solverTransition, j));
            }
            PTRef transitions = logic.mkAnd(formulas);
            SMTsolver.assertProp(transitions);
            auto resSMT = SMTsolver.check();
            assert(resSMT == SMTSolver::Answer::SAT);
            auto model = SMTsolver.getModel();
            std::vector<PTRef> lastVars;
            for (auto var:vars) {
                lastVars.push_back(TimeMachine(logic).sendFlaThroughTime(var,num));
            }
            PTRef reached  =  ModelBasedProjection(logic).keepOnly(transitions, lastVars, *model);
            transitions = logic.mkAnd(transitions, reached);
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
                vec<PTRef> all_vars;
                uint i = 0;
                SMTsolver.resetSolver();
                SMTsolver.assertProp(logic.mkAnd(logic.mkAnd(base), TimeMachine(logic).sendFlaThroughTime(solverTransition,j-1)));
                // std::cout<<"***********CHECK*************\n";
                // std::cout<<"Base: " << logic.pp(logic.mkAnd(base)) << std::endl;
                // std::cout<<"Result: " << logic.pp(logic.mkAnd(results)) << std::endl;
                // std::cout<<"Check: " << logic.pp(TimeMachine(logic).sendFlaThroughTime(solverTransition,j-1)) << std::endl;
                // std::cout<<"*****************************\n";
                for(auto var:vars) {
                    all_vars.push(TimeMachine(logic).sendFlaThroughTime(vars[i],j));
                    i++;
                }
                //     SMTsolver.push();
                SMTsolver.assertProp(logic.mkNot(logic.mkAnd(results)));
                if (SMTsolver.check() == SMTSolver::Answer::SAT) {
                    detected = true;
                }
                SMTsolver.resetSolver();

                SMTsolver.resetSolver();
                if (detected) {
                    // TODO: I need to think on how to detect nondeterminism better
                    PTRef block = TimeMachine(logic).sendFlaThroughTime(QuantifierElimination(logic).keepOnly(transitions, all_vars), -j+1);
                    // std::cout << j <<" Block: " << logic.pp(block) << std::endl;
                    if (block == logic.getTerm_true()) {
                        detected = false;
                        SMTsolver.resetSolver();
                        continue;
                    } else {
                        SMTsolver.resetSolver();
                        SMTsolver.assertProp(logic.mkAnd(transition, logic.mkNot(block)));
                        if (SMTsolver.check() == SMTSolver::Answer::UNSAT) {
                            return Answer::YES;
                        } else {
                            SMTsolver.resetSolver();
                            SMTsolver.assertProp(logic.mkAnd({TimeMachine(logic).sendFlaThroughTime(logic.mkAnd(base), -j+1), transition, transitionConstraint, logic.mkNot(block)}));
                            if (SMTsolver.check() == SMTSolver::Answer::UNSAT) {
                                detected = false;
                                SMTsolver.resetSolver();
                                continue;
                            }
                            transitionConstraint = logic.mkAnd(transitionConstraint, logic.mkNot(block));
                        }
                    }
                }
                if (detected) { break; }
            }
            // if (type == NONTERM) {
            //     PTRef test_q = generateReachabilityQuery(logic, query, vars);
            //     // jobs.push({TransitionSystem(logic,
            //     //         std::make_unique<SystemType>(ts.getStateVars(), ts.getAuxiliaryVars(), logic),
            //     //             logic.mkAnd(init, initConstraint),
            //     //                       transition,
            //     //              logic.mkAnd(query, test_q)), TERM});
            // }
            if (detected) {
                jobs.push({TransitionSystem(logic,
                    std::make_unique<SystemType>(ts.getStateVars(), ts.getAuxiliaryVars(), logic),
                        logic.mkAnd(init, initConstraint),
                    logic.mkAnd(transition, transitionConstraint),
                         query), NONTERM});
            } else {
                transitions = QuantifierElimination(logic).keepOnly(transitions, vars);
                initConstraint = logic.mkAnd(initConstraint, logic.mkNot(transitions));
                jobs.push({TransitionSystem(logic,
                    std::make_unique<SystemType>(ts.getStateVars(), ts.getAuxiliaryVars(), logic),
                        logic.mkAnd(init, initConstraint),
                    logic.mkAnd(transition, transitionConstraint),
                         query), NONTERM});
            }

        } else if (res.getAnswer() == VerificationAnswer::SAFE) {
            // PTRef transitionInv = solver->getTransitionInvariant();
            auto witness = res.getValidityWitness();
            // std::cout<<"DEFS:  "<<witness.getDefinitions().size()<<std::endl;
            assert(witness.getDefinitions().size() == 3);
            PTRef inv;
            std::vector<PTRef> repr;
            for (auto wtn: witness.getDefinitions()) {
                if (wtn.first.x != 3 && wtn.first.x != 0) {
                    repr = graph->predicateRepresentation().getRepresentation(wtn.first);
                    inv = wtn.second;
                }
            }
            TermUtils::substitutions_map varSubstitutions;
            auto edges = graph->getEdges();
            for (uint32_t i = 0u; i < vars.size(); ++i) {
                varSubstitutions.insert({ repr[i], vars[i]});
            }
            inv = TermUtils(logic).varSubstitute(inv, varSubstitutions);
            std::cout<< "Invariant: " << logic.pp(inv) << std::endl;
             // = (*witness.getDefinitions().begin()).second;
            // PTRef inv = solver->getInductiveInvariant();
            if (type == NONTERM) {
                SMTSolver SMTsolver(logic, SMTSolver::WitnessProduction::NONE);
                SMTsolver.resetSolver();
                SMTsolver.assertProp(logic.mkAnd({job.getInit(), job.getTransition()}));
                auto resSMT = SMTsolver.check();
                if (resSMT == SMTSolver::Answer::UNSAT) {
                    return Answer::YES;
                } else {
                    SMTsolver.resetSolver();
                    PTRef constr =  logic.mkNot(QuantifierElimination(logic).keepOnly(logic.mkAnd(transition, transitionConstraint), vars));
                    SMTsolver.assertProp(logic.mkAnd({inv, constr}));
                    auto ans = SMTsolver.check();

                    if (ans == SMTSolver::Answer::UNSAT) {
                        return Answer::NO;
                    } else {
                        query = logic.mkOr(query, constr);
                        transitionConstraint = logic.getTerm_true();
                        jobs.push({TransitionSystem(logic,
                            std::make_unique<SystemType>(ts.getStateVars(), ts.getAuxiliaryVars(), logic),
                                logic.mkAnd(init, initConstraint),
                            logic.mkAnd(transition, transitionConstraint),
                                 query), NONTERM});
                        // if (checkDisjunctiveWellfoundness(logic, logic.mkAnd(inv,transitionInv), vars)) {
                        //     return Answer::YES;
                        // }
                    }
                }
            } else {
                // if (checkDisjunctiveWellfoundness(logic, logic.mkAnd(inv,transitionInv), vars)) {
                //     return Answer::YES;
                // }
            }
        } else {
            assert(false && "Unreachable!");
            return Answer::ERROR;
        }
    }



    assert(false && "Unreachable!");
    return Answer::ERROR;
}

} // namespace golem::termination
