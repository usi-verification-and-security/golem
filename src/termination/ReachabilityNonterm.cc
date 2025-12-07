/*
 * Copyright (c) 2025, Konstantin Britikov <konstantin.britikov@usi.ch>
 *
 * SPDX-License-Identifier: MIT
 */

#include "ReachabilityNonterm.h"

#include <iostream>
#include <ostream>

#include "ChcSystem.h"
#include "ModelBasedProjection.h"
#include "QuantifierElimination.h"
#include "TermUtils.h"
#include "utils/SmtSolver.h"

#include "engine/EngineFactory.h"
#include "graph/ChcGraphBuilder.h"

namespace golem::termination {

std::unique_ptr<ChcDirectedHyperGraph> constructHyperGraph(PTRef const init, PTRef const transition, PTRef const query,
                                                           Logic & logic, std::vector<PTRef> vars) {
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

PTRef shiftOnlyNextVars(PTRef formula, const std::vector<PTRef> & vars, Logic& logic) {
    TermUtils::substitutions_map varSubstitutions;
    for (uint32_t i = 0u; i < vars.size(); ++i) {
        varSubstitutions.insert({TimeMachine(logic).sendVarThroughTime(vars[i], 1), TimeMachine(logic).sendVarThroughTime(vars[i], 2)});
    }
    return TermUtils(logic).varSubstitute(formula, varSubstitutions);
}

    vec<PTRef> extractStrictCandidates(PTRef itp, Logic& logic,  const std::vector<PTRef> & vars) {

    vec<PTRef> strictCandidates;
    SMTSolver smt_solver(logic, SMTSolver::WitnessProduction::NONE);
    if (logic.isOr(itp)) {
        vec<PTRef> candidates = TermUtils(logic).getTopLevelDisjuncts(itp);
        TermUtils::substitutions_map varSubstitutions;
        for (uint32_t i = 0u; i < vars.size(); ++i) {
            varSubstitutions.insert({TimeMachine(logic).sendVarThroughTime(vars[i], 1), vars[i]});
        }
        for (auto cand:candidates) {
            smt_solver.resetSolver();
            smt_solver.assertProp(TermUtils(logic).varSubstitute(cand, varSubstitutions));
            if (smt_solver.check() == SMTSolver::Answer::UNSAT) {
                strictCandidates.push(cand);
            }
        }
    }


    return strictCandidates;
}

    //TODO: houdiniCheck always checks "invCandidates" in an atomic way, never in the relation to init
    //TODO: There is a need to search for restricted invariants as well!!!
void ReachabilityNonterm::houdiniCheck(PTRef invCandidates, PTRef transition, Logic& logic, const std::vector<PTRef> & vars) {
    // RIGHT:
    //   rightInvariants /\ currentLevelTransition /\ getNextVersion(transition) =>
    //     shiftOnlyNextVars(currentLevelTransition);
    // LEFT:
    //   leftInvariants /\ transition /\ getNextVersion(currentLevelTransition) =>
    //     shiftOnlyNextVars(currentLevelTransition);
    SMTSolver solverL(logic, SMTSolver::WitnessProduction::NONE);
    SMTSolver solverR(logic, SMTSolver::WitnessProduction::NONE);
    solverL.push();
    solverR.push();
    auto candidatesL = topLevelConjuncts(logic, invCandidates);
    auto candidatesR = topLevelConjuncts(logic, invCandidates);
    // check for right alignment
    solverR.assertProp(TimeMachine(logic).sendFlaThroughTime(transition,1));
    solverL.assertProp(transition);

    solverL.push();
    solverR.push();
    //    invCandidates.append(conjuncts);
    //    Atr(x, x') /\ tr(x', x'') => Atr(x, x'')
    //    or
    //    Atr(x', x'') /\  tr(x, x') => Atr(x, x'')
    //    Push transition once and for all
    //    While loop externally, because we may drop smth important
    PTRef goal = shiftOnlyNextVars(invCandidates, vars, logic);
    // std::cout<<"SolverL formula: " << logic.pp(TimeMachine(logic).sendFlaThroughTime(transition,1)) << std::endl;
    // std::cout<<"SolverL formula: " << logic.pp(logic.mkAnd(TimeMachine(logic).sendFlaThroughTime(invCandidates,1), logic.mkNot(goal))) << std::endl;
    // std::cout<<"SolverR formula: " << logic.pp(transition) << std::endl;
    // std::cout<<"SolverR formula: " << logic.pp(logic.mkAnd(invCandidates, logic.mkNot(goal))) << std::endl;
    solverR.assertProp(logic.mkAnd(invCandidates, logic.mkNot(goal)));
    solverL.assertProp(logic.mkAnd(TimeMachine(logic).sendFlaThroughTime(invCandidates,1), logic.mkNot(goal)));
    while (solverL.check() == SMTSolver::Answer::SAT) {
        for (int i = candidatesL.size() - 1; i >= 0; i--) {
            PTRef cand = candidatesL[i];
            solverL.pop();
            solverL.push();
            solverL.assertProp(
                logic.mkAnd(TimeMachine(logic).sendFlaThroughTime(logic.mkAnd(candidatesL),1), logic.mkNot(shiftOnlyNextVars(cand, vars, logic))));
            if (solverL.check() == SMTSolver::Answer::SAT) {
                candidatesL[i] = candidatesL[candidatesL.size() - 1];
                candidatesL.pop();
            }
        }
        solverL.pop();
        solverL.push();
        goal = shiftOnlyNextVars(logic.mkAnd(candidatesL), vars, logic);
        solverL.assertProp(logic.mkAnd(TimeMachine(logic).sendFlaThroughTime(logic.mkAnd(candidatesL), 1), logic.mkNot(goal)));
    }

    while (solverR.check() == SMTSolver::Answer::SAT) {
        for (int i = candidatesR.size() - 1; i >= 0; i--) {
            PTRef cand = candidatesR[i];
            solverR.pop();
            solverR.push();
            solverR.assertProp(logic.mkAnd(logic.mkAnd(candidatesR), logic.mkNot(shiftOnlyNextVars(cand, vars, logic))));

            if (solverR.check() == SMTSolver::Answer::SAT) {
                candidatesR[i] = candidatesR[candidatesR.size() - 1];
                candidatesR.pop();
            }
        }
        solverR.pop();
        solverR.push();
        goal = shiftOnlyNextVars(logic.mkAnd(candidatesR), vars, logic);
        solverR.assertProp(logic.mkAnd(logic.mkAnd(candidatesR), logic.mkNot(goal)));
    }
    for (auto cand : candidatesR) {
        if (std::find(rightInvariants.begin(), rightInvariants.end(), cand) != rightInvariants.end()) { continue; }
        rightInvariants.push(cand);
    }
    for (auto cand : candidatesL) {
        if (std::find(leftInvariants.begin(), leftInvariants.end(), cand) != leftInvariants.end()) { continue; }
        leftInvariants.push(cand);
    }
}

ReachabilityNonterm::Answer ReachabilityNonterm::run(TransitionSystem const & ts) {
    auto vars = ts.getStateVars();
    ArithLogic & logic = dynamic_cast<ArithLogic &>(ts.getLogic());
    PTRef init = ts.getInit();
        // std::cout << "Init:" << logic.pp(init) << std::endl;
    PTRef transition = ts.getTransition();
        // std::cout << "Transition:" << logic.pp(transition) << std::endl;
    uint nunsafe = 0;
    uint nsafe = 0;
    uint nnondetfirst = 0;
    // In this case query is a set of sink states - states from which transition is not possible.
    // sink /\ transition is UNSAT
    PTRef sink = logic.mkNot(QuantifierElimination(logic).keepOnly(transition, vars));
    // std::cout << "Sink:" << logic.pp(sink) << std::endl;

    // if sink is false, there are no sink states in the TS, therefore it is nonterminating
    if (sink == logic.getTerm_false()) { return Answer::NO; }

    // Witness computation is required, as we need to use both counterexample traces to limit terminating states
    // and inductive invariants to prove nontermination
    Options witnesses = options;
    witnesses.addOption(options.COMPUTE_WITNESS, "true");
    SMTSolver detChecker(logic, SMTSolver::WitnessProduction::NONE);
    TermUtils::substitutions_map detSubstitutions;
    vec<PTRef> neq;
    for (uint32_t i = 0u; i < vars.size(); ++i) {
        detSubstitutions.insert({TimeMachine(logic).sendVarThroughTime(vars[i],1),TimeMachine(logic).sendVarThroughTime(vars[i],2)});
        neq.push(logic.mkNot(logic.mkEq(TimeMachine(logic).sendVarThroughTime(vars[i],1),TimeMachine(logic).sendVarThroughTime(vars[i],2))));
    }
    PTRef newTransition = TermUtils(logic).varSubstitute(transition, detSubstitutions);
    detChecker.assertProp(logic.mkAnd({transition,newTransition, logic.mkOr(neq)}));
    bool DETERMINISTIC_TRANSITION = false;
    if (detChecker.check() == SMTSolver::Answer::UNSAT) {
        std::cout<<"DETERMINISTIC;"<<std::endl;
        DETERMINISTIC_TRANSITION = true;
    }
    // Main nonterm-checking loop
    vec<PTRef> strictCandidates;

    // PTRef trInv = logic.getTerm_true();
    while (true) {
        // Constructing a graph based on the currently considered TS
        auto graph = constructHyperGraph(init, transition, sink, logic, vars);
        auto engine = EngineFactory(logic, witnesses).getEngine(witnesses.getOrDefault(Options::ENGINE, "spacer"));

        // Check if sink states are reachable within TS
        auto res = engine->solve(*graph);
        if (res.getAnswer() == VerificationAnswer::UNSAFE) {
            nunsafe++;
            // When sink states are reachable, extract the number of transitions needed to reach the sink states
            uint num = res.getInvalidityWitness().getDerivation().size() - 3;

            // Construct the logical formula representing the trace:
            // Init(x) /\ Tr(x,x') /\ ... /\ Bad(x^(num))
            std::vector<PTRef> formulas;
            for (uint j = 0; j < num; j++) {
                formulas.push_back(TimeMachine(logic).sendFlaThroughTime(transition, j));
            }
            PTRef transitions = logic.mkAnd({init, logic.mkAnd(formulas), TimeMachine(logic).sendFlaThroughTime(sink, num)});

            // Get the satisfying model of the trace.
            // It is needed to detect nondeterminism
            SMTSolver SMTsolver(logic, SMTSolver::WitnessProduction::ONLY_MODEL);
            SMTsolver.assertProp(transitions);
            if (SMTsolver.check() != SMTSolver::Answer::SAT) {
                assert(false);
                return Answer::ERROR;
            }
            auto model = SMTsolver.getModel();

            // Result is a formula, depicting all states reachable in j transitions, which can reach
            // termination in n-j transitions (if j = n it is Termination states)
            PTRef Result = TimeMachine(logic).sendFlaThroughTime(sink, num);
            bool detected = false;

            // Traversing trace from the Bad to Init, detecting the last transition where some variables
            // were assigned nondetermenistically
            if (!DETERMINISTIC_TRANSITION) {
                for (uint j = num; j > 0; j--) {
                    vec<PTRef> prev_vars;
                    // Constructing vectors of variables x^(j-1) and x^(j)
                    for (auto var : vars) {
                        PTRef prev = TimeMachine(logic).sendVarThroughTime(var, j - 1);
                        prev_vars.push(prev);
                    }
                    // Base is a formula, depicting all states reachable in j-1 transitions, which can reach
                    // termination in n-j+1 transitions
                    PTRef Base = QuantifierElimination(logic).keepOnly(transitions, prev_vars);
                    SMTsolver.resetSolver();
                    // Checking if it is possible to reach states which would not lead to termination in n-j states
                    // (if j = n) it checks if it is possible to reach nontermination states from trace
                    SMTsolver.assertProp(
                        logic.mkAnd({Base, TimeMachine(logic).sendFlaThroughTime(transition, j - 1), logic.mkNot(Result)}));

                    // It means that this transition was nondetermenistic, since
                    // using transition from the states that guaranteed to reach termination in n-j+1 transitions
                    // it is possible to reach states which are not guaranteed to reach termination in n-j transitions
                    if (SMTsolver.check() == SMTSolver::Answer::SAT) {
                        // We restrict the nondeterminism that leads to the termination, removing the states
                        // which are guaranteed to terminate in n-j transitions
                        if (j==1) {
                            nnondetfirst += 1;
                        }
                        PTRef block = TimeMachine(logic).sendFlaThroughTime(Result, -j + 1);
                        assert(block != logic.getTerm_true());
                        transition = logic.mkAnd(transition, logic.mkNot(block));
                        detected = true;
                        break;
                    } else {
                        Result = Base;
                    }
                }
            } else {
                Result = QuantifierElimination(logic).keepOnly(transitions, vars);
                init = logic.mkAnd(init, logic.mkNot(Result));
                if (num > 0) {
                    std::vector<PTRef> deterministic_trace{transition};
                    vec<PTRef> eq_vars;
                    // Constructing vectors of variables x^(j-1) and x^(j)
                    for (auto var : vars) {
                        PTRef curr = TimeMachine(logic).sendVarThroughTime(var,  0);
                        PTRef next = TimeMachine(logic).sendVarThroughTime(var,  1);
                        eq_vars.push(logic.mkEq(curr, next));
                    }
                    for (uint k = 1; k < num; k++) {
                        deterministic_trace.push_back(TimeMachine(logic).sendFlaThroughTime(logic.mkOr(transition, logic.mkAnd(eq_vars)), k));
                        // deterministic_trace.push_back(TimeMachine(logic).sendFlaThroughTime(transition, k));
                        // TODO: do it via abstract transitions that overapproximate 1 < m <= 2^n transitions
                        // it is possible to do by 1: Checking one transition, 2:
                    }
                    std::vector<PTRef> checked_states;
                    for (int i = 1; i < num; i++) {
                        vec<PTRef> temp_vars;
                        // Constructing vectors of variables x^(j-1) and x^(j)
                        for (auto var : vars) {
                            temp_vars.push(TimeMachine(logic).sendVarThroughTime(var,  i));
                        }
                        checked_states.push_back(TimeMachine(logic).sendFlaThroughTime(QuantifierElimination(logic).keepOnly(transitions, temp_vars), num-i));
                    }
                    checked_states.push_back(TimeMachine(logic).sendFlaThroughTime(sink, num));
                    PTRef temp_sink = logic.mkOr(checked_states);
                    // PTRef temp_sink = TimeMachine(logic).sendFlaThroughTime(sink, num);
                    SMTSolver smt_solver(logic, SMTSolver::WitnessProduction::ONLY_INTERPOLANTS);
                    smt_solver.assertProp(logic.mkAnd(deterministic_trace));
                    smt_solver.push();
                    smt_solver.assertProp(logic.mkAnd(Result,logic.mkNot(temp_sink)));
                    // std::cout<<"Considered init: " << logic.pp(Result) << std::endl;
                    // std::cout<<"Considered transition: " << logic.pp(logic.mkAnd(deterministic_trace)) << std::endl;
                    // std::cout<<"Considered query: " << logic.pp(logic.mkNot(temp_sink)) << std::endl;
                    if(smt_solver.check() == SMTSolver::Answer::UNSAT) {
                        auto itpContext = smt_solver.getInterpolationContext();
                        vec<PTRef> itps;
                        ipartitions_t mask = 1;
                        itpContext->getSingleInterpolant(itps, mask);
                        assert(itps.size() == 1);
                        // Extracting Itp(Tr /\ ... /\ Tr, Init /\ not Sink) - overapproximation of 1 up to the num transitions
                        PTRef itp = itps[0];

                        TermUtils::substitutions_map varSubstitutions;
                        for (uint32_t i = 0u; i < vars.size(); ++i) {
                            varSubstitutions.insert({TimeMachine(logic).sendVarThroughTime(vars[i], num), TimeMachine(logic).sendVarThroughTime(vars[i], 1)});
                        }
                        // Then interpolant is translated, so it would correspond to transition relation Itp(x,x')
                        itp = TermUtils(logic).varSubstitute(itp, varSubstitutions);

                        // Check if some part of interpolant is transition invariant
                        // std::cout<<"Considered itp: " << logic.pp(itp) << std::endl;

                        auto newCands = extractStrictCandidates(itp, logic, vars);
                        if (newCands.size() == 0)
                                continue;

                        for (auto cand : newCands) {
                            strictCandidates.push(cand);
                        }
                        PTRef inv = logic.mkOr(strictCandidates);

                        {
                            // Check for the inv strictness - supposed to be strict
                            smt_solver.resetSolver();
                            varSubstitutions.clear();
                            for (uint32_t i = 0u; i < vars.size(); ++i) {
                                varSubstitutions.insert({TimeMachine(logic).sendVarThroughTime(vars[i], 1), vars[i]});
                            }
                            smt_solver.assertProp(TermUtils(logic).varSubstitute(inv, varSubstitutions));
                            assert (smt_solver.check() == SMTSolver::Answer::UNSAT);
                        }


                        // Check if transition invariant was constrained
                        smt_solver.resetSolver();
                        // std::cout<<"Considered candidate: " << logic.pp(inv) << std::endl;
                        // Check if inv is Transition Invariant
                        smt_solver.assertProp(logic.mkAnd({inv, TimeMachine(logic).sendFlaThroughTime(transition,1), logic.mkNot(shiftOnlyNextVars(inv, vars, logic))}));
                        // TODO: check if init /\ inv /\ tr is feasible.
                        // std::cout<<"Query: " << logic.pp(logic.mkAnd({inv, TimeMachine(logic).sendFlaThroughTime(transition,1), logic.mkNot(shiftOnlyNextVars(inv, vars, logic))})) << std::endl;
                        if (smt_solver.check() == SMTSolver::Answer::UNSAT) {
                            // 2. Check that Init terminates via TrInv
                            smt_solver.resetSolver();
                            PTRef terminatingInitStates = QuantifierElimination(logic).keepOnly(logic.mkAnd({inv, TimeMachine(logic).sendFlaThroughTime(sink, 1)}), vars);
                            smt_solver.assertProp(logic.mkAnd(logic.mkNot(terminatingInitStates), init));
                            if (smt_solver.check() == SMTSolver::Answer::UNSAT) {
                                return Answer::YES;
                            } else {
                                init = logic.mkAnd(init, logic.mkNot(terminatingInitStates));
                                continue;
                            }

                        } else {
                            // TODO: Introduce Restricted TrInv
                            // Left-restricted
                            smt_solver.resetSolver();
                            smt_solver.assertProp(logic.mkAnd({init, inv, TimeMachine(logic).sendFlaThroughTime(transition,1)}));
                            if (smt_solver.check() == SMTSolver::Answer::SAT) {
                                smt_solver.assertProp(logic.mkNot(shiftOnlyNextVars(inv, vars, logic)));
                                if (smt_solver.check() == SMTSolver::Answer::UNSAT) {
                                    smt_solver.resetSolver();
                                    PTRef terminatingInitStates = QuantifierElimination(logic).keepOnly(logic.mkAnd({inv, TimeMachine(logic).sendFlaThroughTime(sink, 1)}), vars);
                                    smt_solver.assertProp(logic.mkAnd(logic.mkNot(terminatingInitStates), init));
                                    if (smt_solver.check() == SMTSolver::Answer::UNSAT) {
                                        return Answer::YES;
                                    } else {
                                        init = logic.mkAnd(init, logic.mkNot(terminatingInitStates));
                                        continue;
                                    }
                                }
                            }

                            // Right-restricted
                            smt_solver.resetSolver();
                            smt_solver.assertProp(logic.mkAnd({ transition, TimeMachine(logic).sendFlaThroughTime(inv,1), sink}));
                            if (smt_solver.check() == SMTSolver::Answer::SAT) {
                                smt_solver.assertProp(logic.mkNot(shiftOnlyNextVars(inv, vars, logic)));
                                if (smt_solver.check() == SMTSolver::Answer::UNSAT) {
                                    smt_solver.resetSolver();
                                    PTRef terminatingInitStates = QuantifierElimination(logic).keepOnly(logic.mkAnd({inv, TimeMachine(logic).sendFlaThroughTime(sink, 1)}), vars);
                                    smt_solver.assertProp(logic.mkAnd(logic.mkNot(terminatingInitStates), init));
                                    if (smt_solver.check() == SMTSolver::Answer::UNSAT) {
                                        return Answer::YES;
                                    } else {
                                        init = logic.mkAnd(init, logic.mkNot(terminatingInitStates));
                                        continue;
                                    }
                                }
                            }

                            // varSubstitutions.clear();
                            // for (uint32_t i = 0u; i < vars.size(); ++i) {
                            //     varSubstitutions.insert({TimeMachine(logic).sendVarThroughTime(vars[i], 1), vars[i]});
                            // }
                            // smt_solver.assertProp(TermUtils(logic).varSubstitute(inv, varSubstitutions));
                            // // 1. Check that TrInv(x,x) is UNSAT, otherwise there is a possibility of lasso
                            // if (smt_solver.check() == SMTSolver::Answer::UNSAT) {
                            //     smt_solver.resetSolver();
                            //     PTRef terminatingInitStates = QuantifierElimination(logic).keepOnly(logic.mkAnd({inv, TimeMachine(logic).sendFlaThroughTime(sink, 1)}), vars);
                            //     smt_solver.assertProp(logic.mkAnd(logic.mkNot(terminatingInitStates), init));
                            //     // 2. Check that there are states in Init, which do not terminate via TrInv
                            //     if (smt_solver.check() == SMTSolver::Answer::UNSAT) {
                            //         return Answer::YES;
                            //     } else {
                            //         Result = logic.mkNot(terminatingInitStates);
                            //         continue;
                            //     }
                            // }
                        }

                    } else {
                        // Since transitions are deterministic, the trace should lead to the sink.
                        // TODO: Idea for nondet transitions: use QE(TrInv, x') to detect Tr invariant sink states. (or every TrInv disjunct)
                        // TODO: If from any state in the system for every TrInv disjunct Inv(x) /\ TrInv(x,x') /\ Sink_TrInv(x') is true, then
                        // TODO: every disjunct is well-founded (because separate disjuncts are strict and lead to sink states)
                        // TODO: check this claims
                        return Answer::ERROR;
                    }
                }

            }
            // If counterexample is detected, we attempt to construct a disjunctive Transition Invariant
            // I. We use interpolation to construct invariant candidates
            // They should maintain the following property:
            // 1. TrInv /\ Tr => TrInv - Transition invariant should be inductive or
            // 2. Tr /\ TrInv => TrInv
            // II. We check if TrInv proves termination
            // This Transition invariant will witness temination by following the next conditions:
            // 1. TrInv(x,x) should be UNSAT - it is impossible to return in the same state, otherwise lasso is present
            // 2. forall x s.t. Init(x) exists x' s.t. TrInv(x,x') /\ Sink(x'). This can be represented by the following check:
            //      not QE(TrInv(x,x') /\ Sink(x'), x) /\ Init(x) should be false. In this conjunction  QE(TrInv(x,x') /\ Sink(x'), x)
            //      is all of the states that can reach Sink via transition relation and it demonstrates if there are some states in Init
            //      which still can't reach termination via TrInv.
            // 3. Considered Tr should be deterministic, because if it is nondet, it is possible
            // if (num>0 && j<num) {
            //     // I. Construction of transition invariant candidates
            //     SMTSolver smt_solver(logic, SMTSolver::WitnessProduction::ONLY_INTERPOLANTS);
            //     // Constructing the deterministic trace that leads to the violation of the safety Property (If from init, can be just formulas)
            //     std::vector<PTRef> deterministic_trace;
            //     for (uint k = 0; k < num-j; k++) {
            //         deterministic_trace.push_back(TimeMachine(logic).sendFlaThroughTime(transition, k));
            //     }
            //     smt_solver.assertProp(logic.mkAnd(deterministic_trace));
            //     smt_solver.push();
            //     // std::cout << "Init:" << logic.pp(Result) << std::endl;
            //     // std::cout << "Tr:" << logic.pp(logic.mkAnd(deterministic_trace)) << std::endl;
            //     // std::cout << "Sink:" << logic.pp(TimeMachine(logic).sendFlaThroughTime(sink, num)) << std::endl;
            //     smt_solver.assertProp(logic.mkAnd(Result,logic.mkNot(TimeMachine(logic).sendFlaThroughTime(sink, num))));
            //     // SMT check, to verify that Result() /\ Tr ... /\ Tr /\ not Sink is UNSAT
            //     // This is expected, because Result is QEd part of the formula, and every transition from Result is determenistic
            //     if(smt_solver.check() == SMTSolver::Answer::UNSAT) {
            //         auto itpContext = smt_solver.getInterpolationContext();
            //         vec<PTRef> itps;
            //         ipartitions_t mask = 1;
            //         itpContext->getSingleInterpolant(itps, mask);
            //         assert(itps.size() == 1);
            //         // Extracting Itp(Tr /\ ... /\ Tr, Init /\ not Sink) - overapproximation of relations that don't lead to violation of safety property
            //         PTRef itp = itps[0];
            //         smt_solver.pop();
            //         smt_solver.resetSolver();
            //         TermUtils::substitutions_map varSubstitutions;
            //         for (uint32_t i = 0u; i < vars.size(); ++i) {
            //             varSubstitutions.insert({TimeMachine(logic).sendVarThroughTime(vars[i], num), TimeMachine(logic).sendVarThroughTime(vars[i], 1)});
            //         }
            //         // Then interpolant is translated, so it would correspond to transition relation Itp(x,x')
            //         itp = TermUtils(logic).varSubstitute(itp, varSubstitutions);
            //         // TODO: a. Do houdini here, decomposing itp into conjuncts and checking every conjunct for being +
            //         // TODO: a left/right transition invariant                                                        -
            //         // TODO: b. Save previously detected invariants which don't prove termination                     +
            //         // TODO: c. MAKE L AND R checks                                                                   -
            //         houdiniCheck(itp, transition, logic, vars);
            //
            //
            //         // This check verifies that itp is transition invariant
            //         // Itp(x,x') /\ Tr(x',x'') => Itp(x,x'')
            //         smt_solver.assertProp(logic.mkAnd({itp,TimeMachine(logic).sendFlaThroughTime(transition, 1),logic.mkNot(shiftOnlyNextVars(itp, vars, logic))}));
            //         // std::cout << "Check: " << logic.pp(logic.mkAnd({itp,TimeMachine(logic).sendFlaThroughTime(transition, 1),logic.mkNot(shiftOnlyNextVars(itp, vars, logic))})) << "\n";
            //         if (smt_solver.check() == SMTSolver::Answer::UNSAT) {
            //             // II. Check if TrInv proves termination
            //             smt_solver.resetSolver();
            //             varSubstitutions.clear();
            //             PTRef inv = logic.mkAnd(logic.mkAnd(leftInvariants), logic.mkAnd(rightInvariants));
            //             for (uint32_t i = 0u; i < vars.size(); ++i) {
            //                 varSubstitutions.insert({TimeMachine(logic).sendVarThroughTime(vars[i], 1), vars[i]});
            //             }
            //             smt_solver.assertProp(TermUtils(logic).varSubstitute(inv, varSubstitutions));
            //             // 1. Check that TrInv(x,x) is UNSAT, otherwise there is a possibility of loop
            //             if (smt_solver.check() == SMTSolver::Answer::UNSAT) {
            //                 smt_solver.resetSolver();
            //                 PTRef terminatingInitStates = QuantifierElimination(logic).keepOnly(logic.mkAnd({inv, TimeMachine(logic).sendFlaThroughTime(sink, 1)}), vars);
            //                 smt_solver.assertProp(logic.mkAnd(logic.mkNot(terminatingInitStates), init));
            //                 // 2. Check that found TrInv(x,x') guarantees that every initial state terminates
            //                 //    (corresponds to the check II.3.)
            //                 if (smt_solver.check() == SMTSolver::Answer::UNSAT) {
            //                     return Answer::YES;
            //                 } else {
            //                     logic.mkAnd(init, logic.mkNot(terminatingInitStates));
            //                     continue;
            //                 }
            //             }
            //         }
            //     } else {
            //         return Answer::ERROR;
            //     }
            // }
            if (!detected) {
                // If all transitions were determenistic, we block the initial states that lead to the termination
                init = logic.mkAnd(init, logic.mkNot(Result));
            }

        } else if (res.getAnswer() == VerificationAnswer::SAFE) {
            nsafe++;
            // In case if sink states are not reachable, we need to construct the inductive invariant and demonstrate
            // that it doesn't contain any sink states itself.
            // It is possible since we add constraints to the transition relation, which were not accounted for
            // initially.
            auto witness = res.getValidityWitness();
            assert(witness.getDefinitions().size() == 3);
            PTRef inv;
            std::vector<PTRef> repr;
            // First, we extract the invariant from the witness. It is interpretation of predicate P.
            for (auto wtn : witness.getDefinitions()) {
                if (wtn.first.x != 3 && wtn.first.x != 0) {
                    repr = graph->predicateRepresentation().getRepresentation(wtn.first);
                    inv = wtn.second;
                }
            }
            TermUtils::substitutions_map varSubstitutions;
            for (uint32_t i = 0u; i < vars.size(); ++i) {
                varSubstitutions.insert({repr[i], vars[i]});
            }
            // Then invariant is translated, so the variables correspond to the encoding of the CHC system,
            // pre-normalization
            inv = TermUtils(logic).varSubstitute(inv, varSubstitutions);

            SMTSolver SMTsolver(logic, SMTSolver::WitnessProduction::NONE);
            SMTsolver.assertProp(logic.mkAnd(init, transition));
            // We check if init state is blocked (it's impossible to make a transition from initial state)
            // When it is the case, TS is terminating
            if (SMTsolver.check() == SMTSolver::Answer::UNSAT) {
                return Answer::YES;
            } else {
                SMTsolver.resetSolver();
                SMTsolver.assertProp(
                    logic.mkAnd({inv, transition, logic.mkNot(TimeMachine(logic).sendFlaThroughTime(inv, 1))}));
                assert(SMTsolver.check() == SMTSolver::Answer::UNSAT);
                PTRef constr = logic.mkNot(QuantifierElimination(logic).keepOnly(transition, vars));
                SMTsolver.resetSolver();
                SMTsolver.assertProp(logic.mkAnd({inv, constr}));
                // We check if from any state satisfying the invariant it is possible to take a transition.
                // For this we check the reverse, if there exists a state satisfying Inv, from which it is impossible
                // to take a transition:
                // Exists x. Inv(x) /\ Does not (Exist x'.  Tr(x,x')) - right conjunct is QE-ed
                // Meaning there exists a state satisfying an invariant, such that there does not exist a SAT transition
                // from this state If it is the case, there exist a sink state in the invariant - otherwise, invariant
                // is a recurrent set
                if (SMTsolver.check() == SMTSolver::Answer::UNSAT) {
                    // std::cout<<"Final check:" << logic.pp(logic.mkAnd({inv, constr})) << "\n";
                    return Answer::NO;
                } else {
                    // We update the sink states by the detected sink states and rerun the verification
                    sink = constr;
                }
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