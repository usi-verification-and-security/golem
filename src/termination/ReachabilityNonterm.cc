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

PTRef dnfize(PTRef input, Logic & logic) {
    TermUtils utils {logic};
    if (logic.isAnd(input)) {
        auto juncts = utils.getTopLevelConjuncts(input);

        for (int i = 0; i < juncts.size(); i++) {
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

    SMTSolver smt_solver(logic, SMTSolver::WitnessProduction::NONE);
    TermUtils::substitutions_map varSubstitutions;
    for (uint32_t i = 0u; i < vars.size(); ++i) {
        varSubstitutions.insert({TimeMachine(logic).sendVarThroughTime(vars[i], 1), vars[i]});
    }

    smt_solver.assertProp(TermUtils(logic).varSubstitute(itp, varSubstitutions));
    if (smt_solver.check() == SMTSolver::Answer::UNSAT) {
        return {itp};
    }


    vec<PTRef> strictCandidates;
    // if (logic.isOr(itp)) {
    // std::cout << "Pre-dnfization:" << logic.pp(itp) << std::endl;
    PTRef dnfized = dnfize(itp, logic);
    // std::cout << "Post-dnfization:" << logic.pp(dnfized) << std::endl;
    vec<PTRef> candidates = TermUtils(logic).getTopLevelDisjuncts(dnfized);
    for (auto cand:candidates) {
        smt_solver.resetSolver();
        smt_solver.assertProp(TermUtils(logic).varSubstitute(cand, varSubstitutions));
        if (smt_solver.check() == SMTSolver::Answer::UNSAT) {
            strictCandidates.push(cand);
        }
    }
    // }


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
    TermUtils utils {logic};
    auto disjuncts = utils.getTopLevelDisjuncts(dnfize(transition, logic));
    vec<PTRef> postTransition;

    for (auto junct: disjuncts) {
        postTransition.push(QuantifierElimination(logic).keepOnly(junct, vars));
    }
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
        // std::cout << "Init:" << logic.pp(init) << std::endl;
        // std::cout << "Transition:" << logic.pp(transition) << std::endl;
        // std::cout << "Sink:" << logic.pp(sink) << std::endl;
        // Constructing a graph based on the currently considered TS
        auto graph = constructHyperGraph(init, transition, sink, logic, vars);
        auto engine = EngineFactory(logic, witnesses).getEngine(witnesses.getOrDefault(Options::ENGINE, "spacer"));

        // Check if sink states are reachable within TS
        auto res = engine->solve(*graph);
        if (res.getAnswer() == VerificationAnswer::UNSAFE) {
            nunsafe++;
            std::cout << "UNSAFE: " << nunsafe << "\n";
            // When sink states are reachable, extract the number of transitions needed to reach the sink states
            uint num = res.getInvalidityWitness().getDerivation().size() - 3;
            // std::cout << "Original number: " << num << "\n";

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
                uint j = num;
                for (; j > 0; j--) {
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
                        detected = true;
                        break;
                    } else {
                        Result = Base;
                    }
                }
                PTRef temp_transition = transition;
                // Since transitions are deterministic, the trace should lead to the sink.
                // TODO: Idea for nondet transitions: use QE(TrInv, x') to detect Tr invariant sink states. (or every TrInv disjunct)
                // TODO: If from any state in the system for every TrInv disjunct Inv(x) /\ TrInv(x,x') /\ Sink_TrInv(x') is true, then
                // TODO: every disjunct is well-founded (because separate disjuncts are strict and lead to sink states)
                // TODO: check this claims
                // TODO: Construction of Well-founded TrInv from traces for non-deterministic instance
                // 1. Deterministic part can be extracted and analyzed for the invariant part in the same way as for deterministic relation
                // 2. For nondeterministic part, it is possible to extract pre/post conditions using QE on the part with nondet which can be done in 2 ways
                //      a. As a single formula, constructing interpolant based on pre and post.
                //      b. Splitting formula into determenistic/nondeterministic parts, and analyzing them separately.
                // 3. Using extracted pre/post conditions for nondet part, postconditions can be negated, and the formula should be UNSAT, which allows to construct
                //    interpolant of the transition relation.
                // TODO: Sink states can be enriched, by checking sink state for every disjunct and building a corresponding interpolant



                // TODO: Different technique
                // TODO: Every disjunct in the system has different sink states!
                // TODO: Therefore, they can be analised separately, for different initial states (which satisfy specific disjuncts)
                // TODO: This approach will also significantly simplify the verification!!!

                PTRef temp_init = init;
                PTRef temp_tr = transition;
                if (j == 0) {
                    init = logic.mkAnd(init, logic.mkNot(Result));
                    SMTSolver SMT_solver(logic, SMTSolver::WitnessProduction::NONE);
                    SMT_solver.assertProp(logic.mkAnd(init, transition));
                    // We check if init state is blocked (it's impossible to make a transition from initial state)
                    // When it is the case, TS is terminating
                    if (SMT_solver.check() == SMTSolver::Answer::UNSAT) {
                        return Answer::YES;
                    }
                } else {
                    PTRef block = TimeMachine(logic).sendFlaThroughTime(Result, -j + 1);
                    assert(block != logic.getTerm_true());
                    transition = logic.mkAnd(transition, logic.mkNot(block));
                }

                if (num > 0) {
                    // Calculate the states that are guaranteed to terminate within num transitions:
                    // (Tr^n(x,x') /\ Sink(x')) /\ not (Tr^n(x,x') /\ not Sink(x')) - is a formula, where values of x
                    // are guaranteed to terminate in n transitions
                    PTRef guaranteedTermination =
                        // logic.mkAnd(
                       // logic.mkAnd(logic.mkAnd(formulas), TimeMachine(logic).sendFlaThroughTime(sink, num)),
                       logic.mkAnd(logic.mkAnd(formulas), logic.mkNot(TimeMachine(logic).sendFlaThroughTime(sink, num)));
                    // );
                    // std::cout<<"Guaranteed termination: " << logic.pp(guaranteedTermination) << std::endl;
                    if (guaranteedTermination == logic.getTerm_false()) {
                        return Answer::NO;
                    }
                    PTRef terminatingStates = logic.mkNot(QuantifierElimination(logic).keepOnly(guaranteedTermination, vars));
                    PTRef newTransitions = logic.mkAnd({terminatingStates, logic.mkAnd(formulas), TimeMachine(logic).sendFlaThroughTime(sink, num)});
                    // std::cout<<"Terminating states: " << logic.pp(terminatingStates) << std::endl;
                    // SMTsolver.resetSolver();
                    // SMTsolver.assertProp(logic.mkAnd(terminatingStates, init));
                    // assert(SMTsolver.check() == SMTSolver::Answer::SAT);

                        // Start buiding the trace that reaches sink states
                    std::vector deterministic_trace{temp_tr};
                    vec<PTRef> eq_vars;
                    // Constructing vectors of equations x^(j-1) = x^(j)
                    for (auto var : vars) {
                        PTRef curr = TimeMachine(logic).sendVarThroughTime(var,  0);
                        PTRef next = TimeMachine(logic).sendVarThroughTime(var,  1);
                        eq_vars.push(logic.mkEq(curr, next));
                    }
                    // For every transition deterministic trace is updated, adding an Id or Tr
                    // This is needed so that Interpolant overapproximates 1 <= n <= num transitions
                    for (uint k = 1; k < num; k++) {
                        deterministic_trace.push_back(TimeMachine(logic).sendFlaThroughTime(logic.mkOr(temp_tr, logic.mkAnd(eq_vars)), k));
                    }
                    // This loop calculates the states reachable in 1 <= n <= num transitions
                    std::vector<PTRef> checked_states;
                    for (int i = 1; i < num; i++) {
                        vec<PTRef> temp_vars;
                        // Constructing vectors of variables x^(j-1) and x^(j)
                        for (auto var : vars) {
                            temp_vars.push(TimeMachine(logic).sendVarThroughTime(var,  i));
                        }
                        checked_states.push_back(TimeMachine(logic).sendFlaThroughTime(QuantifierElimination(logic).keepOnly(newTransitions, temp_vars), num-i));
                    }
                    checked_states.push_back(TimeMachine(logic).sendFlaThroughTime(sink, num));
                    // temp_sink is a formula that describes states reachable in 1 <= n <= num transitions
                    PTRef temp_sink = logic.mkOr(checked_states);
                    // std::cout<<"Temp sink: " << logic.pp(temp_sink) << std::endl;
                    SMTSolver smt_solver(logic, SMTSolver::WitnessProduction::ONLY_INTERPOLANTS);
                    smt_solver.assertProp(logic.mkAnd(deterministic_trace));
                    // std::cout<<"Det trace: " << logic.pp(logic.mkAnd(deterministic_trace)) << std::endl;
                    smt_solver.push();
                    smt_solver.assertProp(logic.mkAnd(terminatingStates,logic.mkNot(temp_sink)));
                    // Formula should be unsat, because \lnot(temp_sink) is the states which can't be reached after n transitions
                    if(smt_solver.check() == SMTSolver::Answer::UNSAT) {
                        auto itpContext = smt_solver.getInterpolationContext();
                        vec<PTRef> itps;
                        ipartitions_t mask = 1;
                        itpContext->getSingleInterpolant(itps, mask);
                        assert(itps.size() == 1);
                        // Extracting Itp(Tr /\ ... /\ Tr, Init /\ not Sink) - overapproximation of 1 <= n <= num transitions
                        PTRef itp = itps[0];

                        TermUtils::substitutions_map varSubstitutions;
                        for (uint32_t i = 0u; i < vars.size(); ++i) {
                            varSubstitutions.insert({TimeMachine(logic).sendVarThroughTime(vars[i], num), TimeMachine(logic).sendVarThroughTime(vars[i], 1)});
                        }
                        // Then interpolant is translated, so it would correspond to transition relation Itp(x,x')
                        itp = TermUtils(logic).varSubstitute(itp, varSubstitutions);

                        // Check if some part of interpolant is transition invariant
                        auto newCands = extractStrictCandidates(itp, logic, vars);
                        if (newCands.size() == 0)
                                newCands = extractStrictCandidates(logic.mkAnd(itp, logic.mkNot(sink)), logic, vars);
                                if (newCands.size() == 0) continue;
                                if (newCands.size() == 0) continue;

                        for (auto cand : newCands) {
                            strictCandidates.push(cand);
                        }
                        PTRef inv = logic.mkOr(strictCandidates);

                        smt_solver.resetSolver();
                        smt_solver.assertProp(logic.mkAnd(temp_tr, logic.mkNot(inv)));
                        // std::cout<<"Considered candidate: " << logic.pp(inv) << std::endl;
                        if(smt_solver.check() == SMTSolver::Answer::SAT) { continue; }


                        // Check if transition invariant was constrained
                        smt_solver.resetSolver();

                        // Check if inv is Transition Invariant
                        smt_solver.assertProp(logic.mkAnd({inv, TimeMachine(logic).sendFlaThroughTime(temp_tr,1), logic.mkNot(shiftOnlyNextVars(inv, vars, logic))}));
                        // std::cout << "Solving!" << std::endl;
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
                            // Left-restricted
                            smt_solver.resetSolver();
                            smt_solver.assertProp(logic.mkAnd({init, inv, TimeMachine(logic).sendFlaThroughTime(temp_tr,1), logic.mkNot(shiftOnlyNextVars(inv, vars, logic))}));
                            if (smt_solver.check() == SMTSolver::Answer::UNSAT) {
                                smt_solver.resetSolver();
                                PTRef terminatingInitStates = QuantifierElimination(logic).keepOnly(logic.mkAnd({inv, TimeMachine(logic).sendFlaThroughTime(sink, 1)}), vars);
                                smt_solver.assertProp(logic.mkAnd(logic.mkNot(terminatingInitStates), init));
                                if (smt_solver.check() == SMTSolver::Answer::UNSAT) {
                                    // std::cout<<"Left Restricted!" << std::endl;
                                    return Answer::YES;
                                } else {
                                    init = logic.mkAnd(init, logic.mkNot(terminatingInitStates));
                                    continue;
                                }
                            }

                            // Right-restricted
                            smt_solver.resetSolver();
                            smt_solver.assertProp(logic.mkAnd({ temp_tr, TimeMachine(logic).sendFlaThroughTime(inv,1), TimeMachine(logic).sendFlaThroughTime(sink,1), logic.mkNot(shiftOnlyNextVars(inv, vars, logic))}));
                            if (smt_solver.check() == SMTSolver::Answer::UNSAT) {
                                smt_solver.resetSolver();
                                PTRef terminatingInitStates = QuantifierElimination(logic).keepOnly(logic.mkAnd({inv, TimeMachine(logic).sendFlaThroughTime(sink, 1)}), vars);
                                smt_solver.assertProp(logic.mkAnd(logic.mkNot(terminatingInitStates), init));
                                if (smt_solver.check() == SMTSolver::Answer::UNSAT) {
                                    // std::cout<<"Right Restricted!" << std::endl;
                                    return Answer::YES;
                                } else {
                                    init = logic.mkAnd(init, logic.mkNot(terminatingInitStates));
                                    continue;
                                }
                            }
                        }

                    } else {
                        return Answer::ERROR;
                    }

                }
            } else {
                // If deterministic transition, Result = set of states that reaches sink states in num transitions
                Result = QuantifierElimination(logic).keepOnly(transitions, vars);
                // Init states are updated to remove terminating states from set of initial states
                init = logic.mkAnd(init, logic.mkNot(Result));
                // If there are transitions taken
                if (num > 0) {
                    // Start buiding the trace that reaches sink states
                    std::vector deterministic_trace{transition};
                    vec<PTRef> eq_vars;
                    // Constructing vectors of equations x^(j-1) = x^(j)
                    for (auto var : vars) {
                        PTRef curr = TimeMachine(logic).sendVarThroughTime(var,  0);
                        PTRef next = TimeMachine(logic).sendVarThroughTime(var,  1);
                        eq_vars.push(logic.mkEq(curr, next));
                    }
                    // For every transition deterministic trace is updated, adding an Id or Tr
                    // This is needed so that Interpolant overapproximates 1 <= n <= num transitions
                    for (uint k = 1; k < num; k++) {
                        deterministic_trace.push_back(TimeMachine(logic).sendFlaThroughTime(logic.mkOr(transition, logic.mkAnd(eq_vars)), k));
                    }
                    // This loop calculates the states reachable in 1 <= n <= num transitions
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
                    // temp_sink is a formula that describes states reachable in 1 <= n <= num transitions
                    PTRef temp_sink = logic.mkOr(checked_states);
                    SMTSolver smt_solver(logic, SMTSolver::WitnessProduction::ONLY_INTERPOLANTS);
                    smt_solver.assertProp(logic.mkAnd(deterministic_trace));
                    smt_solver.push();
                    smt_solver.assertProp(logic.mkAnd(Result,logic.mkNot(temp_sink)));
                    // Formula should be unsat, because \lnot(temp_sink) is the states which can't be reached after n transitions
                    if(smt_solver.check() == SMTSolver::Answer::UNSAT) {
                        auto itpContext = smt_solver.getInterpolationContext();
                        vec<PTRef> itps;
                        ipartitions_t mask = 1;
                        itpContext->getSingleInterpolant(itps, mask);
                        assert(itps.size() == 1);
                        // Extracting Itp(Tr /\ ... /\ Tr, Init /\ not Sink) - overapproximation of 1 <= n <= num transitions
                        PTRef itp = itps[0];

                        TermUtils::substitutions_map varSubstitutions;
                        for (uint32_t i = 0u; i < vars.size(); ++i) {
                            varSubstitutions.insert({TimeMachine(logic).sendVarThroughTime(vars[i], num), TimeMachine(logic).sendVarThroughTime(vars[i], 1)});
                        }
                        // Then interpolant is translated, so it would correspond to transition relation Itp(x,x')
                        itp = TermUtils(logic).varSubstitute(itp, varSubstitutions);

                        // Check if some part of interpolant is transition invariant
                        auto newCands = extractStrictCandidates(itp, logic, vars);
                        if (newCands.size() == 0)
                                newCands = extractStrictCandidates(logic.mkAnd(itp, logic.mkNot(sink)), logic, vars);
                                if (newCands.size() == 0) continue;

                        for (auto cand : newCands) {
                            strictCandidates.push(cand);
                        }
                        PTRef inv = logic.mkOr(strictCandidates);

                        smt_solver.resetSolver();
                        smt_solver.assertProp(logic.mkAnd(transition, logic.mkNot(inv)));
                        // std::cout<<"Considered candidate: " << logic.pp(inv) << std::endl;
                        if(smt_solver.check() == SMTSolver::Answer::SAT) { continue; }


                        // Check if transition invariant was constrained
                        smt_solver.resetSolver();

                        // Check if inv is Transition Invariant
                        smt_solver.assertProp(logic.mkAnd({inv, TimeMachine(logic).sendFlaThroughTime(transition,1), logic.mkNot(shiftOnlyNextVars(inv, vars, logic))}));
                        // std::cout << "Solving!" << std::endl;
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
                            // Left-restricted
                            smt_solver.resetSolver();
                            smt_solver.assertProp(logic.mkAnd({init, inv, TimeMachine(logic).sendFlaThroughTime(transition,1), logic.mkNot(shiftOnlyNextVars(inv, vars, logic))}));
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

                            // Right-restricted
                            smt_solver.resetSolver();
                            smt_solver.assertProp(logic.mkAnd({ transition, TimeMachine(logic).sendFlaThroughTime(inv,1), TimeMachine(logic).sendFlaThroughTime(sink,1), logic.mkNot(shiftOnlyNextVars(inv, vars, logic))}));
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

                    } else {
                        return Answer::ERROR;
                    }
                }
            }

            // if (!detected) {
            //     // If all transitions were determenistic, we block the initial states that lead to the termination
            //     init = logic.mkAnd(init, logic.mkNot(Result));
            // }

        } else if (res.getAnswer() == VerificationAnswer::SAFE) {
            nsafe++;
            std::cout << "SAFE: " << nsafe << "\n";
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