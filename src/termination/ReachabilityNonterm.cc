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


PTRef dnfize(PTRef input, ArithLogic & logic) {
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
        PTRef rev = utils.simplifyMax(logic.mkNot(input));
        // TODO: THINK IF IT IS CORRECT!!!
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
        } else if (logic.isNumEq(rev)) {
            auto it = logic.getPterm(rev).begin();
            vec<PTRef> subjuncts;
            subjuncts.push(logic.mkGeq(it[0], logic.mkPlus(it[1], logic.getTerm_IntOne())));
            subjuncts.push(logic.mkLeq(it[0], logic.mkPlus(it[1], logic.getTerm_IntMinusOne())));
            return logic.mkOr(subjuncts);
        }
    }
    return input;
}

void unrollAtom(ArithLogic & logic, std::vector<PTRef>& coefs, PTRef atom, bool reverse) {
    assert(logic.isVar(atom) || logic.isConstant(atom) || logic.isTimes(atom) || logic.isIntMinus(atom) || logic.isRealMinus(atom) || logic.isPlus(atom) || logic.isIntDiv(atom) || logic.isRealDiv(atom));
    if (logic.isConstant(atom)) {
        if (!reverse)
            coefs.push_back(logic.mkTimes(logic.getTerm_IntMinusOne(), atom));
        else
            coefs.push_back(logic.mkTimes(logic.getTerm_IntOne(), atom));
    }
    if (logic.isVar(atom)) {
        if (reverse)
            coefs.push_back(logic.mkTimes(logic.getTerm_IntMinusOne(), atom));
        else
            coefs.push_back(logic.mkTimes(logic.getTerm_IntOne(), atom));
    } else if (logic.isTimes(atom)) {
        auto it = logic.getPterm(atom).begin();
        auto size = coefs.size();
        assert(logic.getPterm(atom).size() == 2);
        PTRef constant, subatom;
        if (logic.isConstant(it[0])) {
            constant = it[0];
            subatom = it[1];
        } else {
            constant = it[1];
            subatom = it[0];
        }
        assert(logic.isConstant(constant));
        unrollAtom(logic, coefs, subatom, reverse);
        for (int i = size; i < coefs.size(); i++) {
            if (logic.isVar(coefs[i]) or logic.isConstant(coefs[i])) {
                coefs[i] = logic.mkTimes(constant, coefs[i]);
            } else if (logic.isTimes(coefs[i])) {
                auto sub = logic.getPterm(coefs[i]).begin();
                assert(logic.getPterm(coefs[i]).size() == 2);
                if (logic.isConstant(sub[0])){
                    coefs[i] = logic.mkTimes( logic.mkTimes(constant, sub[0]), sub[1]);
                } else {
                    coefs[i] = logic.mkTimes((logic.mkTimes(constant, sub[1])), sub[0]);
                }
            }

        }
    } else if (logic.isIntMinus(atom) || logic.isRealMinus(atom)) {
        auto it = logic.getPterm(atom).begin();
        assert(logic.getPterm(atom).size() == 2);
        PTRef subatom1 = it[0];
        PTRef subatom2 = it[1];
        unrollAtom(logic, coefs, subatom1, reverse);
        unrollAtom(logic, coefs, subatom2, !reverse);
    } else if (logic.isPlus(atom)) {
        auto it = logic.getPterm(atom).begin();
        while (it != logic.getPterm(atom).end()) {
            unrollAtom(logic, coefs, *it, reverse);
            it ++;
        }
    } else if (logic.isIntDiv(atom) or logic.isRealDiv(atom)) {
        auto it = logic.getPterm(atom).begin();
        auto size = coefs.size();
        assert(logic.getPterm(atom).size() == 2);
        PTRef constant = it[1];
        assert(logic.isConstant(constant));
        PTRef subatom = it[0];
        unrollAtom(logic, coefs, subatom, reverse);
        for (int i = size; i < coefs.size(); i++) {
            if (logic.isIntDiv(atom)) {
                coefs[i] = logic.mkTimes(logic.mkIntDiv(logic.getPterm(coefs[i]).begin()[0], constant), logic.getPterm(coefs[i]).begin()[1]);
            } else {
                coefs[i] = logic.mkTimes(logic.mkRealDiv(logic.getPterm(coefs[i]).begin()[0], constant), logic.getPterm(coefs[i]).begin()[1]);
            }
        }
    }

}

void getCoeffs(ArithLogic & logic, std::vector<PTRef>& coefs, PTRef formula) {
    assert (logic.isLeq(formula));
    auto it = logic.getPterm(formula).begin();
    assert(logic.getPterm(formula).size() == 2);
    unrollAtom(logic, coefs, it[0], false);
    unrollAtom(logic, coefs, it[1], true);

}

void lequalize(PTRef conjunct, vec<PTRef> & leqs, ArithLogic& logic) {
    auto it = logic.getPterm(conjunct).begin();
    // x = y <=>
    // x <= y
    // y <= x
    if (logic.isEquality(conjunct)) {
        // std::cout << "lequalized = " << logic.pp(logic.mkLeq(it[0], it[1])) << std::endl;
        // std::cout << "lequalized = " << logic.pp(logic.mkLeq(it[1], it[0])) << std::endl;
        leqs.push(logic.mkLeq(it[0], it[1]));
        leqs.push(logic.mkLeq(it[1], it[0]));
    } else if (logic.isLeq(conjunct)) {
        // x<=y
        leqs.push(conjunct);
        // std::cout << "lequalized = " << logic.pp(conjunct) << std::endl;
    } else if (logic.isGeq(conjunct)) {
        // x >= y <=>
        // y <= x
        leqs.push(logic.mkLeq(it[1], it[0]));
    } else if (logic.isNot(conjunct)) {
        PTRef inner_formula = it[0];
        it = logic.getPterm(inner_formula).begin();
        if (logic.isEquality(inner_formula)) {
            assert(false);
        } else if (logic.isLeq(inner_formula)) {
            // !(x <= y) <=>
            // y <= x-1
            leqs.push(logic.mkLeq(it[1], logic.mkPlus(it[0], logic.getTerm_IntMinusOne())));
            // std::cout << "lequalized = " << logic.pp(logic.mkLeq(it[1], logic.mkPlus(it[0], logic.getTerm_IntMinusOne()))) << std::endl;
        } else if (logic.isGeq(inner_formula)) {
            // !(x >= y) <=>
            // x <= y-1
            leqs.push(logic.mkLeq(it[0], logic.mkPlus(it[1], logic.getTerm_IntMinusOne())));
            // std::cout << "lequalized = " << logic.pp(logic.mkLeq(it[0], logic.mkPlus(it[1], logic.getTerm_IntMinusOne()))) << std::endl;
        }  else if (logic.isBoolAtom(inner_formula)) {
            return;
        } else {
            assert(false);
        }
    } else if (logic.isBoolAtom(conjunct)) {
        return;
    } else {
        assert(false);
    }
}


bool checkWellFounded(PTRef const formula, ArithLogic & logic, vec<PTRef> const & vars) {
    TermUtils utils {logic};
    PTRef dnfized = utils.simplifyMax(dnfize(formula, logic));
    // std::cout << "dnfized = " << logic.pp(dnfized) << std::endl;
    if (logic.isOr(dnfized)) {
        return false;
    }
    vec<PTRef> int_vars;
    vec<PTRef> next_vars;
    for (auto var : vars) {
        if (logic.isNumVar(var)) {
            int_vars.push(var);
            PTRef prev = TimeMachine(logic).sendVarThroughTime(var, 1);
            next_vars.push(prev);
        }
    }

    // std::cout << "CANDIDATE:" << logic.pp(dnfized) << std::endl;
    vec<PTRef> conjuncts = TermUtils(logic).getTopLevelConjuncts(dnfized);
    std::vector<PTRef> b;
    std::vector<std::vector<PTRef>> A;
    std::vector<std::vector<PTRef>> A_p;
    vec<PTRef> temp_conjuncts;
    // Preprocessing, in the end conjuncts should be a set of formulas f(x) <= c, where c is some constant, and f(x) is a linear combination of variables
    for (auto conjunct: conjuncts) {
        // std::cout << "conjunct = " << logic.pp(conjunct) << std::endl;
        lequalize(conjunct, temp_conjuncts, logic);
    }
    if (temp_conjuncts.size() == 0) {
        return true;
    }

    for (auto conjunct:temp_conjuncts) {
        A.push_back(std::vector(int_vars.size(), logic.getTerm_IntZero()));
        A_p.push_back(std::vector(int_vars.size(), logic.getTerm_IntZero()));
        std::vector<PTRef> coefs;
        // std::cout << "conjunct = " << logic.pp(conjunct) << std::endl;
        getCoeffs(logic, coefs, conjunct);
        bool found = false;
        // std::cout << "coefs size = " << coefs.size() << std::endl;
        for (int i = 0; i < coefs.size(); i++) {
            // std::cout << "coefs[i] = " << logic.pp(coefs[i]) << std::endl;
            if (logic.isConstant(coefs[i])) {
                b.push_back(coefs[i]);
                assert(!found);
                found = true;
            } else if (logic.isVar(coefs[i])) {
                for (int j = 0; j < int_vars.size(); j++) {
                    if (coefs[i] == int_vars[j]) {
                        A[A.size()-1][j] = logic.getTerm_IntOne();
                        break;
                    } else if (coefs[i] == next_vars[j]) {
                        A_p[A_p.size()-1][j] = logic.getTerm_IntOne();
                    }
                }
            } else {
                auto it = logic.getPterm(coefs[i]).begin();
                assert(logic.getPterm(coefs[i]).size() == 2);
                PTRef constant, subatom;
                if (logic.isConstant(it[0])) {
                    constant = it[0];
                    subatom = it[1];
                } else {
                    constant = it[1];
                    subatom = it[0];
                }
                assert(logic.isConstant(constant));
                for (int j = 0; j < int_vars.size(); j++) {
                    if (subatom == int_vars[j]) {
                        A[A.size()-1][j] = constant;
                        break;
                    } else if (subatom == next_vars[j]) {
                        A_p[A_p.size()-1][j] = constant;
                        break;
                    }
                }
            }
        }
        if (!found) {
            b.push_back(logic.getTerm_IntZero());
        }
    }

    // Well-foundness check by Podelski - by synthesizing the ranking function

    vec<PTRef> lambda_1, lambda_2;
    for (int i = 0; i < A.size(); i++) {
        lambda_1.push(logic.mkIntVar(("lambda_1" + std::to_string(i)).c_str()));
        lambda_2.push(logic.mkIntVar(("lambda_2" + std::to_string(i)).c_str()));
    }
    // 1. Constraint on lambdas:
    // TODO: at least some lambda_2 != 0
    PTRef ZeroIneq;
    {
        vec<PTRef> ineqs;
        for (uint i = 0; i < lambda_1.size(); ++i) {
            ineqs.push(logic.mkGeq(lambda_1[i], logic.getTerm_IntZero()));
            ineqs.push(logic.mkGeq(lambda_2[i], logic.getTerm_IntZero()));
        }
        ZeroIneq = logic.mkAnd(ineqs);
    }
    // std::cout << "ZeroIneq: " << logic.pp(ZeroIneq) << std::endl;
    // 2. lambda_1 * A_p = 0:
    PTRef firstEq;
    {
        vec<PTRef> sums;
        for (uint j = 0; j< int_vars.size(); j++) {
            vec<PTRef> mults;
            for (uint i = 0; i < lambda_1.size(); ++i) {
                mults.push(logic.mkTimes(lambda_1[i], A_p[i][j]));
            }
            PTRef sum = logic.mkPlus(mults);
            sums.push(logic.mkEq(sum, logic.getTerm_IntZero()));
        }

        firstEq = logic.mkAnd(sums);
    }
    // std::cout << "firstEq: " << logic.pp(firstEq) << std::endl;

    // 3. (lambda_1 - lambda_2) * A = 0
    PTRef secondEq;
    {
        vec<PTRef> minuses(lambda_1.size());
        for (uint i = 0; i < lambda_1.size(); i ++) {
            minuses[i] = logic.mkMinus(lambda_1[i], lambda_2[i]);
        }

        vec<PTRef> sums;
        for (uint j = 0; j< int_vars.size(); j++) {
            vec<PTRef> mults;
            for (uint i = 0; i < lambda_1.size(); ++i) {
                mults.push(logic.mkTimes(minuses[i], A[i][j]));
            }
            PTRef sum = logic.mkPlus(mults);
            sums.push(logic.mkEq(sum, logic.getTerm_IntZero()));
        }

        secondEq = logic.mkAnd(sums);
    }
    // std::cout << "secondEq: " << logic.pp(secondEq) << std::endl;

    //4. lambda_2 * (A + A_p) = 0
    PTRef thirdEq;
    {
        std::vector<std::vector<PTRef>> sumM;
        for (uint i = 0; i < A.size(); i++) {
            sumM.push_back(std::vector(int_vars.size(), logic.getTerm_IntZero()));
            for (uint j = 0; j < int_vars.size(); j++) {
                sumM[i][j] = logic.mkPlus(A[i][j], A_p[i][j]);
            }
        }
        vec<PTRef> sums;
        for (uint j = 0; j< int_vars.size(); j++) {
            vec<PTRef> mults;
            for (uint i = 0; i < lambda_2.size(); ++i) {
                mults.push(logic.mkTimes(lambda_2[i], sumM[i][j]));
            }
            PTRef sum = logic.mkPlus(mults);
            sums.push(logic.mkEq(sum, logic.getTerm_IntZero()));
        }

        thirdEq = logic.mkAnd(sums);
    }
    // std::cout << "thirdEq: " << logic.pp(thirdEq) << std::endl;

    //4. lambda_2 * b < 0
    PTRef constCheck;
    {
        vec<PTRef> sums;
        for (uint j = 0; j < lambda_2.size(); j++) {
            PTRef mult = logic.mkTimes(lambda_2[j], b[j]);
            sums.push(mult);
        }

        constCheck = logic.mkLt(logic.mkPlus(sums), logic.getTerm_IntZero());
    }
    // std::cout << "constCheck: " << logic.pp(constCheck) << std::endl;

    // Final check:
    PTRef finalCheck = logic.mkAnd({ZeroIneq, firstEq, secondEq, thirdEq, constCheck});
    SMTSolver solver(logic, SMTSolver::WitnessProduction::NONE);
    solver.assertProp(finalCheck);
    return solver.check() == SMTSolver::Answer::SAT;
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

vec<PTRef> extractStrictCandidates(PTRef itp, PTRef sink, ArithLogic& logic,  const std::vector<PTRef> & vars) {

    SMTSolver smt_solver(logic, SMTSolver::WitnessProduction::NONE);
    TermUtils::substitutions_map varSubstitutions;
    for (uint32_t i = 0u; i < vars.size(); ++i) {
        varSubstitutions.insert({TimeMachine(logic).sendVarThroughTime(vars[i], 1), vars[i]});
    }

    vec<PTRef> strictCandidates;
    auto dnfized_sink = TermUtils(logic).getTopLevelDisjuncts(dnfize(logic.mkNot(sink), logic));
    // if (logic.isOr(itp)) {
    // std::cout << "Pre-dnfization:" << logic.pp(itp) << std::endl;
    PTRef dnfized = dnfize(itp, logic);
    // std::cout << "Post-dnfization:" << logic.pp(dnfized) << std::endl;
    vec<PTRef> candidates = TermUtils(logic).getTopLevelDisjuncts(dnfized);
    for (auto cand:candidates) {
        smt_solver.resetSolver();
        smt_solver.assertProp(cand);
        if (smt_solver.check() == SMTSolver::Answer::UNSAT) {continue;}

        smt_solver.resetSolver();
        smt_solver.assertProp(TermUtils(logic).varSubstitute(cand, varSubstitutions));
        PTRef simpl_cand = TermUtils(logic).simplifyMax(cand);
        // std::cout << "Checking candidate: " << logic.pp(cand) << std::endl;
        if (smt_solver.check() == SMTSolver::Answer::UNSAT) {
            if (checkWellFounded(simpl_cand, logic, vars)) {
                // std::cout << "Well-Founded: " << logic.pp(cand) << std::endl;
                strictCandidates.push(simpl_cand);
            } else {
                for (auto sink_cand: dnfized_sink) {
                    // std::cout << "Checking candidate: " << logic.pp(logic.mkAnd(sink_cand,simpl_cand)) << std::endl;
                    smt_solver.resetSolver();
                    smt_solver.assertProp(logic.mkAnd(sink_cand,simpl_cand));
                    if (smt_solver.check() == SMTSolver::Answer::SAT && checkWellFounded(logic.mkAnd(sink_cand,simpl_cand), logic, vars)) {
                        strictCandidates.push(logic.mkAnd(sink_cand,simpl_cand));
                        // std::cout << "Well-Founded: " << logic.pp(logic.mkAnd(sink_cand,simpl_cand)) << std::endl;
                        // TODO: Maybe I can weaken recieved candidate using some kind of houdini.
                        // TODO: Particularly, I should try to remove all equalities possible (also ones that are done via <= && >=)
                    }
                }
            }
        }
    }
    // }


    return strictCandidates;
}

ReachabilityNonterm::Answer ReachabilityNonterm::run(TransitionSystem const & ts) {
    auto vars = ts.getStateVars();
    ArithLogic & logic = dynamic_cast<ArithLogic &>(ts.getLogic());
    PTRef init = ts.getInit();
    PTRef transition = ts.getTransition();
    TermUtils utils {logic};
    auto disjuncts = utils.getTopLevelDisjuncts(dnfize(transition, logic));
    vec<PTRef> postTransition;

    for (auto junct: disjuncts) {
        postTransition.push(QuantifierElimination(logic).keepOnly(junct, vars));
    }
    uint nunsafe = 0;
    uint nsafe = 0;
    uint nnondetfirst = 0;
    // In this case query is a set of sink states - states from which transition is not possible.
    // sink /\ transition is UNSAT
    PTRef sink = logic.mkNot(QuantifierElimination(logic).keepOnly(transition, vars));

    // if sink is false, there are no sink states in the TS, therefore it is nonterminating
    if (sink == logic.getTerm_false()) { return Answer::NO; }

    // Witness computation is required, as we need to use both counterexample traces to limit terminating states
    // and inductive invariants to prove nontermination
    Options witnesses = options;
    witnesses.addOption(options.COMPUTE_WITNESS, "true");
    SMTSolver detChecker(logic, SMTSolver::WitnessProduction::NONE);
    TermUtils::substitutions_map detSubstitutions;
    vec<PTRef> neq;
    // Tr(x,x') /\ Tr(x, x'') /\ ! x' = x''
    // Model(Trace, x) /\ Tr^n(x,...,x')  /\ ! (x' /\ Sink(x')) - check  if correct and simplify checks
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
    if (DETERMINISTIC_TRANSITION) {
        // std::cout << "Transition:" << logic.pp(transition) << std::endl;
        if (checkWellFounded(transition, logic, vars)) return Answer::YES;
    }
    // PTRef trInv = logic.getTerm_true();
    while (true) {
        // std::cout << "Init:" << logic.pp(inimak) << std::endl;
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
            std::cout << "Original number: " << num << "\n";
            // Construct the logical formula representing the trace:
            // Init(x) /\ Tr(x,x') /\ ... /\ Bad(x^(num))
            std::vector<PTRef> formulas;
            for (uint j = 0; j < num; j++) {
                formulas.push_back(TimeMachine(logic).sendFlaThroughTime(transition, j));
            }
            PTRef terminatingStates = QuantifierElimination(logic).keepOnly(logic.mkAnd({logic.mkAnd(formulas), TimeMachine(logic).sendFlaThroughTime(sink, num)}), vars);
            PTRef transitions = logic.mkAnd({logic.mkAnd(init, terminatingStates), logic.mkAnd(formulas), TimeMachine(logic).sendFlaThroughTime(sink, num)});

            // Get the satisfying model of the trace.
            // It is needed to detect nondeterminism
            SMTSolver SMTsolver(logic, SMTSolver::WitnessProduction::NONE);
            SMTsolver.assertProp(transitions);
            if (SMTsolver.check() != SMTSolver::Answer::SAT) {
                assert(false);
                return Answer::ERROR;
            }

            // Result is a formula, depicting all states reachable in j transitions, which can reach
            // termination in n-j transitions (if j = n it is Termination states)
            SMTsolver.resetSolver();
            SMTsolver.assertProp(logic.mkAnd({logic.mkAnd(init, terminatingStates), logic.mkAnd(formulas),logic.mkNot(TimeMachine(logic).sendFlaThroughTime(sink, num))}));

            uint j = 0;


            vec<PTRef> last_vars;
            for (auto var : vars) {
                PTRef prev = TimeMachine(logic).sendVarThroughTime(var, num);
                last_vars.push(prev);
            }
            PTRef Result = TimeMachine(logic).sendFlaThroughTime(sink, num);
            // Traversing trace from the Bad to Init, detecting the last transition where some variables
            // were assigned nondetermenistically
            if (!DETERMINISTIC_TRANSITION && SMTsolver.check() == SMTSolver::Answer::SAT) {
                j = num;
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
                        break;
                    } else {
                        Result = Base;
                    }
                }
            }
            // TODO: Different technique
            // TODO: Every disjunct in the system has different sink states!
            // TODO: Therefore, they can be analised separately, for different initial states (which satisfy specific disjuncts)
            // TODO: This approach will also significantly simplify the verification!!!

            PTRef temp_tr = transition;
            if (j == 0) {
                init = logic.mkAnd(init, logic.mkNot(terminatingStates));
                // std::cout<<"Init: " << logic.pp(init) << std::endl;
                // std::cout<<"terminatingStates: " << logic.pp(terminatingStates) << std::endl;
                // std::cout<<"Result: " << logic.pp(Result) << std::endl;
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
                // Tr^n(x,x') /\ not Sink(x') - is a formula, which can be satisfied by any x which can not terminate
                // after n transitions
                PTRef possibleNonterm = logic.mkAnd(logic.mkAnd(formulas), logic.mkNot(TimeMachine(logic).sendFlaThroughTime(sink, num)));
                PTRef stillTerms = logic.mkAnd(logic.mkAnd(formulas), TimeMachine(logic).sendFlaThroughTime(sink, num));

                SMTsolver.resetSolver();
                SMTsolver.assertProp(logic.mkAnd(init, possibleNonterm));
                if (SMTsolver.check() == SMTSolver::Answer::UNSAT) {
                    return Answer::YES;
                }

                PTRef terminatingStates = logic.mkNot(QuantifierElimination(logic).keepOnly(possibleNonterm, vars));
                PTRef statesThatCanTerm = QuantifierElimination(logic).keepOnly(stillTerms, vars);
                std::cout<<"j: " << j << std::endl;

                SMTsolver.resetSolver();
                SMTsolver.assertProp(
                    logic.mkAnd({terminatingStates, logic.mkAnd(formulas), logic.mkNot(TimeMachine(logic).sendFlaThroughTime(sink, num))}) );
                assert(SMTsolver.check() == SMTSolver::Answer::UNSAT);
                SMTsolver.resetSolver();
                SMTsolver.assertProp(logic.mkAnd({terminatingStates, statesThatCanTerm}));
                if (SMTsolver.check() == SMTSolver::Answer::UNSAT) {
                    // std::cout<<"ERROR"<<'\n';
                    return Answer::NO;
                }

                SMTsolver.resetSolver();
                SMTsolver.assertProp(logic.mkAnd({terminatingStates, logic.mkAnd(formulas), TimeMachine(logic).sendFlaThroughTime(sink, num)}));

                // std::cout<<"terminatingFormula: \nInit:" << logic.pp(terminatingStates) << std::endl;
                // std::cout<<"Transitions:" << logic.pp(logic.mkAnd(formulas)) << std::endl;
                // std::cout<<"Sink:" << logic.pp(TimeMachine(logic).sendFlaThroughTime(sink, num)) << std::endl;
                if(SMTsolver.check() != SMTSolver::Answer::SAT) {
                    return Answer::NO;
                }
                PTRef newTransitions = logic.mkAnd({terminatingStates, logic.mkAnd(formulas)});

                // Start buiding the trace that reaches sink states
                vec<PTRef> eq_vars;
                // Constructing vectors of equations x^(j-1) = x^(j)
                for (auto var : vars) {
                    PTRef curr = TimeMachine(logic).sendVarThroughTime(var,  0);
                    PTRef next = TimeMachine(logic).sendVarThroughTime(var,  1);
                    eq_vars.push(logic.mkEq(curr, next));
                }
                std::vector<PTRef> deterministic_trace{temp_tr};
                PTRef id = logic.mkAnd(eq_vars);
                for (uint k = 1; k < num; k++) {
                    // For every transition deterministic trace is updated, adding an Id or Tr// This is needed so that Interpolant overapproximates 1 <= n <= num transitionsfor (uint k = 1; k < num; k++) {
                    deterministic_trace.push_back(TimeMachine(logic).sendFlaThroughTime(logic.mkOr(temp_tr, logic.mkAnd(eq_vars)), k));
                }
                // This if calculates the states reachable in 1 <= n <= num-1 transitions
                std::vector<PTRef> checked_states;
                if (num > 1) {
                    vec<PTRef> temp_vars;
                    for (auto var : vars) {
                        temp_vars.push(TimeMachine(logic).sendVarThroughTime(var,  num-1));
                    }
                    checked_states.push_back(TimeMachine(logic).sendFlaThroughTime(QuantifierElimination(logic).keepOnly(logic.mkAnd(terminatingStates, logic.mkAnd(deterministic_trace)), temp_vars), 1));
                }
                checked_states.push_back(TimeMachine(logic).sendFlaThroughTime(sink, num));
                // temp_sink is a formula that describes states reachable in 1 <= n <= num transitions
                PTRef temp_sink = logic.mkOr(checked_states);
                SMTSolver smt_solver(logic, SMTSolver::WitnessProduction::ONLY_INTERPOLANTS);
                smt_solver.assertProp(logic.mkAnd(deterministic_trace));
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
                    auto newCands = extractStrictCandidates(itp, sink, logic, vars);

                    if (newCands.size() == 0) continue;

                    for (auto cand : newCands) {
                        strictCandidates.push(cand);
                    }
                    PTRef inv = logic.mkOr(strictCandidates);
                    // TODO: Even when Considered Candidate is not inductive invariant, all states that can terminate via it should
                    // TODO: be removed possibly, as any state for which Transition Invariant holds is guaranteed to terminate
                    // TODO: to do it, we can check for which states inv is in fact transition invariant, and remove those.
                    // TODO: Can be checked via:
                    // TODO: TrInv /\ Tr => TrInv, by QE-ing everything except for x
                    // std::cout<<"Considered candidate: " << logic.pp(inv) << std::endl;
                    smt_solver.resetSolver();
                    // Check if inv is Transition Invariant
                    smt_solver.assertProp(logic.mkAnd({logic.mkOr(inv,id), TimeMachine(logic).sendFlaThroughTime(transition,1), logic.mkNot(shiftOnlyNextVars(inv, vars, logic))}));
                    // std::cout << "Solving!" << std::endl;
                    if (smt_solver.check() == SMTSolver::Answer::UNSAT) {
                        return  Answer::YES;
                    } else {
                        // Left-restricted
                        smt_solver.resetSolver();
                        smt_solver.assertProp(logic.mkAnd({init, logic.mkOr(inv,id), TimeMachine(logic).sendFlaThroughTime(transition,1), logic.mkNot(shiftOnlyNextVars(inv, vars, logic))}));
                        if (smt_solver.check() == SMTSolver::Answer::UNSAT) {
                            return  Answer::YES;
                        }

                        // Right-restricted
                        smt_solver.resetSolver();
                        smt_solver.assertProp(logic.mkAnd({ transition, TimeMachine(logic).sendFlaThroughTime(logic.mkOr(inv,id),1), TimeMachine(logic).sendFlaThroughTime(sink,2), logic.mkNot(shiftOnlyNextVars(inv, vars, logic))}));
                        if (smt_solver.check() == SMTSolver::Answer::UNSAT) {
                            PTRef preTransition = QuantifierElimination(logic).keepOnly(logic.mkAnd(logic.mkOr(inv,id), TimeMachine(logic).sendFlaThroughTime(sink,1)),vars);
                            PTRef check = logic.mkAnd(logic.mkNot(preTransition), init);
                            smt_solver.resetSolver();
                            smt_solver.assertProp(check);
                            if (smt_solver.check() == SMTSolver::Answer::UNSAT) {
                                smt_solver.resetSolver();
                                smt_solver.assertProp(logic.mkAnd({preTransition, transition, logic.mkNot(inv)}));
                                if (smt_solver.check() == SMTSolver::Answer::UNSAT)
                                    smt_solver.resetSolver();
                                    smt_solver.assertProp(logic.mkAnd({preTransition, transition, TimeMachine(logic).sendFlaThroughTime(logic.mkOr(inv,id),1), logic.mkNot(shiftOnlyNextVars(inv, vars, logic))}));
                                    if (smt_solver.check() == SMTSolver::Answer::UNSAT) {
                                        return  Answer::YES;
                                    } else {
                                        return Answer::NO;
                                    }
                            } else {
                                init = logic.mkAnd(init, logic.mkNot(preTransition));
                                smt_solver.resetSolver();
                                smt_solver.assertProp(logic.mkAnd(preTransition, init));
                                if (smt_solver.check() == SMTSolver::Answer::UNSAT) {
                                    return  Answer::NO;
                                }
                            }
                        }
                    }

                } else {
                    // continue;
                    return Answer::ERROR;
                }

            }

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