/*
 * Copyright (c) 2025, Konstantin Britikov <konstantin.britikov@usi.ch>
 *
 * SPDX-License-Identifier: MIT
 */

#include "ReachabilityNonterm.h"

#include "ChcSystem.h"
#include "ModelBasedProjection.h"
#include "QuantifierElimination.h"
#include "TermUtils.h"
#include "utils/SmtSolver.h"

#include "engine/EngineFactory.h"
#include "graph/ChcGraphBuilder.h"

namespace golem::termination {

// Function to convert UFLIA formula into the DNF
PTRef dnfize(PTRef input, ArithLogic & logic) {
    TermUtils utils{logic};
    if (logic.isAnd(input)) {
        // x /\ (y \/ v) <=> (x /\ y) \/ (x /\ v)
        auto juncts = utils.getTopLevelConjuncts(input);

        std::vector<vec<PTRef>> subjuncts;
        for (int i = 0; i < juncts.size(); i++) {
            // every conjunct is being dnfized
            PTRef after_junct = dnfize(juncts[i], logic);
            // if any of the conjuncts is a disjunction, then the whole formula is converted into disjunction of conjs
            if (logic.isOr(after_junct)) {
                subjuncts.push_back(utils.getTopLevelDisjuncts(after_junct));
            } else {
                subjuncts.push_back({after_junct});
            }
        }
        std::vector<std::vector<PTRef>> output{{logic.getTerm_true()}};
        // Iterate over all subjuncts, composing a resulting formula
        for (uint i = 0; i < subjuncts.size(); i++) {
            // if subjuncts size is 1, it is added to every conjunct
            if (subjuncts[i].size() == 1) {
                for (uint j = 0; j < output.size(); j++) {
                    output[j].push_back(subjuncts[i][0]);
                }
                // else, if some subjunct is a disjunction composed of n disjuncts, then conjunctions should be split
                // into n disjunctions (corresponding to each disjunct)
            } else if (subjuncts[i].size() > 1) {
                uint size = output.size();
                for (int j = 0; j < subjuncts[i].size() - 1; j++) {
                    // first we extend number of disjuncts (initially m) into m*n
                    for (uint k = 0; k < size; k++) {
                        output.push_back(output[k]);
                    }
                }

                // then every disjunct is conjoined with corresponding disjunct
                for (int j = 0; j < subjuncts[i].size(); j++) {
                    for (uint k = 0; k < size; k++) {
                        output[j * size + k].push_back(subjuncts[i][j]);
                    }
                }
            } else {
                assert(false);
            }
        }
        vec<PTRef> disjuncts;
        for (auto sub : output) {
            disjuncts.push(logic.mkAnd(sub));
        }
        return logic.mkOr(disjuncts);
        // if formula is a disjunction, every disjunct should be checked to move all disjunctions to top level
    } else if (logic.isOr(input)) {
        // x \/ (y /\ (z \/ v)) <=> x \/ (y /\ z) \/ (y /\ v)
        auto juncts = utils.getTopLevelDisjuncts(input);
        vec<PTRef> postprocessJuncts;
        for (int i = 0; i < (int)juncts.size(); i++) {
            PTRef after_junct = dnfize(juncts[i], logic);
            if (logic.isOr(after_junct)) {
                auto subjuncts = utils.getTopLevelDisjuncts(after_junct);
                for (auto subjunct : subjuncts) {
                    postprocessJuncts.push(subjunct);
                }
            } else {
                postprocessJuncts.push(after_junct);
            }
        }
        return logic.mkOr(postprocessJuncts);
        // if formula is a negation, then the results of negation is calculated for conjunction, disjunction and
        // EQUALITY.
    } else if (logic.isNot(input)) {
        PTRef rev = utils.simplifyMax(logic.mkNot(input));
        if (logic.isAnd(rev)) {
            // !(x /\ y) <=> !x \/ !y
            auto subjuncts = utils.getTopLevelConjuncts(rev);
            vec<PTRef> postprocessJuncts;
            for (int i = 0; i < (int)subjuncts.size(); i++) {
                postprocessJuncts.push(logic.mkNot(subjuncts[i]));
            }
            return dnfize(logic.mkOr(postprocessJuncts), logic);
        } else if (logic.isOr(rev)) {
            // !(x \/ y) <=> !x /\ !y
            auto subjuncts = utils.getTopLevelDisjuncts(input);
            vec<PTRef> postprocessJuncts;
            for (int i = 0; i < (int)subjuncts.size(); i++) {
                postprocessJuncts.push(logic.mkNot(subjuncts[i]));
            }
            return dnfize(logic.mkAnd(postprocessJuncts), logic);
        } else if (logic.isNumEq(rev)) {
            auto it = logic.getPterm(rev).begin();
            vec<PTRef> subjuncts;
            // x != y <=> x <= y-1 \/ x >= y+1
            subjuncts.push(logic.mkGeq(it[0], logic.mkPlus(it[1], logic.getTerm_IntOne())));
            subjuncts.push(logic.mkLeq(it[0], logic.mkPlus(it[1], logic.getTerm_IntMinusOne())));
            return logic.mkOr(subjuncts);
        }
    }
    return input;
}

// This function is needed to extract specific atoms from the arithmetic formula
void unrollAtom(ArithLogic & logic, std::vector<PTRef> & coefs, PTRef atom, bool reverse) {
    assert(logic.isVar(atom) || logic.isConstant(atom) || logic.isTimes(atom) || logic.isIntMinus(atom) ||
           logic.isRealMinus(atom) || logic.isPlus(atom) || logic.isIntDiv(atom) || logic.isRealDiv(atom));
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
        for (auto i = size; i < coefs.size(); i++) {
            if (logic.isVar(coefs[i]) or logic.isConstant(coefs[i])) {
                coefs[i] = logic.mkTimes(constant, coefs[i]);
            } else if (logic.isTimes(coefs[i])) {
                auto sub = logic.getPterm(coefs[i]).begin();
                assert(logic.getPterm(coefs[i]).size() == 2);
                if (logic.isConstant(sub[0])) {
                    coefs[i] = logic.mkTimes(logic.mkTimes(constant, sub[0]), sub[1]);
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
            it++;
        }
    } else if (logic.isIntDiv(atom) or logic.isRealDiv(atom)) {
        auto it = logic.getPterm(atom).begin();
        auto size = coefs.size();
        assert(logic.getPterm(atom).size() == 2);
        PTRef constant = it[1];
        assert(logic.isConstant(constant));
        PTRef subatom = it[0];
        unrollAtom(logic, coefs, subatom, reverse);
        for (auto i = size; i < coefs.size(); i++) {
            if (logic.isIntDiv(atom)) {
                coefs[i] = logic.mkTimes(logic.mkIntDiv(logic.getPterm(coefs[i]).begin()[0], constant),
                                         logic.getPterm(coefs[i]).begin()[1]);
            } else {
                coefs[i] = logic.mkTimes(logic.mkRealDiv(logic.getPterm(coefs[i]).begin()[0], constant),
                                         logic.getPterm(coefs[i]).begin()[1]);
            }
        }
    }
}

// Function to get all of the atoms from the inequalities
void getCoeffs(ArithLogic & logic, std::vector<PTRef> & coefs, PTRef formula) {
    assert(logic.isLeq(formula));
    auto it = logic.getPterm(formula).begin();
    assert(logic.getPterm(formula).size() == 2);
    unrollAtom(logic, coefs, it[0], false);
    unrollAtom(logic, coefs, it[1], true);
}

// Function to turn everything in <= formulas
void lequalize(PTRef conjunct, vec<PTRef> & leqs, vec<PTRef> & bools, ArithLogic & logic) {
    auto it = logic.getPterm(conjunct).begin();
    // x = y <=> x <= y /\ y <= x
    if (logic.isEquality(conjunct)) {
        leqs.push(logic.mkLeq(it[0], it[1]));
        leqs.push(logic.mkLeq(it[1], it[0]));
    } else if (logic.isLeq(conjunct)) {
        // x<=y
        leqs.push(conjunct);
    } else if (logic.isGeq(conjunct)) {
        // x >= y <=> y <= x
        leqs.push(logic.mkLeq(it[1], it[0]));
    } else if (logic.isNot(conjunct)) {
        PTRef inner_formula = it[0];
        it = logic.getPterm(inner_formula).begin();
        if (logic.isEquality(inner_formula)) {
            assert(false);
        } else if (logic.isLeq(inner_formula)) {
            // !(x <= y) <=> y <= x-1
            leqs.push(logic.mkLeq(it[1], logic.mkPlus(it[0], logic.getTerm_IntMinusOne())));
        } else if (logic.isGeq(inner_formula)) {
            // !(x >= y) <=> x <= y-1
            leqs.push(logic.mkLeq(it[0], logic.mkPlus(it[1], logic.getTerm_IntMinusOne())));
        } else if (logic.isBoolAtom(inner_formula)) {
            bools.push(conjunct);
        } else {
            assert(false);
        }
    } else if (logic.isBoolAtom(conjunct)) {
        bools.push(conjunct);
    } else {
        assert(false);
    }
}

bool checkWellFounded(PTRef const formula, ArithLogic & logic, vec<PTRef> const & vars) {
    TermUtils utils{logic};
    SMTSolver solver(logic, SMTSolver::WitnessProduction::NONE);

    PTRef dnfized = utils.simplifyMax(dnfize(formula, logic));

    if (logic.isOr(dnfized)) return false;

    vec<PTRef> int_vars;
    vec<PTRef> next_vars;
    // Extract integer variables from the inequalities
    for (auto var : vars) {
        if (logic.isNumVar(var)) {
            int_vars.push(var);
            next_vars.push(TimeMachine(logic).sendVarThroughTime(var, 1));
        }
    }

    vec<PTRef> conjuncts = TermUtils(logic).getTopLevelConjuncts(dnfized);
    std::vector<PTRef> b;
    std::vector<std::vector<PTRef>> A;
    std::vector<std::vector<PTRef>> A_p;

    vec<PTRef> leq_conjuncts;
    vec<PTRef> bools;
    // Preprocessing, conjuncts should be a set of formulas f(x) <= c, where c is some constant, and f(x)
    // is a linear combination of variables
    for (auto conjunct : conjuncts) {
        lequalize(conjunct, leq_conjuncts, bools, logic);
    }

    // TODO: Think about termination in the presence of booleans
    if (leq_conjuncts.size() == 0) {
        // This is pure boolean formula
        TermUtils::substitutions_map varSubstitutions;
        for (int i = 0; i < vars.size(); ++i) {
            varSubstitutions.insert({TimeMachine(logic).sendVarThroughTime(vars[i], 1), vars[i]});
        }
        solver.assertProp(TermUtils(logic).varSubstitute(logic.mkAnd(bools), varSubstitutions));
        return solver.check() == SMTSolver::Answer::UNSAT;
    } else if (bools.size() > 0) {
        // TODO: If transition is possible to take only once it should be well-founded
        // TODO: However, such disjuncts tend to create loops within trInvariants
        // TODO: like TrInv(x,x') = (!a /\ b /\ a' /\ !b') \/ (a /\ !b /\ b' /\ !a'), which violates termination
        // TODO: These are both well-founded disjuncts, but they don't prove termination taken together
        // TODO: However, if there are no booolean loops, it is sufficient to prove termination...
        solver.assertProp(
            logic.mkAnd(logic.mkAnd(bools), TimeMachine(logic).sendFlaThroughTime(logic.mkAnd(bools), 1)));
        // This is a check to see if it is possible to take transition twice
        // (Otherwise it is trivially well-founded)
        // if (solver.check() == SMTSolver::Answer::UNSAT) return true;
        solver.resetSolver();
    }

    // Computation of matrixes A, A_p, and vector b based on the coefficients of vars and constants
    for (auto conjunct : leq_conjuncts) {
        A.push_back(std::vector(int_vars.size(), logic.getTerm_IntZero()));
        A_p.push_back(std::vector(int_vars.size(), logic.getTerm_IntZero()));
        std::vector<PTRef> coefs;
        getCoeffs(logic, coefs, conjunct);
        bool found = false;
        for (size_t i = 0; i < coefs.size(); i++) {
            if (logic.isConstant(coefs[i])) {
                b.push_back(coefs[i]);
                assert(!found);
                if (found) exit(1);
                found = true;
            } else if (logic.isVar(coefs[i])) {
                for (int j = 0; j < int_vars.size(); j++) {
                    if (coefs[i] == int_vars[j]) {
                        if (A[A.size() - 1][j] != logic.getTerm_IntZero()) { exit(1); }
                        A[A.size() - 1][j] = logic.getTerm_IntOne();
                        break;
                    } else if (coefs[i] == next_vars[j]) {
                        if (A_p[A_p.size() - 1][j] != logic.getTerm_IntZero()) { exit(1); }
                        A_p[A_p.size() - 1][j] = logic.getTerm_IntOne();
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
                        if (A_p[A.size() - 1][j] != logic.getTerm_IntZero()) { exit(1); }
                        A[A.size() - 1][j] = constant;
                        break;
                    } else if (subatom == next_vars[j]) {
                        if (A_p[A_p.size() - 1][j] != logic.getTerm_IntZero()) { exit(1); }
                        A_p[A_p.size() - 1][j] = constant;
                        break;
                    }
                }
            }
        }
        if (!found) { b.push_back(logic.getTerm_IntZero()); }
    }

    // Well-foundness check by Podelski - by synthesizing the ranking function
    vec<PTRef> lambda_1, lambda_2;
    for (size_t i = 0; i < A.size(); i++) {
        lambda_1.push(logic.mkIntVar(("lambda_1" + std::to_string(i)).c_str()));
        lambda_2.push(logic.mkIntVar(("lambda_2" + std::to_string(i)).c_str()));
    }
    // 0. Constraint on lambdas:
    PTRef ZeroIneq;
    {
        vec<PTRef> ineqs;
        for (auto i = 0; i < lambda_1.size(); ++i) {
            ineqs.push(logic.mkGeq(lambda_1[i], logic.getTerm_IntZero()));
            ineqs.push(logic.mkGeq(lambda_2[i], logic.getTerm_IntZero()));
        }
        ZeroIneq = logic.mkAnd(ineqs);
    }

    // 1. lambda_1 * A_p = 0:
    PTRef firstEq;
    {
        vec<PTRef> sums;
        for (auto j = 0; j < int_vars.size(); j++) {
            vec<PTRef> mults;
            for (auto i = 0; i < lambda_1.size(); ++i) {
                mults.push(logic.mkTimes(lambda_1[i], A_p[i][j]));
            }
            PTRef sum = logic.mkPlus(mults);
            sums.push(logic.mkEq(sum, logic.getTerm_IntZero()));
        }

        firstEq = logic.mkAnd(sums);
    }

    // 2. (lambda_1 - lambda_2) * A = 0
    PTRef secondEq;
    {
        vec<PTRef> minuses(lambda_1.size());
        for (auto i = 0; i < lambda_1.size(); i++) {
            minuses[i] = logic.mkMinus(lambda_1[i], lambda_2[i]);
        }

        vec<PTRef> sums;
        for (auto j = 0; j < int_vars.size(); j++) {
            vec<PTRef> mults;
            for (auto i = 0; i < lambda_1.size(); ++i) {
                mults.push(logic.mkTimes(minuses[i], A[i][j]));
            }
            PTRef sum = logic.mkPlus(mults);
            sums.push(logic.mkEq(sum, logic.getTerm_IntZero()));
        }

        secondEq = logic.mkAnd(sums);
    }

    // 3. lambda_2 * (A + A_p) = 0
    PTRef thirdEq;
    {
        std::vector<std::vector<PTRef>> sumM;
        for (size_t i = 0; i < A.size(); i++) {
            sumM.push_back(std::vector(int_vars.size(), logic.getTerm_IntZero()));
            for (int j = 0; j < int_vars.size(); j++) {
                sumM[i][j] = logic.mkPlus(A[i][j], A_p[i][j]);
            }
        }
        vec<PTRef> sums;
        for (auto j = 0; j < int_vars.size(); j++) {
            vec<PTRef> mults;
            for (auto i = 0; i < lambda_2.size(); ++i) {
                mults.push(logic.mkTimes(lambda_2[i], sumM[i][j]));
            }
            PTRef sum = logic.mkPlus(mults);
            sums.push(logic.mkEq(sum, logic.getTerm_IntZero()));
        }

        thirdEq = logic.mkAnd(sums);
    }

    // 4. lambda_2 * b < 0
    PTRef constCheck;
    {
        vec<PTRef> sums;
        for (auto j = 0; j < lambda_2.size(); j++) {
            PTRef mult = logic.mkTimes(lambda_2[j], b[j]);
            sums.push(mult);
        }

        constCheck = logic.mkLt(logic.mkPlus(sums), logic.getTerm_IntZero());
    }

    // Final check:
    PTRef finalCheck = logic.mkAnd({ZeroIneq, firstEq, secondEq, thirdEq, constCheck});
    solver.resetSolver();
    solver.assertProp(finalCheck);
    return solver.check() == SMTSolver::Answer::SAT;
}



PTRef houdiniCheck(PTRef candidate, ArithLogic& logic, const std::vector<PTRef> & vars) {
   assert(logic.isAnd(candidate));
   auto conjuncts = TermUtils(logic).getTopLevelConjuncts(candidate);
   for (int i = 0; i < conjuncts.size();) {
       PTRef conjunct = conjuncts[i];
       conjuncts[i] = conjuncts.last();
       conjuncts.pop();
       if (checkWellFounded(logic.mkAnd(conjuncts),logic, vars)) {
           continue;
       } else {
           conjuncts.push(conjuncts[i]);
           conjuncts[i] = conjunct;
           i++;
       }
   }
   return logic.mkAnd(conjuncts);
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

PTRef shiftOnlyNextVars(PTRef formula, const std::vector<PTRef> & vars, Logic & logic) {
    TermUtils::substitutions_map varSubstitutions;
    for (uint32_t i = 0u; i < vars.size(); ++i) {
        varSubstitutions.insert(
            {TimeMachine(logic).sendVarThroughTime(vars[i], 1), TimeMachine(logic).sendVarThroughTime(vars[i], 2)});
    }
    return TermUtils(logic).varSubstitute(formula, varSubstitutions);
}

// This function extracts well-founded disjuncts from the interpolant
vec<PTRef> extractWellFoundedCandidate(PTRef itp, PTRef sink, ArithLogic & logic, const std::vector<PTRef> & vars) {
    SMTSolver smt_solver(logic, SMTSolver::WitnessProduction::NONE);

    auto sink_disjuncts = TermUtils(logic).getTopLevelDisjuncts(dnfize(logic.mkNot(sink), logic));
    PTRef dnfized_interpolant = dnfize(itp, logic);
    vec<PTRef> candidates = TermUtils(logic).getTopLevelDisjuncts(dnfized_interpolant);
    vec<PTRef> strictCandidates;
    for (auto cand : candidates) {
        smt_solver.resetSolver();
        smt_solver.assertProp(cand);
        if (smt_solver.check() == SMTSolver::Answer::UNSAT) { continue; }

        PTRef simpl_cand = TermUtils(logic).simplifyMax(cand);
        if (checkWellFounded(cand, logic, vars)) {
            // std::cout << "Wellfounded: " << logic.pp(simpl_cand) << std::endl;
            // std::cout << "Houdini: " << logic.pp(houdiniCheck(simpl_cand, logic, vars)) << std::endl;
            strictCandidates.push(houdiniCheck(simpl_cand, logic, vars));
        } else {
            for (auto sink_cand : sink_disjuncts) {
                smt_solver.resetSolver();
                smt_solver.assertProp(logic.mkAnd(sink_cand, simpl_cand));
                if (smt_solver.check() == SMTSolver::Answer::SAT &&
                checkWellFounded(logic.mkAnd(sink_cand, simpl_cand), logic, vars)) {
                    // std::cout << "Wellfounded: " << logic.pp(simpl_cand) << std::endl;
                    // std::cout << "Houdini: " << logic.pp(houdiniCheck(simpl_cand, logic, vars)) << std::endl;
                    // TODO: Maybe I can weaken recieved candidate using some kind of houdini, dropping not needed
                    // conjuncts
                    // TODO: Particularly, I can remove all equalities (also ones that are done via <= && >=)
                    strictCandidates.push(TermUtils(logic).simplifyMax(logic.mkAnd(sink_cand, simpl_cand)));
                }
            }
        }
    }
    return strictCandidates;
}

ReachabilityNonterm::Answer ReachabilityNonterm::run(TransitionSystem const & ts) {
    auto vars = ts.getStateVars();
    ArithLogic & logic = dynamic_cast<ArithLogic &>(ts.getLogic());
    PTRef init = ts.getInit();
    PTRef transition = ts.getTransition();
    uint nunsafe = 0;
    uint nsafe = 0;
    if (checkWellFounded(transition, logic, vars)) return Answer::YES;
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
    // Constructing x' != x''
    for (uint32_t i = 0u; i < vars.size(); ++i) {
        detSubstitutions.insert(
            {TimeMachine(logic).sendVarThroughTime(vars[i], 1), TimeMachine(logic).sendVarThroughTime(vars[i], 2)});
        neq.push(logic.mkNot(logic.mkEq(TimeMachine(logic).sendVarThroughTime(vars[i], 1),
                                        TimeMachine(logic).sendVarThroughTime(vars[i], 2))));
    }
    PTRef newTransition = TermUtils(logic).varSubstitute(transition, detSubstitutions);
    // Tr(x,x') /\ Tr(x, x'') /\ ! x' = x''
    detChecker.assertProp(logic.mkAnd({transition, newTransition, logic.mkOr(neq)}));
    bool DETERMINISTIC_TRANSITION = false;
    if (detChecker.check() == SMTSolver::Answer::UNSAT) {
        std::cout << "DETERMINISTIC;" << std::endl;
        DETERMINISTIC_TRANSITION = true;
    }
    // This is vector that stores candidates for Disjunctively Well-Founded Transition Invariant
    vec<PTRef> strictCandidates;
    // Main nonterm-checking loop

    std::cout << "Init: " << logic.pp(init) << std::endl;
    std::cout << "Transition: " << logic.pp(transition) << std::endl;
    std::cout << "Sink: " << logic.pp(sink) << std::endl;
    while (true) {
        // TODO: Do smth with exponential transition growth in some cases via blocks...
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
            PTRef terminatingStates = QuantifierElimination(logic).keepOnly(
                logic.mkAnd({logic.mkAnd(formulas), TimeMachine(logic).sendFlaThroughTime(sink, num)}), vars);
            PTRef transitions =
                logic.mkAnd({init, logic.mkAnd(formulas), TimeMachine(logic).sendFlaThroughTime(sink, num)});

            // Get the satisfying model of the trace.
            // It is needed to detect nondeterminism
            SMTSolver SMTsolver(logic, SMTSolver::WitnessProduction::NONE);
            SMTsolver.assertProp(transitions);
            if (SMTsolver.check() != SMTSolver::Answer::SAT) {
                assert(false);
                return Answer::ERROR;
            }

            SMTsolver.resetSolver();
            SMTsolver.assertProp(logic.mkAnd({logic.mkAnd(init, terminatingStates), logic.mkAnd(formulas),
                                              logic.mkNot(TimeMachine(logic).sendFlaThroughTime(sink, num))}));
            PTRef Result = TimeMachine(logic).sendFlaThroughTime(sink, num);

            uint j = 0;
            // Traversing trace from the Bad to Init, detecting the last transition where some variables
            // were assigned nondetermenistically (Only if it is possible to reach some states other then sink in n trs)
            if (!DETERMINISTIC_TRANSITION && SMTsolver.check() == SMTSolver::Answer::SAT) {
                for (j = num; j > 0; j--) {
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
                    SMTsolver.assertProp(logic.mkAnd(
                        {Base, TimeMachine(logic).sendFlaThroughTime(transition, j - 1), logic.mkNot(Result)}));

                    // It means that this transition was nondetermenistic, since
                    // using transition from the states that guaranteed to reach termination in n-j+1 transitions
                    // it is possible to reach states which are not guaranteed to reach termination in n-j transitions
                    if (SMTsolver.check() == SMTSolver::Answer::SAT) {
                        // We restrict the nondeterminism that leads to the termination, removing the states
                        // which are guaranteed to terminate in n-j transitions
                        break;
                    } else {
                        Result = Base;
                    }
                }
            }

            PTRef temp_tr = transition;
            if (j == 0) {
                init = logic.mkAnd(init, logic.mkNot(terminatingStates));
            } else {
                PTRef block = TimeMachine(logic).sendFlaThroughTime(Result, -j + 1);
                assert(block != logic.getTerm_true());
                transition = logic.mkAnd(transition, logic.mkNot(block));
            }
            SMTsolver.resetSolver();
            SMTsolver.assertProp(logic.mkAnd(init, transition));
            // We check if init state is blocked (it's impossible to make a transition from initial state)
            // When it is the case, TS is terminating
            if (SMTsolver.check() == SMTSolver::Answer::UNSAT) { return Answer::YES; }
            if (num > 0) {
                // Calculate the states that are guaranteed to terminate within num transitions:
                // Tr^n(x,x') /\ not Sink(x') - is a formula, which can be satisfied by any x which can not terminate
                // after n transitions
                // PTRef R = QuantifierElimination(logic).keepOnly(logic.mkAnd(logic.mkAnd(formulas),
                // TimeMachine(logic).sendFlaThroughTime(sink, num )),vars);

                // States that can reach non-terminating state in n transitions:
                PTRef F = QuantifierElimination(logic).keepOnly(
                    logic.mkAnd(logic.mkAnd(formulas), logic.mkNot(TimeMachine(logic).sendFlaThroughTime(sink, num))),
                    vars);
                // States that can not reach non-terminating state in <= n transitions:
                PTRef T = logic.mkNot(F);

                SMTsolver.resetSolver();
                SMTsolver.assertProp(logic.mkAnd(init, F));
                // If no initial states can reach nonterminating states in n transitions, then they won't be able to do
                // it in n+1 => system terminates
                if (SMTsolver.check() == SMTSolver::Answer::UNSAT) return Answer::YES;

                // assume R = set of states which can terminate in n transitions
                // R /\ T = \bot - so there are no states which are both:
                // 1: Can terminate in n transitions
                // 2: Can not reach non-terminating state in n transitions
                // There exist some extra cases, for example:
                // x>0 /\ x' = x-3 /\ x' = x-6 where there does not exist a state that can reach termination in 2
                // transitions, but not in one transition, but generally in a lot of cases it is the situation
                // TODO: I need to think how to distinguish it

                SMTsolver.resetSolver();
                SMTsolver.assertProp(logic.mkAnd({T, temp_tr, TimeMachine(logic).sendFlaThroughTime(sink, num)}));

                // This check guarantees the states T (states that cannot reach nonterminating states in n transition)
                // contain the states that terminate in at least one transition (otherwise system is nonterminating)
                // because there doesn't exist state that can reach sink states.
                if (SMTsolver.check() == SMTSolver::Answer::UNSAT) { return Answer::NO; }

                // Start buiding the trace that reaches sink states
                vec<PTRef> eq_vars;
                // Constructing vectors of equations x^(j-1) = x^(j)
                for (auto var : vars) {
                    PTRef curr = TimeMachine(logic).sendVarThroughTime(var, 0);
                    PTRef next = TimeMachine(logic).sendVarThroughTime(var, 1);
                    eq_vars.push(logic.mkEq(curr, next));
                }
                std::vector<PTRef> deterministic_trace{temp_tr};
                PTRef id = logic.mkAnd(eq_vars);
                for (uint k = 1; k < num; k++) {
                    // For every transition deterministic trace is updated, adding an Id or Tr
                    // This is needed so that Interpolant overapproximates 1 <= n <= num transitions
                    deterministic_trace.push_back(
                        TimeMachine(logic).sendFlaThroughTime(logic.mkOr(temp_tr, logic.mkAnd(eq_vars)), k));
                }
                std::vector<PTRef> checked_states;
                // This if calculates the states reachable in 1 <= n <= num-1 transitions
                if (num > 1) {
                    vec<PTRef> temp_vars;
                    for (auto var : vars) {
                        temp_vars.push(TimeMachine(logic).sendVarThroughTime(var, num - 1));
                    }
                    checked_states.push_back(TimeMachine(logic).sendFlaThroughTime(
                        QuantifierElimination(logic).keepOnly(logic.mkAnd(T, logic.mkAnd(deterministic_trace)),
                                                              temp_vars),
                        1));
                }
                checked_states.push_back(TimeMachine(logic).sendFlaThroughTime(sink, num));
                // sink is updated, representing states that are guaranteed to reach termination
                PTRef temp_sink = logic.mkOr(checked_states);
                SMTSolver smt_solver(logic, SMTSolver::WitnessProduction::ONLY_INTERPOLANTS);
                smt_solver.assertProp(logic.mkAnd(deterministic_trace));
                smt_solver.push();
                smt_solver.assertProp(logic.mkAnd(T, logic.mkNot(temp_sink)));
                // TODO: Think why this constraint does not work
                // sink = TimeMachine(logic).sendFlaThroughTime(temp_sink, -num);

                // Formula should be unsat, because \lnot(sink) are the states which can't be reached after n
                // transitions
                if (smt_solver.check() == SMTSolver::Answer::UNSAT) {
                    auto itpContext = smt_solver.getInterpolationContext();
                    vec<PTRef> itps;
                    ipartitions_t mask = 1;
                    itpContext->getSingleInterpolant(itps, mask);
                    assert(itps.size() == 1);
                    // Extracting Itp(Tr /\ ... /\ Tr, Init /\ not Sink) - overapproximation of 1 <= n <= num
                    // transitions
                    PTRef itp = itps[0];

                    TermUtils::substitutions_map varSubstitutions;
                    for (uint32_t i = 0u; i < vars.size(); ++i) {
                        varSubstitutions.insert({TimeMachine(logic).sendVarThroughTime(vars[i], num),
                                                 TimeMachine(logic).sendVarThroughTime(vars[i], 1)});
                    }
                    // Then interpolant is translated, so it would correspond to transition relation Itp(x,x')
                    itp = TermUtils(logic).varSubstitute(itp, varSubstitutions);
                    // std::cout << "Itp: " << logic.pp(itp) << std::endl;
                    // Check if some part of interpolant is transition invariant
                    auto newCands = extractWellFoundedCandidate(itp, sink, logic, vars);
                    if (newCands.size() == 0) continue;

                    for (auto cand : newCands) {
                        strictCandidates.push(cand);
                    }
                    PTRef inv = logic.mkOr(strictCandidates);
                    // TODO: Even when Considered Candidate is not inductive invariant, all states that can terminate
                    // via it should
                    // TODO: be removed possibly, as any state for which Transition Invariant holds is guaranteed to
                    // terminate
                    // TODO: to do it, we can check for which states inv is in fact transition invariant, and remove
                    // those.
                    // TODO: Can be checked via:
                    // TODO: TrInv /\ Tr => TrInv, by QE-ing everything except for x
                    smt_solver.resetSolver();
                    // Check if inv is Transition Invariant
                    SMTSolver smt_checker(logic, SMTSolver::WitnessProduction::NONE);
                    smt_checker.assertProp(
                        logic.mkAnd({logic.mkOr(inv, id), TimeMachine(logic).sendFlaThroughTime(temp_tr, 1),
                                     logic.mkNot(shiftOnlyNextVars(inv, vars, logic))}));
                    if (smt_checker.check() == SMTSolver::Answer::UNSAT) {
                        return Answer::YES;
                    } else {
                        // TODO: Compute all states, for which inv would be transition invariant!
                        // TODO: These states can be excluded from the search and added to sink, since those states are
                        // guaranteed to
                        //  lead to the termination!!
                        //  Left-restricted
                        smt_checker.resetSolver();
                        smt_checker.assertProp(
                            logic.mkAnd({init, logic.mkOr(inv, id), TimeMachine(logic).sendFlaThroughTime(temp_tr, 1),
                                         logic.mkNot(shiftOnlyNextVars(inv, vars, logic))}));
                        if (smt_checker.check() == SMTSolver::Answer::UNSAT) {
                            std::cout << "Left"  << std::endl;
                            return Answer::YES;
                        }

                        // Right-restricted
                        smt_checker.resetSolver();
                        smt_checker.assertProp(
                            logic.mkAnd({temp_tr, TimeMachine(logic).sendFlaThroughTime(logic.mkOr(inv, id), 1),
                                         TimeMachine(logic).sendFlaThroughTime(sink, 2),
                                         logic.mkNot(shiftOnlyNextVars(inv, vars, logic))}));
                        if (smt_checker.check() == SMTSolver::Answer::UNSAT) {
                            PTRef preTransition = QuantifierElimination(logic).keepOnly(
                                logic.mkAnd(logic.mkOr(inv, id), TimeMachine(logic).sendFlaThroughTime(sink, 1)), vars);
                            PTRef check = logic.mkAnd(preTransition, init);
                            smt_checker.resetSolver();
                            smt_checker.assertProp(check);

                            if (smt_checker.check() == SMTSolver::Answer::UNSAT) { return Answer::NO; }
                            else {
                                auto graph = constructHyperGraph(init, transition, logic.mkNot(preTransition), logic,
                                vars); auto engine = EngineFactory(logic,
                                witnesses).getEngine(witnesses.getOrDefault(Options::ENGINE, "spacer")); if
                                (engine->solve(*graph).getAnswer() == VerificationAnswer::UNSAFE) {
                                    return Answer::NO;
                                }
                            }
                        }
                    }
                } else {
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
            PTRef inv = logic.getTerm_true();
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