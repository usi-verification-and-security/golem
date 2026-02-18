/*
 * Copyright (c) 2021-2026, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include <gtest/gtest.h>
#include "TermUtils.h"

#include "utils/SmtSolver.h"

using namespace golem;

namespace{
bool implies(Logic & logic, PTRef antecedent, PTRef consequent) {
    SMTSolver solver(logic);
    solver.assertProp(logic.mkNot(logic.mkImpl(antecedent, consequent)));
    auto res = solver.check();
    return res == SMTSolver::Answer::UNSAT;
}
}


class NormalFormsTest : public ::testing::Test {
protected:
    ArithLogic logic {opensmt::Logic_t::QF_LRA};
    PTRef x;
    PTRef b;
    PTRef a;
    PTRef c;
    PTRef na;
    PTRef nb;
    PTRef nc;
    PTRef zero;
    PTRef one;
    NormalFormsTest() {
        x = logic.mkRealVar("x");
        a = logic.mkBoolVar("a");
        b = logic.mkBoolVar("b");
        c = logic.mkBoolVar("c");
        na = logic.mkNot(a);
        nb = logic.mkNot(b);
        nc = logic.mkNot(c);
        zero = logic.getTerm_RealZero();
        one = logic.getTerm_RealOne();
    }
};

TEST_F(NormalFormsTest, test_NNF_Atom) {
    PTRef atom = logic.mkLeq(x, zero);
    PTRef nnf = TermUtils(logic).toNNF(atom);
    ASSERT_EQ(atom, nnf);
}

TEST_F(NormalFormsTest, test_NNF_NegatedConjunction) {
    PTRef atom = logic.mkLeq(x, zero);
    PTRef conj = logic.mkAnd(atom, b);
    PTRef fla = logic.mkNot(conj);
    PTRef nnf = TermUtils(logic).toNNF(fla);
    ASSERT_EQ(nnf, logic.mkOr(logic.mkNot(atom), logic.mkNot(b)));
}

TEST_F(NormalFormsTest, test_NNF_NegatedDisjunction) {
    PTRef atom = logic.mkLeq(x, zero);
    PTRef disj = logic.mkOr(atom, b);
    PTRef fla = logic.mkNot(disj);
    PTRef nnf = TermUtils(logic).toNNF(fla);
    ASSERT_EQ(nnf, logic.mkAnd(logic.mkNot(atom), logic.mkNot(b)));
}

TEST_F(NormalFormsTest, test_NNF_BoolEquality) {
    PTRef eq = logic.mkEq(a,b);
    PTRef nnf = TermUtils(logic).toNNF(eq);
    ASSERT_NE(nnf, eq);
    EXPECT_EQ(nnf, logic.mkAnd(
        logic.mkOr(a, logic.mkNot(b)),
        logic.mkOr(b, logic.mkNot(a))
    ));
}

TEST_F(NormalFormsTest, test_NNF_NestedNegatedDisjunction) {
    //  (= (= a b) c) && (a || ~b)

    PTRef eq = logic.mkEq(a, b);
    PTRef eq2 = logic.mkEq(eq, c);
    PTRef disj = logic.mkOr(a, nb);
    PTRef fla = logic.mkAnd(eq2, disj);
    PTRef nnf = TermUtils(logic).toNNF(fla);

    ASSERT_TRUE(implies(logic, fla, nnf));
    ASSERT_TRUE(implies(logic, nnf, fla));
}

TEST_F(NormalFormsTest, test_DNF_Distribution) {
    // (a && (b || c))  ==>  ((a && b) || (a && c))
    PTRef const fla = logic.mkAnd (a, logic.mkOr(b,c));
    PTRef const dnf = TermUtils(logic).toDNF(fla);
    PTRef const expected = logic.mkOr(logic.mkAnd(a, b), logic.mkAnd(a, c));
    EXPECT_EQ(expected, dnf);
}