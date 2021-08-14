//
// Created by Martin Blicha on 10.06.21.
//

#include <gtest/gtest.h>
#include "TermUtils.h"

class NNFTest : public ::testing::Test {
protected:
    LRALogic logic;
    PTRef x;
    PTRef b;
    PTRef a;
    PTRef zero;
    PTRef one;
    NNFTest() {
        x = logic.mkNumVar("x");
        a = logic.mkBoolVar("a");
        b = logic.mkBoolVar("b");
        zero = logic.getTerm_NumZero();
        one = logic.getTerm_NumOne();
    }
};

TEST_F(NNFTest, test_Atom) {
    PTRef atom = logic.mkNumLeq(x, zero);
    PTRef nnf = TermUtils(logic).toNNF(atom);
    ASSERT_EQ(atom, nnf);
}

TEST_F(NNFTest, test_NegatedConjunction) {
    PTRef atom = logic.mkNumLeq(x, zero);
    PTRef conj = logic.mkAnd(atom, b);
    PTRef fla = logic.mkNot(conj);
    PTRef nnf = TermUtils(logic).toNNF(fla);
    ASSERT_EQ(nnf, logic.mkOr(logic.mkNot(atom), logic.mkNot(b)));
}

TEST_F(NNFTest, test_NegatedDisjunction) {
    PTRef atom = logic.mkNumLeq(x, zero);
    PTRef disj = logic.mkOr(atom, b);
    PTRef fla = logic.mkNot(disj);
    PTRef nnf = TermUtils(logic).toNNF(fla);
    ASSERT_EQ(nnf, logic.mkAnd(logic.mkNot(atom), logic.mkNot(b)));
}

TEST_F(NNFTest, test_BoolEquality) {
    PTRef eq = logic.mkEq(a,b);
    PTRef nnf = TermUtils(logic).toNNF(eq);
    ASSERT_NE(nnf, eq);
    EXPECT_EQ(nnf, logic.mkAnd(
        logic.mkOr(a, logic.mkNot(b)),
        logic.mkOr(b, logic.mkNot(a))
    ));
}
