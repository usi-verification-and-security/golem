//
// Created by Martin Blicha on 24.08.21.
//

#include <gtest/gtest.h>
#include "TermUtils.h"

bool contains(vec<PTRef> const & v, PTRef p) {
    for (PTRef t : v) {
        if (p == t) { return true; }
    }
    return false;
}

class TermUtils_Test : public ::testing::Test {
protected:
    Logic logic;
    TermUtils utils;
    PTRef a;
    PTRef b;
    PTRef c;
    PTRef na;
    PTRef nb;
    PTRef nc;

    TermUtils_Test() : logic{}, utils{logic} {
        a = logic.mkBoolVar("a");
        b = logic.mkBoolVar("b");
        c = logic.mkBoolVar("c");
        na = logic.mkNot(a);
        nb = logic.mkNot(b);
        nc = logic.mkNot(c);
    }
};

TEST_F(TermUtils_Test, test_TopLevelConjuncts_SingleTerm) {
    PTRef fla = a;
    auto conjunctions = utils.getTopLevelConjuncts(fla);
    ASSERT_EQ(conjunctions.size(), 1);
    EXPECT_EQ(conjunctions[0], a);
}

TEST_F(TermUtils_Test, test_TopLevelConjuncts_SingleNegatedTerm) {
    PTRef fla = logic.mkNot(a);
    auto conjunctions = utils.getTopLevelConjuncts(fla);
    ASSERT_EQ(conjunctions.size(), 1);
    EXPECT_EQ(conjunctions[0], fla);
}

TEST_F(TermUtils_Test, test_TopLevelConjuncts_SingleDisjunction) {
    PTRef fla = logic.mkOr(a, b);
    auto conjunctions = utils.getTopLevelConjuncts(fla);
    ASSERT_EQ(conjunctions.size(), 1);
    EXPECT_EQ(conjunctions[0], fla);
}

TEST_F(TermUtils_Test, test_TopLevelConjuncts_NestedOneLevel) {
    PTRef disj = logic.mkOr(a,b);
    PTRef fla = logic.mkNot(disj);
    auto conjunctions = utils.getTopLevelConjuncts(fla);
    ASSERT_EQ(conjunctions.size(), 2);
    EXPECT_TRUE(contains(conjunctions, na));
    EXPECT_TRUE(contains(conjunctions, nb));
}

TEST_F(TermUtils_Test, test_TopLevelConjuncts_NestedTwoLevels) {
    PTRef nested = logic.mkOr(a,b);
    PTRef fla = logic.mkNot(logic.mkOr(nested, c));
    auto conjunctions = utils.getTopLevelConjuncts(fla);
    ASSERT_EQ(conjunctions.size(), 3);
    EXPECT_TRUE(contains(conjunctions, na));
    EXPECT_TRUE(contains(conjunctions, nb));
    EXPECT_TRUE(contains(conjunctions, nc));
}

TEST_F(TermUtils_Test, test_TopLevelDisjuncts_SingleTerm) {
    PTRef fla = a;
    auto disjunctions = utils.getTopLevelDisjuncts(fla);
    ASSERT_EQ(disjunctions.size(), 1);
    EXPECT_EQ(disjunctions[0], a);
}

TEST_F(TermUtils_Test, test_TopLevelDisjuncts_SingleNegatedTerm) {
    PTRef fla = logic.mkNot(a);
    auto disjunctions = utils.getTopLevelDisjuncts(fla);
    ASSERT_EQ(disjunctions.size(), 1);
    EXPECT_EQ(disjunctions[0], fla);
}

TEST_F(TermUtils_Test, test_TopLevelDisjuncts_SingleConjunction) {
    PTRef fla = logic.mkAnd(a, b);
    auto disjunctions = utils.getTopLevelDisjuncts(fla);
    ASSERT_EQ(disjunctions.size(), 1);
    EXPECT_EQ(disjunctions[0], fla);
}

TEST_F(TermUtils_Test, test_TopLevelDisjuncts_NestedOneLevel) {
    PTRef disj = logic.mkAnd(a,b);
    PTRef fla = logic.mkNot(disj);
    auto disjunctions = utils.getTopLevelDisjuncts(fla);
    ASSERT_EQ(disjunctions.size(), 2);
    EXPECT_TRUE(contains(disjunctions, na));
    EXPECT_TRUE(contains(disjunctions, nb));
}

TEST_F(TermUtils_Test, test_TopLevelDisjuncts_NestedTwoLevels) {
    PTRef nested = logic.mkAnd(a,b);
    PTRef fla = logic.mkNot(logic.mkAnd(nested, c));
    auto disjunctions = utils.getTopLevelDisjuncts(fla);
    ASSERT_EQ(disjunctions.size(), 3);
    EXPECT_TRUE(contains(disjunctions, na));
    EXPECT_TRUE(contains(disjunctions, nb));
    EXPECT_TRUE(contains(disjunctions, nc));
}