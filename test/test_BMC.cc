/*
 * Copyright (c) 2021-2025, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "TestTemplate.h"
#include "Validator.h"
#include "engine/Bmc.h"
#include "graph/ChcGraphBuilder.h"
#include <gtest/gtest.h>

class BMCTest : public LIAEngineTest {
};

TEST(BMC_test, test_BMC_simple) {
    ArithLogic logic {opensmt::Logic_t::QF_LIA};
    Options options;
    options.addOption(Options::LOGIC, "QF_LIA");
    options.addOption(Options::COMPUTE_WITNESS, "true");
    SymRef s1 = logic.declareFun("s1", logic.getSort_bool(), {logic.getSort_int()});
    PTRef x = logic.mkIntVar("x");
    PTRef xp = logic.mkIntVar("xp");
    PTRef current = logic.mkUninterpFun(s1, {x});
    PTRef next = logic.mkUninterpFun(s1, {xp});
    ChcSystem system;
    system.addUninterpretedPredicate(s1);
    system.addClause( // x' = 0 => s1(x')
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{{logic.mkEq(xp, logic.getTerm_IntZero())}, {}});
    system.addClause( // s1(x) and x' = x + 1 => s1(x')
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{{logic.mkEq(xp, logic.mkPlus(x, logic.getTerm_IntOne()))}, {UninterpretedPredicate{current}}}
    );
    system.addClause( // s1(x) and x > 1 => false
            ChcHead{UninterpretedPredicate{logic.getTerm_false()}},
            ChcBody{{logic.mkGt(x, logic.getTerm_IntOne())}, {UninterpretedPredicate{current}}}
    );
    auto normalizedSystem = Normalizer(logic).normalize(system);
    auto hypergraph = ChcGraphBuilder(logic).buildGraph(normalizedSystem);
    ASSERT_TRUE(hypergraph->isNormalGraph());
    auto graph = hypergraph->toNormalGraph();
    BMC bmc(logic, options);
    auto res = bmc.solve(*graph);
    auto answer = res.getAnswer();
    ASSERT_EQ(answer, VerificationAnswer::UNSAFE);
    auto witness = res.getInvalidityWitness();
    auto validationResult = Validator(logic).validate(*hypergraph, res);
    ASSERT_EQ(validationResult, Validator::Result::VALIDATED);
}

TEST_F(BMCTest, test_BMC_BeyondTransitionSystem)
{
    Options options;
    options.addOption(Options::LOGIC, "QF_LIA");
    options.addOption(Options::COMPUTE_WITNESS, "true");
    SymRef s1 = mkPredicateSymbol("s1", {intSort(), intSort()});
    SymRef s2 = mkPredicateSymbol("s2", {intSort(), intSort()});
    PTRef current1 = instantiatePredicate(s1, {x,y});
    PTRef next1 = instantiatePredicate(s1, {xp,yp});
    PTRef current2 = instantiatePredicate(s2, {x,y});
    PTRef next2 = instantiatePredicate(s2, {xp,yp});
    // x = 0 and y = 0 => S1(x,y)
    // S1(x,y) and x' = x + 1 => S1(x',y)
    // S1(x,y) and x > 5 => S2(x,y)
    // S2(x,y) and y' = y + 1 => S2(x,y')
    // S2(x,y) and y > 5 => S1(x,y)
    // S1(x,y) and y > 0 and x = 10 => false
    std::vector<ChClause> clauses{
        {
            ChcHead{UninterpretedPredicate{next1}},
            ChcBody{{logic->mkAnd(logic->mkEq(xp, zero), logic->mkEq(yp, zero))}, {}}
        },
        {
            ChcHead{UninterpretedPredicate{next1}},
            ChcBody{{logic->mkAnd(logic->mkEq(xp, logic->mkPlus(x, one)), logic->mkEq(yp, y))}, {UninterpretedPredicate{current1}}}
        },
        {
            ChcHead{UninterpretedPredicate{current2}},
            ChcBody{{logic->mkGt(x, logic->mkIntConst(5))}, {UninterpretedPredicate{current1}}}
        },
        {
            ChcHead{UninterpretedPredicate{next2}},
            ChcBody{{logic->mkAnd(logic->mkEq(yp, logic->mkPlus(y, one)), logic->mkEq(xp, x))}, {UninterpretedPredicate{current2}}}
        },
        {
            ChcHead{UninterpretedPredicate{current1}},
            ChcBody{{logic->mkGt(y, logic->mkIntConst(5))}, {UninterpretedPredicate{current2}}}
        },
        {
            ChcHead{UninterpretedPredicate{logic->getTerm_false()}},
            ChcBody{{logic->mkAnd(logic->mkGt(y, zero), logic->mkEq(x, logic->mkIntConst(10)))}, {UninterpretedPredicate{current1}}}
        }};
    BMC engine(*logic, options);
    solveSystem(clauses, engine, VerificationAnswer::UNSAFE, true);
}

TEST_F(BMCTest, test_KIND_BeyondTransitionSystemWithAuxVar_unsafe)
{
    Options options;
    options.addOption(Options::LOGIC, "QF_LIA");
    options.addOption(Options::COMPUTE_WITNESS, "true");
    SymRef s1 = mkPredicateSymbol("s1", {intSort(), intSort()});
    SymRef s2 = mkPredicateSymbol("s2", {intSort(), intSort()});
    PTRef current1 = instantiatePredicate(s1, {x,y});
    PTRef next1 = instantiatePredicate(s1, {xp,yp});
    PTRef current2 = instantiatePredicate(s2, {x,y});
    PTRef next2 = instantiatePredicate(s2, {xp,yp});
    PTRef c = logic->mkIntVar("c");
    // x = 0 and y = 0 => S1(x,y)
    // S1(x,y) and x' = x + 1 => S1(x',y)
    // S1(x,y) and x > 5 => S2(x,y)
    // S2(x,y) and y' = y + 1 => S2(x,y')
    // S2(x,y) and y > 5 => S1(x,y)
    // S1(x,y) and y > c and c > x => false
    std::vector<ChClause> clauses{
        {
            ChcHead{UninterpretedPredicate{next1}},
            ChcBody{{logic->mkAnd(logic->mkEq(xp, zero), logic->mkEq(yp, zero))}, {}}
        },
        {
            ChcHead{UninterpretedPredicate{next1}},
            ChcBody{{logic->mkAnd(logic->mkEq(xp, logic->mkPlus(x, one)), logic->mkEq(yp, y))}, {UninterpretedPredicate{current1}}}
        },
        {
            ChcHead{UninterpretedPredicate{current2}},
            ChcBody{{logic->mkGt(x, logic->mkIntConst(5))}, {UninterpretedPredicate{current1}}}
        },
        {
            ChcHead{UninterpretedPredicate{next2}},
            ChcBody{{logic->mkAnd(logic->mkEq(yp, logic->mkPlus(y, one)), logic->mkEq(xp, x))}, {UninterpretedPredicate{current2}}}
        },
        {
            ChcHead{UninterpretedPredicate{current1}},
            ChcBody{{logic->mkGt(y, logic->mkIntConst(5))}, {UninterpretedPredicate{current2}}}
        },
        {
            ChcHead{UninterpretedPredicate{logic->getTerm_false()}},
            ChcBody{{logic->mkAnd(logic->mkGt(y, c), logic->mkGt(c, x))}, {UninterpretedPredicate{current1}}}
        }};
    BMC engine(*logic, options);
    solveSystem(clauses, engine, VerificationAnswer::UNSAFE, true);
}
