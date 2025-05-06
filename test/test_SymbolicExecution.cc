/*
 * Copyright (c) 2025, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "TestTemplate.h"
#include "Validator.h"
#include "engine/SymbolicExecution.h"
#include "graph/ChcGraphBuilder.h"
#include <gtest/gtest.h>

class SETest : public LIAEngineTest {
};

TEST_F(SETest, test_Simple_Unsafe) {
    options.addOption(Options::COMPUTE_WITNESS, "true");
    SymRef inv_sym = mkPredicateSymbol("Inv", {intSort()});
    PTRef inv = instantiatePredicate(inv_sym, {x});
    PTRef invp = instantiatePredicate(inv_sym, {xp});
    std::vector<ChClause> clauses{
        { // x' = 0 => Inv(x')
            ChcHead{UninterpretedPredicate{invp}},
            ChcBody{{logic->mkEq(xp, zero)}, {}}
        },
        { // Inv(x) & x' = x + 1 => Inv(x')
            ChcHead{UninterpretedPredicate{invp}},
            ChcBody{{logic->mkEq(xp, logic->mkPlus(x, one))}, {UninterpretedPredicate{inv}}}
        },
        { // Inv(x) & x > 1 => false
            ChcHead{UninterpretedPredicate{logic->getTerm_false()}},
            ChcBody{{logic->mkGt(x, one)}, {UninterpretedPredicate{inv}}}
        }
    };

    SymbolicExecution engine(*logic, options);
    solveSystem(clauses, engine, VerificationAnswer::UNSAFE);
}

TEST_F(SETest, test_Simple_Safe) {
    SymRef inv_sym = mkPredicateSymbol("Inv", {intSort(), intSort()});
    PTRef inv = instantiatePredicate(inv_sym, {x, y});
    PTRef invp = instantiatePredicate(inv_sym, {xp, yp});
    std::vector<ChClause> clauses{
        { // x' = y' => Inv(x', y')
            ChcHead{UninterpretedPredicate{invp}},
            ChcBody{{logic->mkEq(xp, yp)}, {}}
        },
        { // Inv(x,y) and x' = x + 1 and y' = y + 1 => Inv(x', y')
            ChcHead{UninterpretedPredicate{invp}},
            ChcBody{{logic->mkAnd(logic->mkEq(xp, logic->mkPlus(x, one)), logic->mkEq(yp, logic->mkPlus(y, one)))}, {UninterpretedPredicate{inv}}}
        },
        { // Inv(x, y) and x != y => false
            ChcHead{UninterpretedPredicate{logic->getTerm_false()}},
            ChcBody{{logic->mkNot(logic->mkEq(x, y))}, {UninterpretedPredicate{inv}}}
        }
    };

    SymbolicExecution engine(*logic, options);
    solveSystem(clauses, engine, VerificationAnswer::SAFE, false);
}

TEST_F(SETest, test_BeyondTransitionSystem_Unsafe)
{
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
    SymbolicExecution engine(*logic, options);
    solveSystem(clauses, engine, VerificationAnswer::UNSAFE);
}