/*
 * Copyright (c) 2022, Konstantin Britikov <britikovki@gmail.com>
 * Copyright (c) 2022, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "TestTemplate.h"
#include "engine/IMC.h"



class IMCTest : public LIAEngineTest {};


TEST_F(IMCTest, test_IMC_simple) {
    Options options;
    options.addOption(Options::COMPUTE_WITNESS, "true");
    SymRef s1 = mkPredicateSymbol("s1", {intSort()});
    PTRef current = instantiatePredicate(s1, {x});
    PTRef next = instantiatePredicate(s1, {xp});
    std::vector<ChClause> clauses {
        { // x' = 0 => s1(x')
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{{logic->mkEq(xp, zero)}, {}}
        },
        { // s1(x) and x' = x + 1 => s1(x')
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{{logic->mkEq(xp, logic->mkPlus(x, one))}, {UninterpretedPredicate{current}}}
        },
        { // s1(x) and x > 1 => false
            ChcHead{UninterpretedPredicate{logic->getTerm_false()}},
            ChcBody{{logic->mkGt(x, one)}, {UninterpretedPredicate{current}}}
        }
    };
    IMC imc(*logic, options);
    solveSystem(clauses, imc, VerificationAnswer::UNSAFE, true);
}


TEST_F(IMCTest, test_IMC_simple_safe) {
    Options options;
    options.addOption(Options::COMPUTE_WITNESS, "true");
    SymRef s1 = mkPredicateSymbol("s1", {intSort()});
    PTRef current = instantiatePredicate(s1, {x});
    PTRef next = instantiatePredicate(s1, {xp});

    std::vector<ChClause> clauses{
        { // x = 0 => S1(x)
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{{logic->mkEq(xp, zero)}, {}}
        },
        { // S1(x) and x' = x + 1 => S1(x')
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{{logic->mkEq(xp, logic->mkPlus(x, one))}, {UninterpretedPredicate{current}}}
        },
        { // S1(x) and x < 0 => false
            ChcHead{UninterpretedPredicate{logic->getTerm_false()}},
            ChcBody{{logic->mkLt(x, zero)}, {UninterpretedPredicate{current}}}
        }
    };
    IMC engine(*logic, options);
    solveSystem(clauses, engine, VerificationAnswer::SAFE, true);
}

TEST_F(IMCTest, test_IMC_moreInductionForward_safe) {
    Options options;
    options.addOption(Options::COMPUTE_WITNESS, "true");
    SymRef s1 = mkPredicateSymbol("s1", {intSort()});
    PTRef current = instantiatePredicate(s1, {x});
    PTRef next = instantiatePredicate(s1, {xp});
    // x = 0 => S1(x)
    // S1(x) and x' = ite(x = 10, 0, x + 1) => S1(x')
    // S1(x) and x = 15 => false
    std::vector<ChClause> clauses{
        {
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{{logic->mkEq(xp, zero)}, {}}
        },
        {
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{{logic->mkEq(xp, logic->mkIte(logic->mkEq(x, logic->mkIntConst(10)), zero, logic->mkPlus(x, one)))}, {UninterpretedPredicate{current}}}
        },
        {
            ChcHead{UninterpretedPredicate{logic->getTerm_false()}},
            ChcBody{{logic->mkEq(x, logic->mkIntConst(15))}, {UninterpretedPredicate{current}}}
        }
    };
    IMC engine(*logic, options);
    solveSystem(clauses, engine, VerificationAnswer::SAFE, true);
}

TEST_F(IMCTest, test_IMC_moreInductionBackward_safe) {
    Options options;
    options.addOption(Options::COMPUTE_WITNESS, "true");
    SymRef s1 = mkPredicateSymbol("s1", {intSort()});
    PTRef current = instantiatePredicate(s1, {x});
    PTRef next = instantiatePredicate(s1, {xp});
    // x = 0 => S1(x)
    // S1(x) and x' = ite(x = 5, 0, x + 1) => S1(x')
    // S1(x) and x = 15 => false
    std::vector<ChClause> clauses{
        {
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{{logic->mkEq(xp, zero)}, {}}
        },
        {
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{{logic->mkEq(xp, logic->mkIte(logic->mkEq(x, logic->mkIntConst(5)), zero, logic->mkPlus(x, one)))}, {UninterpretedPredicate{current}}}
        },
        {
            ChcHead{UninterpretedPredicate{logic->getTerm_false()}},
            ChcBody{{logic->mkEq(x, logic->mkIntConst(15))}, {UninterpretedPredicate{current}}}
        }
    };
    IMC engine(*logic, options);
    solveSystem(clauses, engine, VerificationAnswer::SAFE, true);
}

TEST_F(IMCTest, test_IMC_BeyondTransitionSystemWithAuxVar_unsafe)
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
    // S1(x,y) and x > 2 => S2(x,y)
    // S2(x,y) and y' = y + 1 => S2(x,y')
    // S2(x,y) and y > 2 => S1(x,y)
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
            ChcBody{{logic->mkGt(x, logic->mkIntConst(2))}, {UninterpretedPredicate{current1}}}
        },
        {
            ChcHead{UninterpretedPredicate{next2}},
            ChcBody{{logic->mkAnd(logic->mkEq(yp, logic->mkPlus(y, one)), logic->mkEq(xp, x))}, {UninterpretedPredicate{current2}}}
        },
        {
            ChcHead{UninterpretedPredicate{current1}},
            ChcBody{{logic->mkGt(y, logic->mkIntConst(2))}, {UninterpretedPredicate{current2}}}
        },
        {
            ChcHead{UninterpretedPredicate{logic->getTerm_false()}},
            ChcBody{{logic->mkAnd(logic->mkGt(y, c), logic->mkGt(c, x))}, {UninterpretedPredicate{current1}}}
        }};
    IMC engine(*logic, options);
    solveSystem(clauses, engine, VerificationAnswer::UNSAFE, true);
}

TEST_F(IMCTest, test_IMC_BeyondTransitionSystem_safe)
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
    // S1(x,y) and x < 0 => false
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
            ChcBody{{logic->mkLt(x, zero)}, {UninterpretedPredicate{current1}}}
        }};
    IMC engine(*logic, options);
    solveSystem(clauses, engine, VerificationAnswer::SAFE, true);
}