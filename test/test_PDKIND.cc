/*
 * Copyright (c) 2025, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "TestTemplate.h"
#include "engine/PDKind.h"

class PDKindTest : public LIAEngineTest {
};

TEST_F(PDKindTest, test_PDKIND_simple_safe)
{
    options.addOption(Options::LOGIC, "QF_LIA");
    options.addOption(Options::COMPUTE_WITNESS, "true");
    SymRef s1 = mkPredicateSymbol("s1", {intSort()});
    PTRef current = instantiatePredicate(s1, {x});
    PTRef next = instantiatePredicate(s1, {xp});
    // x = 0 => S1(x)
    // S1(x) and x' = x + 1 => S1(x')
    // S1(x) and x < 0 => false
    std::vector<ChClause> clauses{
        {
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{{logic->mkEq(xp, zero)}, {}}
        },
        {
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{{logic->mkEq(xp, logic->mkPlus(x, one))}, {UninterpretedPredicate{current}}}
        },
        {
            ChcHead{UninterpretedPredicate{logic->getTerm_false()}},
            ChcBody{{logic->mkLt(x, zero)}, {UninterpretedPredicate{current}}}
        }};
    PDKind engine(*logic, options);
    solveSystem(clauses, engine, VerificationAnswer::SAFE, true);
}

TEST_F(PDKindTest, test_PDKIND_simple_unsafe)
{
    options.addOption(Options::LOGIC, "QF_LIA");
    options.addOption(Options::COMPUTE_WITNESS, "true");
    SymRef s1 = mkPredicateSymbol("s1", {intSort()});
    PTRef current = instantiatePredicate(s1, {x});
    PTRef next = instantiatePredicate(s1, {xp});
    // x = 0 => S1(x)
    // S1(x) and x' = x + 1 => S1(x')
    // S1(x) and x > 1 => false
    std::vector<ChClause> clauses{
        {
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{{logic->mkEq(xp, zero)}, {}}
        },
        {
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{{logic->mkEq(xp, logic->mkPlus(x, one))}, {UninterpretedPredicate{current}}}
        },
        {
            ChcHead{UninterpretedPredicate{logic->getTerm_false()}},
            ChcBody{{logic->mkGt(x, one)}, {UninterpretedPredicate{current}}}
        }};
    PDKind engine(*logic, options);
    solveSystem(clauses, engine, VerificationAnswer::UNSAFE, true);
}

TEST_F(PDKindTest, test_PDKIND_moreInductionForward_safe)
{
    options.addOption(Options::LOGIC, "QF_LIA");
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
        }};
    PDKind engine(*logic, options);
    solveSystem(clauses, engine, VerificationAnswer::SAFE, true);
}

TEST_F(PDKindTest, test_PDKIND_moreInductionBackward_safe)
{
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
    PDKind engine(*logic, options);
    solveSystem(clauses, engine, VerificationAnswer::SAFE, true);
}

TEST_F(PDKindTest, test_PDKIND_BeyondTransitionSystem_safe)
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
    PDKind engine(*logic, options);
    solveSystem(clauses, engine, VerificationAnswer::SAFE, true);
}

TEST_F(PDKindTest, test_PDKIND_modelRegression_safe) {
    Options options;
    options.addOption(Options::COMPUTE_WITNESS, "true");
    SymRef s1 = mkPredicateSymbol("s1", {intSort(), intSort()});
    PTRef current = instantiatePredicate(s1, {x,y});
    PTRef next = instantiatePredicate(s1, {xp,yp});
    // x = 0 and y = 0 => S1(x,y)
    // S1(x,y) and x < 3 and x' = x + y and y' = y + 1 => S1(x',y')
    // S1(x,y) and x < 0 => false
    std::vector<ChClause> clauses{
        {
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{{logic->mkAnd(logic->mkEq(xp, zero), logic->mkEq(yp, zero))}, {}}
        },
        {
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{{logic->mkAnd({
                        logic->mkEq(xp, logic->mkPlus(x, y)),
                        logic->mkEq(yp, logic->mkPlus(y, one)),
                        logic->mkLt(x, logic->mkIntConst(3))
                    })},
                    {UninterpretedPredicate{current}}
            }
        },
        {
            ChcHead{UninterpretedPredicate{logic->getTerm_false()}},
            ChcBody{{logic->mkLt(x, zero)}, {UninterpretedPredicate{current}}}
        }
    };
    PDKind engine(*logic, options);
    solveSystem(clauses, engine, VerificationAnswer::SAFE, true);
}

TEST_F(PDKindTest, test_PDKIND_RegressionUnsafe) {
    Options options;
    options.addOption(Options::COMPUTE_WITNESS, "true");
    SymRef s = mkPredicateSymbol("s", {boolSort(), intSort(), intSort(), intSort()});
    PTRef x0 = mkBoolVar("x0");
    PTRef x1 = mkIntVar("x1");
    PTRef x2 = mkIntVar("x2");
    PTRef x3 = mkIntVar("x3");
    PTRef x0p = mkBoolVar("x0p");
    PTRef x1p = mkIntVar("x1p");
    PTRef x2p = mkIntVar("x2p");
    PTRef x3p = mkIntVar("x3p");
    PTRef aux = logic->mkIntVar("aux");

    PTRef current = instantiatePredicate(s, {x0,x1,x2,x3});
    PTRef next = instantiatePredicate(s, {x0p, x1p, x2p, x3p});
    // x0 = false and x1 = 0 and x2 = 0 and x3 = 0 => s(x0,x1,x2,x3)
    // s(x0,x1,x2,x3) and x3 = 0 and (x0 = true or (x0 = false and aux != 0)) and x0p = true and x1p = x2 and x2p = 1 and x3p = x1 => s(x0p,x1p,x2p,x3p)
    // s(x0,x1,x2,x3) and x0 = true and x1 = 1 and x2 = 1 and x3 = 1 => false

    std::vector<ChClause> clauses {
        {
            ChcHead{UninterpretedPredicate{current}},
            ChcBody{{logic->mkAnd({logic->mkEq(x2, zero), logic->mkEq(x3, zero), logic->mkEq(x1, zero), logic->mkEq(x0, logic->getTerm_false())})}, {}}
        },
        {
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{{logic->mkAnd({
                        logic->mkEq(x3, zero),
                        logic->mkOr(logic->mkEq(x0, logic->getTerm_true()), logic->mkAnd(logic->mkEq(x0, logic->getTerm_false()), logic->mkNot(logic->mkEq(aux, zero)))),
                        logic->mkEq(x0p, logic->getTerm_true()),
                        logic->mkEq(x1p, x2),
                        logic->mkEq(x2p, one),
                        logic->mkEq(x3p, x1)
                    })},
                    {UninterpretedPredicate{current}}
            }
        },
        {
            ChcHead{UninterpretedPredicate{logic->getTerm_false()}},
            ChcBody{{logic->mkAnd({
                        logic->mkEq(x0, logic->getTerm_true()),
                        logic->mkEq(x1, one),
                        logic->mkEq(x2, one),
                        logic->mkEq(x3, one)
                    })},
                    {UninterpretedPredicate{current}}}
        }
    };
    PDKind engine(*logic, options);
    solveSystem(clauses, engine, VerificationAnswer::UNSAFE, true);
}