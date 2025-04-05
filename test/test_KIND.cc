/*
 * Copyright (c) 2022-2025, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "TestTemplate.h"
#include "engine/Kind.h"

class KindTest : public LIAEngineTest {
};

TEST_F(KindTest, test_KIND_simple_safe)
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
    Kind engine(*logic, options);
    solveSystem(clauses, engine, VerificationAnswer::SAFE, true);
}

TEST_F(KindTest, test_KIND_moreInductionForward_safe)
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
    Kind engine(*logic, options);
    solveSystem(clauses, engine, VerificationAnswer::SAFE, true);
}

TEST_F(KindTest, test_KIND_moreInductionBackward_safe)
{
    Options options;
    options.addOption(Options::LOGIC, "QF_LIA");
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
        }};
    Kind engine(*logic, options);
    solveSystem(clauses, engine, VerificationAnswer::SAFE, true);
}