/*
 * Copyright (c) 2025, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "TestTemplate.h"
#include "engine/TRL.h"

class TRLTest : public LIAEngineTest {
};

TEST_F(TRLTest, test_TRL_simple_safe)
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
    TRL engine(*logic, options);
    solveSystem(clauses, engine, VerificationAnswer::SAFE, true);
}

TEST_F(TRLTest, test_TRL_incdec_safe)
{
    options.addOption(Options::LOGIC, "QF_LIA");
    options.addOption(Options::COMPUTE_WITNESS, "true");
    SymRef s = mkPredicateSymbol("s", {intSort(), intSort(), intSort()});
    PTRef current = instantiatePredicate(s, {x, y, z});
    PTRef next = instantiatePredicate(s, {xp, yp, zp});
    // x = 0 and y = 0 => S(x,y,z)
    // S(x,y,z) and (z = 0 and x' = x + 1 and y' = y + 1) or (z' = z and z = 1 and x' = x - 1 and y' = y - 1) => S(x', y', z')
    // S(x, y, z) and z = 1 and x <= 0 and y > 0 => false
    PTRef inc = logic->mkAnd({logic->mkEq(z, zero), logic->mkEq(xp, logic->mkPlus(x, one)), logic->mkEq(yp, logic->mkPlus(y, one))});
    PTRef dec = logic->mkAnd({logic->mkEq(z, one), logic->mkEq(zp, z), logic->mkEq(xp, logic->mkMinus(x, one)), logic->mkEq(yp, logic->mkMinus(y, one))});
    std::vector<ChClause> clauses{
        {
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{{logic->mkAnd(logic->mkEq(xp, zero), logic->mkEq(yp, zero))}, {}}
        },
        {
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{{logic->mkOr(inc, dec)}, {UninterpretedPredicate{current}}}
        },
        {
            ChcHead{UninterpretedPredicate{logic->getTerm_false()}},
            ChcBody{{logic->mkAnd({logic->mkEq(z, one), logic->mkLeq(x, zero), logic->mkGt(y, zero)})}, {UninterpretedPredicate{current}}}
        }};
    TRL engine(*logic, options);
    solveSystem(clauses, engine, VerificationAnswer::SAFE, true);
}
