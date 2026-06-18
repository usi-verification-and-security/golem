/*
 * Copyright (c) 2025
 *
 * SPDX-License-Identifier: MIT
 */

#include "TestTemplate.h"
#include "engine/IC3IA.h"

// ===========================================================================
// IC3 tests (QF_LIA system — the CHC pipeline converts to a TransitionSystem
//            whose state vars happen to be versioned integer vars, but IC3
//            works on any domain where model evaluation returns bool values.
//            For pure Boolean systems IC3 is sound and complete.
//            For QF_LIA we test IC3IA instead.)
// ===========================================================================

class IC3LIATest : public LIAEngineTest {};

TEST_F(IC3LIATest, test_IC3IA_simple_unsafe) {
    Options options;
    options.addOption(Options::LOGIC, "QF_LIA");
    options.addOption(Options::COMPUTE_WITNESS, "true");
    SymRef s1 = mkPredicateSymbol("s1", {intSort()});
    PTRef current = instantiatePredicate(s1, {x});
    PTRef next    = instantiatePredicate(s1, {xp});
    std::vector<ChClause> clauses{
        { // x' = 0 => s1(x')
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{{logic->mkEq(xp, zero)}, {}}
        },
        { // s1(x) and x' = x + 1 => s1(x')
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{{logic->mkEq(xp, logic->mkPlus(x, one))},
                    {UninterpretedPredicate{current}}}
        },
        { // s1(x) and x > 1 => false
            ChcHead{UninterpretedPredicate{logic->getTerm_false()}},
            ChcBody{{logic->mkGt(x, one)}, {UninterpretedPredicate{current}}}
        }
    };
    IC3IA engine(*logic, options);
    solveSystem(clauses, engine, VerificationAnswer::UNSAFE, true);
}

TEST_F(IC3LIATest, test_IC3IA_simple_safe) {
    Options options;
    options.addOption(Options::LOGIC, "QF_LIA");
    options.addOption(Options::COMPUTE_WITNESS, "true");
    SymRef s1 = mkPredicateSymbol("s1", {intSort()});
    PTRef current = instantiatePredicate(s1, {x});
    PTRef next    = instantiatePredicate(s1, {xp});
    std::vector<ChClause> clauses{
        { // x' = 0 => s1(x')
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{{logic->mkEq(xp, zero)}, {}}
        },
        { // s1(x) and x' = x + 1 => s1(x')
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{{logic->mkEq(xp, logic->mkPlus(x, one))},
                    {UninterpretedPredicate{current}}}
        },
        { // s1(x) and x < 0 => false
            ChcHead{UninterpretedPredicate{logic->getTerm_false()}},
            ChcBody{{logic->mkLt(x, zero)}, {UninterpretedPredicate{current}}}
        }
    };
    IC3IA engine(*logic, options);
    solveSystem(clauses, engine, VerificationAnswer::SAFE, true);
}

TEST_F(IC3LIATest, test_IC3IA_two_vars_safe) {
    Options options;
    options.addOption(Options::LOGIC, "QF_LIA");
    options.addOption(Options::COMPUTE_WITNESS, "true");
    SymRef s1 = mkPredicateSymbol("s1", {intSort(), intSort()});
    PTRef current = instantiatePredicate(s1, {x, y});
    PTRef next    = instantiatePredicate(s1, {xp, yp});
    std::vector<ChClause> clauses{
        { // x' = 0 and y' = 0 => s1(x',y')
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{{logic->mkAnd(logic->mkEq(xp, zero), logic->mkEq(yp, zero))}, {}}
        },
        { // s1(x,y) and x' = x+1 and y' = y+1 => s1(x',y')
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{{logic->mkAnd(logic->mkEq(xp, logic->mkPlus(x, one)),
                                  logic->mkEq(yp, logic->mkPlus(y, one)))},
                    {UninterpretedPredicate{current}}}
        },
        { // s1(x,y) and x != y => false
            ChcHead{UninterpretedPredicate{logic->getTerm_false()}},
            ChcBody{{logic->mkNot(logic->mkEq(x, y))}, {UninterpretedPredicate{current}}}
        }
    };
    IC3IA engine(*logic, options);
    solveSystem(clauses, engine, VerificationAnswer::SAFE, true);
}

TEST_F(IC3LIATest, test_IC3IA_single_feasible_state) {
    Options options;
    options.addOption(Options::LOGIC, "QF_LIA");
    options.addOption(Options::COMPUTE_WITNESS, "true");
    SymRef s1 = mkPredicateSymbol("s1", {intSort()});
    PTRef current = instantiatePredicate(s1, {x});
    PTRef next    = instantiatePredicate(s1, {xp});
    // Init: x = 0; Trans: x' = 0; Bad: x > 0
    std::vector<ChClause> clauses{
        {
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{{logic->mkEq(xp, zero)}, {}}
        },
        {
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{{logic->mkEq(xp, zero)}, {UninterpretedPredicate{current}}}
        },
        {
            ChcHead{UninterpretedPredicate{logic->getTerm_false()}},
            ChcBody{{logic->mkGt(x, zero)},
                    {UninterpretedPredicate{current}}}
        }
    };
    IC3IA engine(*logic, options);
    solveSystem(clauses, engine, VerificationAnswer::SAFE, true);
}

TEST_F(IC3LIATest, test_IC3IA_init_violates_property) {
    Options options;
    options.addOption(Options::LOGIC, "QF_LIA");
    options.addOption(Options::COMPUTE_WITNESS, "true");
    SymRef s1 = mkPredicateSymbol("s1", {intSort()});
    PTRef current = instantiatePredicate(s1, {x});
    PTRef next    = instantiatePredicate(s1, {xp});
    // Init: x = 5; Trans: x' = x; Bad: x >= 5
    std::vector<ChClause> clauses{
        {
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{{logic->mkEq(xp, logic->mkIntConst(5))}, {}}
        },
        {
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{{logic->mkEq(xp, x)}, {UninterpretedPredicate{current}}}
        },
        {
            ChcHead{UninterpretedPredicate{logic->getTerm_false()}},
            ChcBody{{logic->mkGeq(x, logic->mkIntConst(5))},
                    {UninterpretedPredicate{current}}}
        }
    };
    IC3IA engine(*logic, options);
    solveSystem(clauses, engine, VerificationAnswer::UNSAFE, true);
}
