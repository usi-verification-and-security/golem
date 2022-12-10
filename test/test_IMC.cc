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