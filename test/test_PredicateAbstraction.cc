/*
 * Copyright (c) 2022, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "TestTemplate.h"
#include "engine/ArgBasedEngine.h"


class PredicateAbstractionTest : public LIAEngineTest {
};

TEST_F(PredicateAbstractionTest, test_PA_simple_safe) {
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
    ARGBasedEngine engine(*logic, options);
    solveSystem(clauses, engine, VerificationAnswer::SAFE, true);
}

TEST_F(PredicateAbstractionTest, test_PA_simple_unsafe) {
    options.addOption(Options::COMPUTE_WITNESS, "true");
    SymRef s1 = mkPredicateSymbol("s1", {intSort()});
    PTRef current = instantiatePredicate(s1, {x});
    PTRef next = instantiatePredicate(s1, {xp});
    // x = 0 => S1(x)
    // S1(x) and x' = x + 1 => S1(x')
    // S1(x) and x = 1 => false
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
            ChcBody{{logic->mkEq(x, one)}, {UninterpretedPredicate{current}}}
        }
    };
    ARGBasedEngine engine(*logic, options);
    solveSystem(clauses, engine, VerificationAnswer::UNSAFE, true);
}

TEST_F(PredicateAbstractionTest, test_BasicLinearSystem_Safe) {
    options.addOption(Options::COMPUTE_WITNESS, "true");
    SymRef inv1_sym = mkPredicateSymbol("Inv1", {intSort(), intSort()});
    SymRef inv2_sym = mkPredicateSymbol("Inv2", {intSort(), intSort()});
    PTRef inv1 = instantiatePredicate(inv1_sym, {x,y});
    PTRef inv2 = instantiatePredicate(inv2_sym, {x,y});
    // x = 0 and y = 0 => Inv1(x,y)
    // Inv1(x,y) and xp = x + 1 => Inv1(xp,y)
    // Inv1(x,y) => Inv2(x,y)
    // Inv2(x,y) and yp = y + 1 => Inv2(x,yp)
    // Inv2(x,y) and x + y < 0 => false
    std::vector<ChClause> clauses{
        {
            ChcHead{UninterpretedPredicate{inv1}},
            ChcBody{{logic->mkAnd(logic->mkEq(x, zero), logic->mkEq(y, zero))}, {}}
        },
        {
            ChcHead{UninterpretedPredicate{instantiatePredicate(inv1_sym, {xp,y})}},
            ChcBody{{logic->mkEq(xp, logic->mkPlus(x, one))}, {UninterpretedPredicate{inv1}}}
        },
        {
            ChcHead{UninterpretedPredicate{inv2}},
            ChcBody{{logic->getTerm_true()}, {UninterpretedPredicate{inv1}}}

        },
        {
            ChcHead{UninterpretedPredicate{instantiatePredicate(inv2_sym, {x,yp})}},
            ChcBody{{logic->mkEq(yp, logic->mkPlus(y, one))}, {UninterpretedPredicate{inv2}}}

        },
        {
            ChcHead{UninterpretedPredicate{logic->getTerm_false()}},
            ChcBody{{logic->mkLt(logic->mkPlus(x,y), zero)}, {UninterpretedPredicate{inv2}}}

        }
    };
    ARGBasedEngine engine(*logic, options);
    solveSystem(clauses, engine, VerificationAnswer::SAFE, true);
}

TEST_F(PredicateAbstractionTest, test_BasicNonLinearSystem_Safe) {
    options.addOption(Options::COMPUTE_WITNESS, "true");
    SymRef invx_sym = mkPredicateSymbol("Invx", {intSort()});
    SymRef invy_sym = mkPredicateSymbol("Invy", {intSort()});
    PTRef invx = instantiatePredicate(invx_sym, {x});
    PTRef invy = instantiatePredicate(invy_sym, {y});

    // x = 0 => Invx(x)
    // Invx(x) and x' = x + 1 => Invx(x')
    // y = 0 => Invy(y)
    // Invy(y) and y' = y + 1 => Invy(y')
    // Invx(x) and Invy(y) and x + y < 0 => false
    std::vector<ChClause> clauses{
        {
            ChcHead{UninterpretedPredicate{invx}},
            ChcBody{{logic->mkEq(x, zero)}, {}}
        },
        {
            ChcHead{UninterpretedPredicate{instantiatePredicate(invx_sym, {xp})}},
            ChcBody{{logic->mkEq(xp, logic->mkPlus(x, one))}, {UninterpretedPredicate{invx}}}
        },
        {
            ChcHead{UninterpretedPredicate{invy}},
            ChcBody{{logic->mkEq(y, zero)}, {}}
        },
        {
            ChcHead{UninterpretedPredicate{instantiatePredicate(invy_sym, {yp})}},
            ChcBody{{logic->mkEq(yp, logic->mkPlus(y, one))}, {UninterpretedPredicate{invy}}}
        },
        {
            ChcHead{UninterpretedPredicate{logic->getTerm_false()}},
            ChcBody{{logic->mkLt(logic->mkPlus(x,y), zero)}, {UninterpretedPredicate{invx}, UninterpretedPredicate{invy}}}
        }
    };
    ARGBasedEngine engine(*logic, options);
    solveSystem(clauses, engine, VerificationAnswer::SAFE, true);
}

TEST_F(PredicateAbstractionTest, test_BasicNonLinearSystem_Unsafe) {
    options.addOption(Options::COMPUTE_WITNESS, "true");
    SymRef invx_sym = mkPredicateSymbol("Invx", {intSort()});
    SymRef invy_sym = mkPredicateSymbol("Invy", {intSort()});
    PTRef invx = instantiatePredicate(invx_sym, {x});
    PTRef invy = instantiatePredicate(invy_sym, {y});

    // x = 0 => Invx(x)
    // Invx(x) and x' = x + 1 => Invx(x')
    // y = 0 => Invy(y)
    // Invy(y) and y' = y + 1 => Invy(y')
    // Invx(x) and Invy(y) and x + y = 3 => false
    std::vector<ChClause> clauses{
        {
            ChcHead{UninterpretedPredicate{invx}},
            ChcBody{{logic->mkEq(x, zero)}, {}}
        },
        {
            ChcHead{UninterpretedPredicate{instantiatePredicate(invx_sym, {xp})}},
            ChcBody{{logic->mkEq(xp, logic->mkPlus(x, one))}, {UninterpretedPredicate{invx}}}
        },
        {
            ChcHead{UninterpretedPredicate{invy}},
            ChcBody{{logic->mkEq(y, zero)}, {}}
        },
        {
            ChcHead{UninterpretedPredicate{instantiatePredicate(invy_sym, {yp})}},
            ChcBody{{logic->mkEq(yp, logic->mkPlus(y, one))}, {UninterpretedPredicate{invy}}}
        },
        {
            ChcHead{UninterpretedPredicate{logic->getTerm_false()}},
            ChcBody{{logic->mkEq(logic->mkPlus(x,y), logic->mkIntConst(3))}, {UninterpretedPredicate{invx}, UninterpretedPredicate{invy}}}
        }
    };
    ARGBasedEngine engine(*logic, options);
    solveSystem(clauses, engine, VerificationAnswer::UNSAFE, true);
}