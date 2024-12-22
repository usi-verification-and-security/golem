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

TEST_F(PredicateAbstractionTest, test_MultiPredicateInBody_Safe) {
    options.addOption(Options::COMPUTE_WITNESS, "true");
    SymRef inv_sym = mkPredicateSymbol("Inv", {intSort(), intSort()});
    PTRef inv1 = instantiatePredicate(inv_sym, {x,y});
    PTRef inv2 = instantiatePredicate(inv_sym, {xp,yp});
    // x = 0 and y = 0 => Inv(x,y)
    // x = 1 and y = 1 => Inv(x,y)
    // Inv(x,y) and Inv(x',y') => Inv(y + y', x + x')
    // Inv(x,y) and x = 0 and y = 1 => false
    std::vector<ChClause> clauses{
        {
            ChcHead{UninterpretedPredicate{inv1}},
            ChcBody{{logic->mkAnd(logic->mkEq(x, zero), logic->mkEq(y, zero))}, {}}
        },
        {
            ChcHead{UninterpretedPredicate{inv1}},
            ChcBody{{logic->mkAnd(logic->mkEq(x, one), logic->mkEq(y, one))}, {}}
        },
        {
            ChcHead{UninterpretedPredicate{instantiatePredicate(inv_sym, {logic->mkPlus(y,yp), logic->mkPlus(x,xp)})}},
            ChcBody{{logic->getTerm_true()}, {UninterpretedPredicate{inv1}, UninterpretedPredicate{inv2}}}
        },
        {
            ChcHead{UninterpretedPredicate{logic->getTerm_false()}},
            ChcBody{{logic->mkAnd(logic->mkEq(x, zero), logic->mkEq(y, one))}, {UninterpretedPredicate{inv1}}}
        }
    };
    ARGBasedEngine engine(*logic, options);
    solveSystem(clauses, engine, VerificationAnswer::SAFE, true);
}

TEST_F(PredicateAbstractionTest, test_OneOfTwo_Unsafe) {
    options.addOption(Options::COMPUTE_WITNESS, "true");
    SymRef inv1_sym = mkPredicateSymbol("Inv1", {intSort()});
    SymRef inv2_sym = mkPredicateSymbol("Inv2", {intSort()});
    PTRef inv1 = instantiatePredicate(inv1_sym, {x});
    PTRef inv2 = instantiatePredicate(inv2_sym, {x});
    // x = 0 => Inv1(x)
    // x = 1 => Inv1(x)
    // Inv1(x) => Inv2(x)
    // Inv2(x) and x = 1 => false
    std::vector<ChClause> clauses{
        {
            ChcHead{UninterpretedPredicate{inv1}},
            ChcBody{{logic->mkEq(x, zero)}, {}}
        },
        {
            ChcHead{UninterpretedPredicate{inv1}},
            ChcBody{{logic->mkEq(x, one)}, {}}
        },
        {
            ChcHead{UninterpretedPredicate{inv2}},
            ChcBody{{}, {UninterpretedPredicate{inv1}}}
        },
        {
            ChcHead{UninterpretedPredicate{logic->getTerm_false()}},
            ChcBody{{logic->mkEq(x, one)}, {UninterpretedPredicate{inv2}}}
        }
    };
    ARGBasedEngine engine(*logic, options);
    solveSystem(clauses, engine, VerificationAnswer::UNSAFE, true);
}


TEST_F(PredicateAbstractionTest, test_Regression_Unsafe) {
    options.addOption(Options::COMPUTE_WITNESS, "true");
    SymRef S1 = mkPredicateSymbol("S1", {intSort()});
    SymRef S2 = mkPredicateSymbol("S2", {intSort()});
    SymRef S3 = mkPredicateSymbol("S3", {intSort()});
    // true => S1(0)
    // S1(0) => S1(1)
    // S1(1) => S2(0)
    // S2(1) => false
    // S2(0) => S3(0)
    // false => S3(x)
    // S2(0) => S2(1)
    // S3(0) => S2(1)

    std::vector<ChClause> clauses{
        {// true => S1(0)
            ChcHead{UninterpretedPredicate{instantiatePredicate(S1, {zero})}},
            ChcBody{{logic->getTerm_true()}, {}}
        },
        {// S1(0) => S1(1)
            ChcHead{UninterpretedPredicate{instantiatePredicate(S1, {one})}},
            ChcBody{{logic->getTerm_true()}, {UninterpretedPredicate{instantiatePredicate(S1, {zero})}}}
        },
        {// S1(1) => S2(0)
            ChcHead{UninterpretedPredicate{instantiatePredicate(S2, {zero})}},
            ChcBody{{logic->getTerm_true()}, {UninterpretedPredicate{instantiatePredicate(S1, {one})}}}
        },
        {// S2(1) => false
            ChcHead{UninterpretedPredicate{logic->getTerm_false()}},
            ChcBody{{logic->getTerm_true()}, {UninterpretedPredicate{instantiatePredicate(S2, {one})}}}
        },
        {// S2(0) => S3(0)
            ChcHead{UninterpretedPredicate{instantiatePredicate(S3, {zero})}},
            ChcBody{{logic->getTerm_true()}, {UninterpretedPredicate{instantiatePredicate(S2, {zero})}}}
        },
        {// false => S3(x)
            ChcHead{UninterpretedPredicate{instantiatePredicate(S3, {x})}},
            ChcBody{{logic->getTerm_false()}, {}}
        },
        {// S2(0) => S2(1)
            ChcHead{UninterpretedPredicate{instantiatePredicate(S2, {one})}},
            ChcBody{{logic->getTerm_true()}, {UninterpretedPredicate{instantiatePredicate(S2, {zero})}}}
        },
        {// S3(0) => S2(1)
            ChcHead{UninterpretedPredicate{instantiatePredicate(S2, {one})}},
            ChcBody{{logic->getTerm_true()}, {UninterpretedPredicate{instantiatePredicate(S3, {zero})}}}
        }
    };
    ARGBasedEngine engine(*logic, options);
    solveSystem(clauses, engine, VerificationAnswer::UNSAFE, true);
}