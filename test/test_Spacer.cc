/*
 * Copyright (c) 2021-2022, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "TestTemplate.h"
#include "engine/Spacer.h"

class Spacer_LRA_Test : public LRAEngineTest {
};

TEST_F(Spacer_LRA_Test, test_TransitionSystem)
{
    SymRef inv_sym = mkPredicateSymbol("Inv", {realSort()});
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
        { // Inv(x) & x < 0 => false
            ChcHead{UninterpretedPredicate{logic->getTerm_false()}},
            ChcBody{{logic->mkLt(x, zero)}, {UninterpretedPredicate{inv}}}
        }
    };
	
    Spacer engine(*logic, options);
    solveSystem(clauses, engine, VerificationAnswer::SAFE);
}

TEST_F(Spacer_LRA_Test, test_BasicLinearSystem)
{
    SymRef inv1_sym = mkPredicateSymbol("Inv1", {realSort(), realSort()});
    SymRef inv2_sym = mkPredicateSymbol("Inv2", {realSort(), realSort()});
    PTRef y = mkRealVar("y");
    PTRef yp = mkRealVar("yp");
    PTRef inv1 = instantiatePredicate(inv1_sym, {x,y});
    PTRef inv2 = instantiatePredicate(inv2_sym, {x,y});
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
    Spacer engine(*logic, options);
    solveSystem(clauses, engine, VerificationAnswer::SAFE);
}

TEST_F(Spacer_LRA_Test, test_BasicNonLinearSystem_Safe)
{
    SymRef invx_sym = mkPredicateSymbol("Invx", {realSort()});
    SymRef invy_sym = mkPredicateSymbol("Invy", {realSort()});
    PTRef y = mkRealVar("y");
    PTRef yp = mkRealVar("yp");
    PTRef invx = instantiatePredicate(invx_sym, {x});
    PTRef invy = instantiatePredicate(invy_sym, {y});
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
    Spacer engine(*logic, options);
    solveSystem(clauses, engine, VerificationAnswer::SAFE);
}

TEST_F(Spacer_LRA_Test, test_BasicNonLinearSystem_Unsafe)
{
    options.addOption(Options::COMPUTE_WITNESS, "true");
    SymRef invx_sym = mkPredicateSymbol("Invx", {realSort()});
    SymRef invy_sym = mkPredicateSymbol("Invy", {realSort()});
    PTRef y = mkRealVar("y");
    PTRef yp = mkRealVar("yp");
    PTRef invx = instantiatePredicate(invx_sym, {x});
    PTRef invy = instantiatePredicate(invy_sym, {y});
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
            ChcBody{{logic->mkEq(logic->mkPlus(x,y), logic->mkRealConst(FastRational(3)))}, {UninterpretedPredicate{invx}, UninterpretedPredicate{invy}}}    
        }
    };
    Spacer engine(*logic, options);
    solveSystem(clauses, engine, VerificationAnswer::UNSAFE, true);
}

TEST_F(Spacer_LRA_Test, test_NonLinearSystem_Bug)
{
    options.addOption(Options::COMPUTE_WITNESS, "true");
    SymRef M = mkPredicateSymbol("M", {realSort()});
    SymRef B = mkPredicateSymbol("B", {boolSort()});
    std::vector<ChClause> clauses{
        { // true => B(true)
            ChcHead{UninterpretedPredicate{instantiatePredicate(B, {logic->getTerm_true()})}},
            ChcBody{InterpretedFla{logic->getTerm_true()}, {}}
        },
        { // true => B(false)
            ChcHead{UninterpretedPredicate{instantiatePredicate(B, {logic->getTerm_false()})}},
            ChcBody{InterpretedFla{logic->getTerm_true()}, {}}
        },
        { // true => M(0)
            ChcHead{UninterpretedPredicate{instantiatePredicate(M, {zero})}},
            ChcBody{InterpretedFla{logic->getTerm_true()}, {}}
        },
        { // B(true) & B(false) & M(0) => M(1)
            ChcHead{UninterpretedPredicate{instantiatePredicate(M, {one})}},
            ChcBody{InterpretedFla{logic->getTerm_true()}, {
                UninterpretedPredicate{instantiatePredicate(B, {logic->getTerm_true()})},
                UninterpretedPredicate{instantiatePredicate(B, {logic->getTerm_false()})},
                UninterpretedPredicate{instantiatePredicate(M, {zero})},
            }}
        },
        { // M(1) => false
            ChcHead{UninterpretedPredicate{logic->getTerm_false()}},
            ChcBody{InterpretedFla{logic->getTerm_true()}, {UninterpretedPredicate{instantiatePredicate(M, {one})}}}
        }
    };
    Spacer engine(*logic, options);
    solveSystem(clauses, engine, VerificationAnswer::UNSAFE, true);
}

TEST_F(Spacer_LRA_Test, test_UnsatProofNondeterministicSystem)
{
    options.addOption(Options::COMPUTE_WITNESS, "true");
    SymRef P = mkPredicateSymbol("P", {realSort()});
    SymRef M = mkPredicateSymbol("M", {realSort()});
    PTRef y = mkRealVar("y");
    std::vector<ChClause> clauses{
        { // x < 0 => M(x)
            ChcHead{UninterpretedPredicate{instantiatePredicate(M, {xp})}},
            ChcBody{InterpretedFla{logic->mkLt(xp, zero)}, {}}
        },
        { // x > 0 => P(x)
            ChcHead{UninterpretedPredicate{instantiatePredicate(P, {xp})}},
            ChcBody{InterpretedFla{logic->mkGt(xp, zero)}, {}}
        },
        { // M(x) and P(y) and x + y = 0 => false
            ChcHead{UninterpretedPredicate{logic->getTerm_false()}},
            ChcBody{InterpretedFla{logic->mkEq(zero, logic->mkPlus(x,y))},
                {
                    UninterpretedPredicate{instantiatePredicate(M, {x})},
                    UninterpretedPredicate{instantiatePredicate(P, {y})}
                }
            }
        },
    };
    Spacer engine(*logic, options);
    solveSystem(clauses, engine, VerificationAnswer::UNSAFE, true);
}

TEST_F(Spacer_LRA_Test, test_UnsatProof_FactWithNoConstraints)
{
    options.addOption(Options::COMPUTE_WITNESS, "true");
    SymRef P = mkPredicateSymbol("P", {});
    std::vector<ChClause> clauses{
        { // true => P()
            ChcHead{UninterpretedPredicate{instantiatePredicate(P, {})}},
            ChcBody{InterpretedFla{logic->getTerm_true()}, {}}
        },
        { // P() => false
            ChcHead{UninterpretedPredicate{logic->getTerm_false()}},
            ChcBody{InterpretedFla{logic->getTerm_true()}, {UninterpretedPredicate{instantiatePredicate(P,{})}}}
        },
    };
    Spacer engine(*logic, options);
    solveSystem(clauses, engine, VerificationAnswer::UNSAFE, true);
}

