/*
 * Copyright (c) 2021-2022, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include <gtest/gtest.h>
#include "engine/Spacer.h"
#include "Validator.h"

TEST(Spacer_test, test_TransitionSystem)
{
	LRALogic logic;
	Options options;
	SymRef inv_sym = logic.declareFun("Inv", logic.getSort_bool(), {logic.getSort_num()}, nullptr, false);
	PTRef x = logic.mkNumVar("x");
	PTRef xp = logic.mkNumVar("xp");
	PTRef inv = logic.mkUninterpFun(inv_sym, {x});
	PTRef invp = logic.mkUninterpFun(inv_sym, {xp});
	ChcSystem system;
	system.addUninterpretedPredicate(inv_sym);
	system.addClause( // x' = 0 => Inv(x')
		ChcHead{UninterpretedPredicate{invp}},
		ChcBody{logic.mkEq(xp, logic.getTerm_NumZero()), {}});
	system.addClause( // Inv(x) & x' = x + 1 => Inv(x')
		ChcHead{UninterpretedPredicate{invp}},
		ChcBody{logic.mkEq(xp, logic.mkNumPlus(x, logic.getTerm_NumOne())), {UninterpretedPredicate{inv}}}
	);
	system.addClause( // Inv(x) & x < 0 => false
		ChcHead{UninterpretedPredicate{logic.getTerm_false()}},
		ChcBody{logic.mkNumLt(x, logic.getTerm_NumZero()), {UninterpretedPredicate{inv}}}
	);
    auto normalizedSystem = Normalizer(logic).normalize(system);
	auto hypergraph = ChcGraphBuilder(logic).buildGraph(normalizedSystem);
	Spacer engine(logic, options);
	auto res = engine.solve(*hypergraph);
	auto answer = res.getAnswer();
	ASSERT_EQ(answer, VerificationResult::SAFE);
    SystemVerificationResult systemResult(std::move(res));
    auto validationResult = Validator(logic).validate(*normalizedSystem.normalizedSystem, systemResult);
    ASSERT_EQ(validationResult, Validator::Result::VALIDATED);
}

TEST(Spacer_test, test_BasicLinearSystem)
{
    LRALogic logic;
    Options options;
    SymRef inv1_sym = logic.declareFun("Inv1", logic.getSort_bool(), {logic.getSort_num(), logic.getSort_num()}, nullptr, false);
    SymRef inv2_sym = logic.declareFun("Inv2", logic.getSort_bool(), {logic.getSort_num(), logic.getSort_num()}, nullptr, false);
    PTRef x = logic.mkNumVar("x");
    PTRef xp = logic.mkNumVar("xp");
    PTRef y = logic.mkNumVar("y");
    PTRef yp = logic.mkNumVar("yp");
    PTRef zero = logic.getTerm_NumZero();
    PTRef inv1 = logic.mkUninterpFun(inv1_sym, {x,y});
    PTRef inv2 = logic.mkUninterpFun(inv2_sym, {x,y});
    ChcSystem system;
    system.addUninterpretedPredicate(inv1_sym);
    system.addUninterpretedPredicate(inv2_sym);
    system.addClause(
        ChcHead{UninterpretedPredicate{inv1}},
        ChcBody{logic.mkAnd(logic.mkEq(x, zero), logic.mkEq(y, zero)), {}});
    system.addClause(
        ChcHead{UninterpretedPredicate{logic.mkUninterpFun(inv1_sym, {xp,y})}},
        ChcBody{logic.mkEq(xp, logic.mkNumPlus(x, logic.getTerm_NumOne())), {UninterpretedPredicate{inv1}}}
    );
    system.addClause(
        ChcHead{UninterpretedPredicate{inv2}},
        ChcBody{logic.getTerm_true(), {UninterpretedPredicate{inv1}}}
    );
    system.addClause(
        ChcHead{UninterpretedPredicate{logic.mkUninterpFun(inv2_sym, {x,yp})}},
        ChcBody{logic.mkEq(yp, logic.mkNumPlus(y, logic.getTerm_NumOne())), {UninterpretedPredicate{inv2}}}
    );
    system.addClause(
        ChcHead{UninterpretedPredicate{logic.getTerm_false()}},
        ChcBody{logic.mkNumLt(logic.mkNumPlus(x,y), logic.getTerm_NumZero()), {UninterpretedPredicate{inv2}}}
    );
//    ChcPrinter{logic, std::cout}.print(system);
    auto normalizedSystem = Normalizer(logic).normalize(system);
    auto hypergraph = ChcGraphBuilder(logic).buildGraph(normalizedSystem);
    Spacer engine(logic, options);
    auto res = engine.solve(*hypergraph);
    auto answer = res.getAnswer();
    ASSERT_EQ(answer, VerificationResult::SAFE);
    SystemVerificationResult systemResult(std::move(res));
    auto validationResult = Validator(logic).validate(*normalizedSystem.normalizedSystem, systemResult);
    ASSERT_EQ(validationResult, Validator::Result::VALIDATED);
}

TEST(Spacer_test, test_BasicNonLinearSystem_Safe)
{
    LRALogic logic;
    Options options;
    SymRef invx_sym = logic.declareFun("Invx", logic.getSort_bool(), {logic.getSort_num()}, nullptr, false);
    SymRef invy_sym = logic.declareFun("Invy", logic.getSort_bool(), {logic.getSort_num()}, nullptr, false);
    PTRef x = logic.mkNumVar("x");
    PTRef xp = logic.mkNumVar("xp");
    PTRef y = logic.mkNumVar("y");
    PTRef yp = logic.mkNumVar("yp");
    PTRef zero = logic.getTerm_NumZero();
    PTRef invx = logic.mkUninterpFun(invx_sym, {x});
    PTRef invy = logic.mkUninterpFun(invy_sym, {y});
    ChcSystem system;
    system.addUninterpretedPredicate(invx_sym);
    system.addUninterpretedPredicate(invy_sym);
    system.addClause(
        ChcHead{UninterpretedPredicate{invx}},
        ChcBody{logic.mkEq(x, zero), {}});
    system.addClause(
        ChcHead{UninterpretedPredicate{logic.mkUninterpFun(invx_sym, {xp})}},
        ChcBody{logic.mkEq(xp, logic.mkNumPlus(x, logic.getTerm_NumOne())), {UninterpretedPredicate{invx}}}
    );
    system.addClause(
        ChcHead{UninterpretedPredicate{invy}},
        ChcBody{logic.mkEq(y, zero), {}});
    system.addClause(
        ChcHead{UninterpretedPredicate{logic.mkUninterpFun(invy_sym, {yp})}},
        ChcBody{logic.mkEq(yp, logic.mkNumPlus(y, logic.getTerm_NumOne())), {UninterpretedPredicate{invy}}}
    );

    system.addClause(
        ChcHead{UninterpretedPredicate{logic.getTerm_false()}},
        ChcBody{logic.mkNumLt(logic.mkNumPlus(x,y), logic.getTerm_NumZero()), {UninterpretedPredicate{invx}, UninterpretedPredicate{invy}}}
    );
//    ChcPrinter{logic, std::cout}.print(system);
    auto normalizedSystem = Normalizer(logic).normalize(system);
    auto hypergraph = ChcGraphBuilder(logic).buildGraph(normalizedSystem);
    Spacer engine(logic, options);
    auto res = engine.solve(*hypergraph);
    auto answer = res.getAnswer();
    ASSERT_EQ(answer, VerificationResult::SAFE);
    SystemVerificationResult systemResult(std::move(res));
    auto validationResult = Validator(logic).validate(*normalizedSystem.normalizedSystem, systemResult);
    ASSERT_EQ(validationResult, Validator::Result::VALIDATED);
}

TEST(Spacer_test, test_BasicNonLinearSystem_Unsafe)
{
    LRALogic logic;
    Options options;
    SymRef invx_sym = logic.declareFun("Invx", logic.getSort_bool(), {logic.getSort_num()}, nullptr, false);
    SymRef invy_sym = logic.declareFun("Invy", logic.getSort_bool(), {logic.getSort_num()}, nullptr, false);
    PTRef x = logic.mkNumVar("x");
    PTRef xp = logic.mkNumVar("xp");
    PTRef y = logic.mkNumVar("y");
    PTRef yp = logic.mkNumVar("yp");
    PTRef zero = logic.getTerm_NumZero();
    PTRef invx = logic.mkUninterpFun(invx_sym, {x});
    PTRef invy = logic.mkUninterpFun(invy_sym, {y});
    ChcSystem system;
    system.addUninterpretedPredicate(invx_sym);
    system.addUninterpretedPredicate(invy_sym);
    system.addClause(
        ChcHead{UninterpretedPredicate{invx}},
        ChcBody{logic.mkEq(x, zero), {}});
    system.addClause(
        ChcHead{UninterpretedPredicate{logic.mkUninterpFun(invx_sym, {xp})}},
        ChcBody{logic.mkEq(xp, logic.mkNumPlus(x, logic.getTerm_NumOne())), {UninterpretedPredicate{invx}}}
    );
    system.addClause(
        ChcHead{UninterpretedPredicate{invy}},
        ChcBody{logic.mkEq(y, zero), {}});
    system.addClause(
        ChcHead{UninterpretedPredicate{logic.mkUninterpFun(invy_sym, {yp})}},
        ChcBody{logic.mkEq(yp, logic.mkNumPlus(y, logic.getTerm_NumOne())), {UninterpretedPredicate{invy}}}
    );

    system.addClause(
        ChcHead{UninterpretedPredicate{logic.getTerm_false()}},
        ChcBody{logic.mkEq(logic.mkNumPlus(x,y), logic.mkConst(FastRational(3))), {UninterpretedPredicate{invx}, UninterpretedPredicate{invy}}}
    );
//    ChcPrinter{logic, std::cout}.print(system);
    auto hypergraph = ChcGraphBuilder(logic).buildGraph(Normalizer(logic).normalize(system));
    Spacer engine(logic, options);
    auto res = engine.solve(*hypergraph);
    auto answer = res.getAnswer();
    ASSERT_EQ(answer, VerificationResult::UNSAFE);
}

TEST(Spacer_test, test_NonLinearSystem_Bug)
{
    LRALogic logic;
    Options options;
    SymRef M = logic.declareFun("M", logic.getSort_bool(), {logic.getSort_num()}, nullptr, false);
    SymRef B = logic.declareFun("B", logic.getSort_bool(), {logic.getSort_bool()}, nullptr, false);
    PTRef x = logic.mkNumVar("x");
    PTRef xp = logic.mkNumVar("xp");
    PTRef b = logic.mkBoolVar("b");
    PTRef zero = logic.getTerm_NumZero();
    PTRef one = logic.getTerm_NumOne();
    ChcSystem system;
    system.addUninterpretedPredicate(M);
    system.addUninterpretedPredicate(B);
    system.addClause( // true => B(true)
            ChcHead{UninterpretedPredicate{logic.mkUninterpFun(B, {logic.getTerm_true()})}},
            ChcBody{InterpretedFla{logic.getTerm_true()}, {}}
    );
    system.addClause( // true => B(false)
            ChcHead{UninterpretedPredicate{logic.mkUninterpFun(B, {logic.getTerm_false()})}},
            ChcBody{InterpretedFla{logic.getTerm_true()}, {}}
    );
    system.addClause( // true => M(0)
            ChcHead{UninterpretedPredicate{logic.mkUninterpFun(M, {zero})}},
            ChcBody{InterpretedFla{logic.getTerm_true()}, {}}
    );
    system.addClause( // B(true) & B(false) & M(0) => M(1)
            ChcHead{UninterpretedPredicate{logic.mkUninterpFun(M, {one})}},
            ChcBody{InterpretedFla{logic.getTerm_true()}, {
                    UninterpretedPredicate{logic.mkUninterpFun(B, {logic.getTerm_true()})},
                    UninterpretedPredicate{logic.mkUninterpFun(B, {logic.getTerm_false()})},
                    UninterpretedPredicate{logic.mkUninterpFun(M, {zero})},
            }});
    system.addClause( // M(1) => false
            ChcHead{UninterpretedPredicate{logic.getTerm_false()}},
            ChcBody{InterpretedFla{logic.getTerm_true()}, {UninterpretedPredicate{logic.mkUninterpFun(M, {one})}}}
    );
    ChcPrinter{logic, std::cout}.print(system);
    auto normalizedSystem = Normalizer(logic).normalize(system);
    ChcPrinter{logic, std::cout}.print(*normalizedSystem.normalizedSystem);
    auto hypergraph = ChcGraphBuilder(logic).buildGraph(normalizedSystem);
    Spacer engine(logic, options);
    auto res = engine.solve(*hypergraph);
    auto answer = res.getAnswer();
    ASSERT_EQ(answer, VerificationResult::UNSAFE);
}

