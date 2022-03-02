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
	ArithLogic logic {opensmt::Logic_t::QF_LRA};
	Options options;
	SymRef inv_sym = logic.declareFun("Inv", logic.getSort_bool(), {logic.getSort_real()});
	PTRef x = logic.mkRealVar("x");
	PTRef xp = logic.mkRealVar("xp");
	PTRef inv = logic.mkUninterpFun(inv_sym, {x});
	PTRef invp = logic.mkUninterpFun(inv_sym, {xp});
	ChcSystem system;
	system.addUninterpretedPredicate(inv_sym);
	system.addClause( // x' = 0 => Inv(x')
		ChcHead{UninterpretedPredicate{invp}},
		ChcBody{logic.mkEq(xp, logic.getTerm_RealZero()), {}});
	system.addClause( // Inv(x) & x' = x + 1 => Inv(x')
		ChcHead{UninterpretedPredicate{invp}},
		ChcBody{logic.mkEq(xp, logic.mkPlus(x, logic.getTerm_RealOne())), {UninterpretedPredicate{inv}}}
	);
	system.addClause( // Inv(x) & x < 0 => false
		ChcHead{UninterpretedPredicate{logic.getTerm_false()}},
		ChcBody{logic.mkLt(x, logic.getTerm_RealZero()), {UninterpretedPredicate{inv}}}
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
    ArithLogic logic {opensmt::Logic_t::QF_LRA};
    Options options;
    SymRef inv1_sym = logic.declareFun("Inv1", logic.getSort_bool(), {logic.getSort_real(), logic.getSort_real()});
    SymRef inv2_sym = logic.declareFun("Inv2", logic.getSort_bool(), {logic.getSort_real(), logic.getSort_real()});
    PTRef x = logic.mkRealVar("x");
    PTRef xp = logic.mkRealVar("xp");
    PTRef y = logic.mkRealVar("y");
    PTRef yp = logic.mkRealVar("yp");
    PTRef zero = logic.getTerm_RealZero();
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
        ChcBody{logic.mkEq(xp, logic.mkPlus(x, logic.getTerm_RealOne())), {UninterpretedPredicate{inv1}}}
    );
    system.addClause(
        ChcHead{UninterpretedPredicate{inv2}},
        ChcBody{logic.getTerm_true(), {UninterpretedPredicate{inv1}}}
    );
    system.addClause(
        ChcHead{UninterpretedPredicate{logic.mkUninterpFun(inv2_sym, {x,yp})}},
        ChcBody{logic.mkEq(yp, logic.mkPlus(y, logic.getTerm_RealOne())), {UninterpretedPredicate{inv2}}}
    );
    system.addClause(
        ChcHead{UninterpretedPredicate{logic.getTerm_false()}},
        ChcBody{logic.mkLt(logic.mkPlus(x,y), logic.getTerm_RealZero()), {UninterpretedPredicate{inv2}}}
    );
//    ChcPrinter{logic, std::cout}.print(system);
    auto normalizedSystem = Normalizer(logic).normalize(system);
//    ChcPrinter{logic, std::cout}.print(*normalizedSystem.normalizedSystem);
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
    ArithLogic logic {opensmt::Logic_t::QF_LRA};
    Options options;
    SymRef invx_sym = logic.declareFun("Invx", logic.getSort_bool(), {logic.getSort_real()});
    SymRef invy_sym = logic.declareFun("Invy", logic.getSort_bool(), {logic.getSort_real()});
    PTRef x = logic.mkRealVar("x");
    PTRef xp = logic.mkRealVar("xp");
    PTRef y = logic.mkRealVar("y");
    PTRef yp = logic.mkRealVar("yp");
    PTRef zero = logic.getTerm_RealZero();
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
        ChcBody{logic.mkEq(xp, logic.mkPlus(x, logic.getTerm_RealOne())), {UninterpretedPredicate{invx}}}
    );
    system.addClause(
        ChcHead{UninterpretedPredicate{invy}},
        ChcBody{logic.mkEq(y, zero), {}});
    system.addClause(
        ChcHead{UninterpretedPredicate{logic.mkUninterpFun(invy_sym, {yp})}},
        ChcBody{logic.mkEq(yp, logic.mkPlus(y, logic.getTerm_RealOne())), {UninterpretedPredicate{invy}}}
    );

    system.addClause(
        ChcHead{UninterpretedPredicate{logic.getTerm_false()}},
        ChcBody{logic.mkLt(logic.mkPlus(x,y), logic.getTerm_RealZero()), {UninterpretedPredicate{invx}, UninterpretedPredicate{invy}}}
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
    ArithLogic logic {opensmt::Logic_t::QF_LRA};
    Options options;
    SymRef invx_sym = logic.declareFun("Invx", logic.getSort_bool(), {logic.getSort_real()});
    SymRef invy_sym = logic.declareFun("Invy", logic.getSort_bool(), {logic.getSort_real()});
    PTRef x = logic.mkRealVar("x");
    PTRef xp = logic.mkRealVar("xp");
    PTRef y = logic.mkRealVar("y");
    PTRef yp = logic.mkRealVar("yp");
    PTRef zero = logic.getTerm_RealZero();
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
        ChcBody{logic.mkEq(xp, logic.mkPlus(x, logic.getTerm_RealOne())), {UninterpretedPredicate{invx}}}
    );
    system.addClause(
        ChcHead{UninterpretedPredicate{invy}},
        ChcBody{logic.mkEq(y, zero), {}});
    system.addClause(
        ChcHead{UninterpretedPredicate{logic.mkUninterpFun(invy_sym, {yp})}},
        ChcBody{logic.mkEq(yp, logic.mkPlus(y, logic.getTerm_RealOne())), {UninterpretedPredicate{invy}}}
    );

    system.addClause(
        ChcHead{UninterpretedPredicate{logic.getTerm_false()}},
        ChcBody{logic.mkEq(logic.mkPlus(x,y), logic.mkRealConst(FastRational(3))), {UninterpretedPredicate{invx}, UninterpretedPredicate{invy}}}
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
    ArithLogic logic {opensmt::Logic_t::QF_LRA};
    Options options;
    SymRef M = logic.declareFun("M", logic.getSort_bool(), {logic.getSort_real()});
    SymRef B = logic.declareFun("B", logic.getSort_bool(), {logic.getSort_bool()});
    PTRef x = logic.mkRealVar("x");
    PTRef xp = logic.mkRealVar("xp");
    PTRef b = logic.mkBoolVar("b");
    PTRef zero = logic.getTerm_RealZero();
    PTRef one = logic.getTerm_RealOne();
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

