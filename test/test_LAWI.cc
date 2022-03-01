//
// Created by Martin Blicha on 18.01.21.
//

#include <gtest/gtest.h>
#include "engine/Lawi.h"
#include "engine/LoopAccelerator.h"
#include "Validator.h"

TEST(LAWI_test, test_LAWI_simple)
{
	ArithLogic logic {opensmt::Logic_t::QF_LRA};
	Options options;
	options.addOption(Options::LOGIC, "QF_LRA");
	options.addOption(Options::COMPUTE_WITNESS, "true");
	SymRef s1 = logic.declareFun("s1", logic.getSort_bool(), {logic.getSort_real()});
	PTRef x = logic.mkRealVar("x");
	PTRef xp = logic.mkRealVar("xp");
	PTRef current = logic.mkUninterpFun(s1, {x});
	PTRef next = logic.mkUninterpFun(s1, {xp});
	ChcSystem system;
	system.addUninterpretedPredicate(s1);
	system.addClause(
		ChcHead{UninterpretedPredicate{next}},
		ChcBody{logic.mkEq(xp, logic.getTerm_RealZero()), {}});
	system.addClause(
		ChcHead{UninterpretedPredicate{next}},
		ChcBody{logic.mkEq(xp, logic.mkPlus(x, logic.getTerm_RealOne())), {UninterpretedPredicate{current}}}
		);
	system.addClause(
		ChcHead{UninterpretedPredicate{logic.getTerm_false()}},
		ChcBody{logic.mkLt(x, logic.getTerm_RealZero()), {UninterpretedPredicate{current}}}
	);
	auto hypergraph = ChcGraphBuilder(logic).buildGraph(Normalizer(logic).normalize(system));
	ASSERT_TRUE(hypergraph->isNormalGraph());
	auto graph = hypergraph->toNormalGraph(logic);
	Lawi engine(logic, options);
	auto res = engine.solve(*graph);
	auto answer = res.getAnswer();
	ASSERT_EQ(answer, VerificationResult::SAFE);
	auto witness = res.getValidityWitness();
	ChcGraphContext ctx(*graph, logic);
	SystemVerificationResult systemResult (std::move(res), ctx);
	auto validationResult = Validator(logic).validate(system, systemResult);
	ASSERT_EQ(validationResult, Validator::Result::VALIDATED);
}

TEST(LAWI_test, test_LAWI_branch)
{
	ArithLogic logic {opensmt::Logic_t::QF_LRA};
	Options options;
	options.addOption(Options::LOGIC, "QF_LRA");
	options.addOption(Options::COMPUTE_WITNESS, "true");
	SymRef first = logic.declareFun("s1", logic.getSort_bool(), {logic.getSort_real(), logic.getSort_real()});
	SymRef second = logic.declareFun("s2", logic.getSort_bool(), {logic.getSort_real(), logic.getSort_real()});
	PTRef x = logic.mkRealVar("x");
	PTRef xp = logic.mkRealVar("xp");
	PTRef y = logic.mkRealVar("y");
	PTRef yp = logic.mkRealVar("yp");
	PTRef s1 = logic.mkUninterpFun(first, {x,y});
	PTRef s1p = logic.mkUninterpFun(first, {xp, yp});
	PTRef s2 = logic.mkUninterpFun(second, {x,y});
	PTRef s2p = logic.mkUninterpFun(second, {xp, yp});
	ChcSystem system;
	system.addUninterpretedPredicate(first);
	system.addUninterpretedPredicate(second);
	system.addClause(
		ChcHead{UninterpretedPredicate{s1p}},
		ChcBody{logic.mkEq(xp, logic.getTerm_RealZero()), {}});
	system.addClause(
		ChcHead{UninterpretedPredicate{s1p}},
		ChcBody{logic.mkEq(xp, logic.mkPlus(x, logic.getTerm_RealOne())), {UninterpretedPredicate{s1}}}
	);
	system.addClause(
		ChcHead{UninterpretedPredicate{s2}},
		ChcBody{logic.mkLt(y, logic.getTerm_RealZero()), {UninterpretedPredicate{s1}}}
	);
	system.addClause(
		ChcHead{UninterpretedPredicate{s2}},
		ChcBody{logic.mkGeq(y, logic.getTerm_RealZero()), {UninterpretedPredicate{s1}}}
	);
	system.addClause(
		ChcHead{UninterpretedPredicate{s2p}},
		ChcBody{
			logic.mkAnd(
				logic.mkEq(yp, logic.mkPlus(y, logic.getTerm_RealOne())),
				logic.mkEq(xp, x)
				),
			{UninterpretedPredicate{s2}}}
	);
	system.addClause(
		ChcHead{UninterpretedPredicate{logic.getTerm_false()}},
		ChcBody{logic.mkLt(x, logic.getTerm_RealZero()), {UninterpretedPredicate{s2}}}
	);
	auto hypergraph = ChcGraphBuilder(logic).buildGraph(Normalizer(logic).normalize(system));
	ASSERT_TRUE(hypergraph->isNormalGraph());
	auto graph = hypergraph->toNormalGraph(logic);
//	graph->toDot(std::cout, logic);
	Lawi engine(logic, options);
	auto res = engine.solve(*graph);
	auto answer = res.getAnswer();
	ASSERT_EQ(answer, VerificationResult::SAFE);
	ChcGraphContext ctx(*graph, logic);
	SystemVerificationResult systemResult (std::move(res), ctx);
	systemResult.printWitness(std::cout, logic);
	auto validationResult = Validator(logic).validate(system, systemResult);
	ASSERT_EQ(validationResult, Validator::Result::VALIDATED);
}

TEST(LAWI_test, test_LAWI_unreachable_state)
{
	ArithLogic logic {opensmt::Logic_t::QF_LRA};
	Options options;
	options.addOption(Options::LOGIC, "QF_LRA");
	options.addOption(Options::COMPUTE_WITNESS, "true");
	SymRef s1 = logic.declareFun("s1", logic.getSort_bool(), {logic.getSort_real()});
	SymRef bin = logic.declareFun("bin", logic.getSort_bool(), {logic.getSort_real()});
	PTRef x = logic.mkRealVar("x");
	PTRef xp = logic.mkRealVar("xp");
	PTRef current = logic.mkUninterpFun(s1, {x});
	PTRef next = logic.mkUninterpFun(s1, {xp});
	PTRef binCurrent = logic.mkUninterpFun(bin, {x});
	PTRef binNext = logic.mkUninterpFun(bin, {xp});
	ChcSystem system;
	system.addUninterpretedPredicate(s1);
	system.addClause(
		ChcHead{UninterpretedPredicate{next}},
		ChcBody{logic.mkEq(xp, logic.getTerm_RealZero()), {}});
	system.addClause(
		ChcHead{UninterpretedPredicate{next}},
		ChcBody{logic.mkEq(xp, logic.mkPlus(x, logic.getTerm_RealOne())), {UninterpretedPredicate{current}}}
	);
	system.addClause(
		ChcHead{UninterpretedPredicate{logic.getTerm_false()}},
		ChcBody{logic.mkLt(x, logic.getTerm_RealZero()), {UninterpretedPredicate{current}}}
	);
	system.addClause(
		ChcHead{UninterpretedPredicate{binNext}},
		ChcBody{logic.mkEq(xp, logic.mkPlus(x, logic.getTerm_RealOne())), {UninterpretedPredicate{binCurrent}}}
	);
	system.addClause(
		ChcHead{UninterpretedPredicate{next}},
		ChcBody{
			logic.mkAnd(
				logic.mkEq(xp, x),
				logic.mkLt(x, logic.getTerm_RealZero())
			),
			{UninterpretedPredicate{binCurrent}}
		}
	);
	auto hypergraph = ChcGraphBuilder(logic).buildGraph(Normalizer(logic).normalize(system));
	ASSERT_TRUE(hypergraph->isNormalGraph());
	auto graph = hypergraph->toNormalGraph(logic);
	Lawi engine(logic, options);
	auto res = engine.solve(*graph);
	auto answer = res.getAnswer();
	ASSERT_EQ(answer, VerificationResult::SAFE);
	auto witness = res.getValidityWitness();
	ChcGraphContext ctx(*graph, logic);
	SystemVerificationResult systemResult (std::move(res), ctx);
	auto validationResult = Validator(logic).validate(system, systemResult);
	systemResult.printWitness(std::cout, logic);
	ASSERT_EQ(validationResult, Validator::Result::VALIDATED);
}

TEST(LAWI_test, test_LAWI_simple_unsafe)
{
    ArithLogic logic {opensmt::Logic_t::QF_LRA};
    Options options;
    options.addOption(Options::LOGIC, "QF_LRA");
    options.addOption(Options::COMPUTE_WITNESS, "true");
    SymRef s1 = logic.declareFun("s1", logic.getSort_bool(), {logic.getSort_real()});
    PTRef x = logic.mkRealVar("x");
    PTRef xp = logic.mkRealVar("xp");
    PTRef current = logic.mkUninterpFun(s1, {x});
    PTRef next = logic.mkUninterpFun(s1, {xp});
    ChcSystem system;
    system.addUninterpretedPredicate(s1);
    system.addClause(
        ChcHead{UninterpretedPredicate{next}},
        ChcBody{logic.mkEq(xp, logic.getTerm_RealZero()), {}});
    system.addClause(
        ChcHead{UninterpretedPredicate{next}},
        ChcBody{logic.mkEq(xp, logic.mkPlus(x, logic.getTerm_RealOne())), {UninterpretedPredicate{current}}}
    );
    system.addClause(
        ChcHead{UninterpretedPredicate{logic.getTerm_false()}},
        ChcBody{logic.mkEq(x, logic.mkRealConst(FastRational(1))), {UninterpretedPredicate{current}}}
    );
    auto normalizedSystem = Normalizer(logic).normalize(system);
    auto hypergraph = ChcGraphBuilder(logic).buildGraph(normalizedSystem);
    ASSERT_TRUE(hypergraph->isNormalGraph());
    auto graph = hypergraph->toNormalGraph(logic);
    Lawi engine(logic, options);
    auto res = engine.solve(*graph);
    auto answer = res.getAnswer();
    ASSERT_EQ(answer, VerificationResult::UNSAFE);

    ChcGraphContext ctx(*graph, logic);
    SystemVerificationResult systemResult (std::move(res), ctx);
    auto validationResult = Validator(logic).validate(*normalizedSystem.normalizedSystem, systemResult);
    ASSERT_EQ(validationResult, Validator::Result::VALIDATED);
}

TEST(LAWI_test, test_LAWI_accelerated_unsafe)
{
    ArithLogic logic {opensmt::Logic_t::QF_LIA};
    Options options;
    options.addOption(Options::COMPUTE_WITNESS, "true");
    SymRef s1 = logic.declareFun("s1", logic.getSort_bool(), {logic.getSort_int()});
    PTRef x = logic.mkIntVar("x");
    PTRef xp = logic.mkIntVar("xp");
    PTRef current = logic.mkUninterpFun(s1, {x});
    PTRef next = logic.mkUninterpFun(s1, {xp});
    ChcSystem system;
    system.addUninterpretedPredicate(s1);
    system.addClause(
        ChcHead{UninterpretedPredicate{next}},
        ChcBody{logic.mkEq(xp, logic.getTerm_IntZero()), {}});
    system.addClause(
        ChcHead{UninterpretedPredicate{next}},
        ChcBody{logic.mkEq(xp, logic.mkPlus(x, logic.getTerm_IntOne())), {UninterpretedPredicate{current}}}
    );
    system.addClause(
        ChcHead{UninterpretedPredicate{logic.getTerm_false()}},
        ChcBody{logic.mkEq(x, logic.mkIntConst(FastRational(100))), {UninterpretedPredicate{current}}}
    );
    auto normalizedSystem = Normalizer(logic).normalize(system);
    auto hypergraph = ChcGraphBuilder(logic).buildGraph(normalizedSystem);
    ASSERT_TRUE(hypergraph->isNormalGraph());
    auto graph = hypergraph->toNormalGraph(logic);
    LoopAccelerator engine(logic, std::unique_ptr<Engine>(new Lawi(logic, options)));
    auto res = engine.solve(*graph);
    auto answer = res.getAnswer();
    ASSERT_EQ(answer, VerificationResult::UNSAFE);

    ChcGraphContext ctx(*graph, logic);
    SystemVerificationResult systemResult (std::move(res), ctx);
    auto validationResult = Validator(logic).validate(*normalizedSystem.normalizedSystem, systemResult);
    ASSERT_EQ(validationResult, Validator::Result::VALIDATED);
}
