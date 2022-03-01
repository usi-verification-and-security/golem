//
// Created by Martin Blicha on 06.12.21.
//

#include <gtest/gtest.h>
#include "engine/TPA.h"
#include "Validator.h"

TEST(TPA_test, test_TPA_simple_safe)
{
    ArithLogic logic {opensmt::Logic_t::QF_LIA};
    Options options;
    options.addOption(Options::LOGIC, "QF_LIA");
    options.addOption(Options::COMPUTE_WITNESS, "true");
    options.addOption(Options::ENGINE, "tpa-split");
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
            ChcBody{logic.mkLt(x, logic.getTerm_IntZero()), {UninterpretedPredicate{current}}}
    );
    auto hypergraph = ChcGraphBuilder(logic).buildGraph(Normalizer(logic).normalize(system));
    ASSERT_TRUE(hypergraph->isNormalGraph());
    auto graph = hypergraph->toNormalGraph(logic);
    TPAEngine engine(logic, options);
    auto res = engine.solve(*graph);
    auto answer = res.getAnswer();
    ASSERT_EQ(answer, VerificationResult::SAFE);
    auto witness = res.getValidityWitness();
    ChcGraphContext ctx(*graph, logic);
    SystemVerificationResult systemResult (std::move(res), ctx);
    auto validationResult = Validator(logic).validate(system, systemResult);
    ASSERT_EQ(validationResult, Validator::Result::VALIDATED);
}

TEST(TPA_test, test_TPA_simple_unsafe)
{
    ArithLogic logic {opensmt::Logic_t::QF_LIA};
    Options options;
    options.addOption(Options::LOGIC, "QF_LIA");
    options.addOption(Options::COMPUTE_WITNESS, "true");
    options.addOption(Options::ENGINE, "tpa-split");
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
            ChcBody{logic.mkGt(x, logic.getTerm_IntOne()), {UninterpretedPredicate{current}}}
    );
    auto normalizedSystem = Normalizer(logic).normalize(system);
    auto hypergraph = ChcGraphBuilder(logic).buildGraph(normalizedSystem);
    ASSERT_TRUE(hypergraph->isNormalGraph());
    auto graph = hypergraph->toNormalGraph(logic);
    TPAEngine engine(logic, options);
    auto res = engine.solve(*graph);
    auto answer = res.getAnswer();
    ASSERT_EQ(answer, VerificationResult::UNSAFE);
//    auto witness = res.getInvalidityWitness();
    ChcGraphContext ctx(*graph, logic);
    SystemVerificationResult systemResult (std::move(res), ctx);
    auto validationResult = Validator(logic).validate(*normalizedSystem.normalizedSystem, systemResult);
    ASSERT_EQ(validationResult, Validator::Result::VALIDATED);
}

TEST(TPA_test, test_TPA_CEX_zero) {
    ArithLogic logic {opensmt::Logic_t::QF_LIA};
    Options options;
    options.addOption(Options::LOGIC, "QF_LIA");
    options.addOption(Options::COMPUTE_WITNESS, "true");
    options.addOption(Options::ENGINE, "tpa");
    SymRef s1 = logic.declareFun("s1", logic.getSort_bool(), {logic.getSort_int()});
    PTRef x = logic.mkIntVar("x");
    PTRef xp = logic.mkIntVar("xp");
    PTRef current = logic.mkUninterpFun(s1, {x});
    PTRef next = logic.mkUninterpFun(s1, {xp});
    ChcSystem system;
    system.addUninterpretedPredicate(s1);
    system.addClause( // x' = 0 => S1(x')
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{logic.mkEq(xp, logic.getTerm_IntZero()), {}});
    system.addClause( // S1(x) and x' = x + 1 => S1(x')
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{logic.mkEq(xp, logic.mkPlus(x, logic.getTerm_IntOne())), {UninterpretedPredicate{current}}}
    );
    system.addClause( // S1(x) and x = 0 => false
            ChcHead{UninterpretedPredicate{logic.getTerm_false()}},
            ChcBody{logic.mkEq(x, logic.getTerm_IntZero()), {UninterpretedPredicate{current}}}
    );
    auto normalizedSystem = Normalizer(logic).normalize(system);
    auto hypergraph = ChcGraphBuilder(logic).buildGraph(normalizedSystem);
    ASSERT_TRUE(hypergraph->isNormalGraph());
    auto graph = hypergraph->toNormalGraph(logic);
    TPAEngine engine(logic, options);
    auto res = engine.solve(*graph);
    auto answer = res.getAnswer();
    ASSERT_EQ(answer, VerificationResult::UNSAFE);
    ChcGraphContext ctx(*graph, logic);
    SystemVerificationResult systemResult (std::move(res), ctx);
    auto validationResult = Validator(logic).validate(*normalizedSystem.normalizedSystem, systemResult);
    ASSERT_EQ(validationResult, Validator::Result::VALIDATED);
}

TEST(TPA_test, test_TPA_CEX_one) {
    ArithLogic logic {opensmt::Logic_t::QF_LIA};
    Options options;
    options.addOption(Options::LOGIC, "QF_LIA");
    options.addOption(Options::COMPUTE_WITNESS, "true");
    options.addOption(Options::ENGINE, "tpa");
    SymRef s1 = logic.declareFun("s1", logic.getSort_bool(), {logic.getSort_int()});
    PTRef x = logic.mkIntVar("x");
    PTRef xp = logic.mkIntVar("xp");
    PTRef current = logic.mkUninterpFun(s1, {x});
    PTRef next = logic.mkUninterpFun(s1, {xp});
    ChcSystem system;
    system.addUninterpretedPredicate(s1);
    system.addClause( // x' = 0 => S1(x')
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{logic.mkEq(xp, logic.getTerm_IntZero()), {}});
    system.addClause( // S1(x) and x' = x + 1 => S1(x')
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{logic.mkEq(xp, logic.mkPlus(x, logic.getTerm_IntOne())), {UninterpretedPredicate{current}}}
    );
    system.addClause( // S1(x) and x = 1 => false
            ChcHead{UninterpretedPredicate{logic.getTerm_false()}},
            ChcBody{logic.mkEq(x, logic.getTerm_IntOne()), {UninterpretedPredicate{current}}}
    );
    auto normalizedSystem = Normalizer(logic).normalize(system);
    auto hypergraph = ChcGraphBuilder(logic).buildGraph(normalizedSystem);
    ASSERT_TRUE(hypergraph->isNormalGraph());
    auto graph = hypergraph->toNormalGraph(logic);
    TPAEngine engine(logic, options);
    auto res = engine.solve(*graph);
    auto answer = res.getAnswer();
    ASSERT_EQ(answer, VerificationResult::UNSAFE);
    ChcGraphContext ctx(*graph, logic);
    SystemVerificationResult systemResult (std::move(res), ctx);
    auto validationResult = Validator(logic).validate(*normalizedSystem.normalizedSystem, systemResult);
    ASSERT_EQ(validationResult, Validator::Result::VALIDATED);
}

TEST(TPA_test, test_TPA_CEX_six) {
    ArithLogic logic {opensmt::Logic_t::QF_LIA};
    Options options;
    options.addOption(Options::LOGIC, "QF_LIA");
    options.addOption(Options::COMPUTE_WITNESS, "true");
    options.addOption(Options::ENGINE, "tpa");
    SymRef s1 = logic.declareFun("s1", logic.getSort_bool(), {logic.getSort_int()});
    PTRef x = logic.mkIntVar("x");
    PTRef xp = logic.mkIntVar("xp");
    PTRef current = logic.mkUninterpFun(s1, {x});
    PTRef next = logic.mkUninterpFun(s1, {xp});
    ChcSystem system;
    system.addUninterpretedPredicate(s1);
    system.addClause( // x' = 0 => S1(x')
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{logic.mkEq(xp, logic.getTerm_IntZero()), {}});
    system.addClause( // S1(x) and x' = x + 1 => S1(x')
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{logic.mkEq(xp, logic.mkPlus(x, logic.getTerm_IntOne())), {UninterpretedPredicate{current}}}
    );
    system.addClause( // S1(x) and x = 6 => false
            ChcHead{UninterpretedPredicate{logic.getTerm_false()}},
            ChcBody{logic.mkEq(x, logic.mkIntConst(6)), {UninterpretedPredicate{current}}}
    );
    auto normalizedSystem = Normalizer(logic).normalize(system);
    auto hypergraph = ChcGraphBuilder(logic).buildGraph(normalizedSystem);
    ASSERT_TRUE(hypergraph->isNormalGraph());
    auto graph = hypergraph->toNormalGraph(logic);
    TPAEngine engine(logic, options);
    auto res = engine.solve(*graph);
    auto answer = res.getAnswer();
    ASSERT_EQ(answer, VerificationResult::UNSAFE);
    ChcGraphContext ctx(*graph, logic);
    SystemVerificationResult systemResult (std::move(res), ctx);
    auto validationResult = Validator(logic).validate(*normalizedSystem.normalizedSystem, systemResult);
    ASSERT_EQ(validationResult, Validator::Result::VALIDATED);
}

TEST(TPA_test, test_TPA_chain_of_two_unsafe) {
    ArithLogic logic {opensmt::Logic_t::QF_LIA};
    Options options;
    options.addOption(Options::LOGIC, "QF_LIA");
    options.addOption(Options::COMPUTE_WITNESS, "true");
    options.addOption(Options::ENGINE, "tpa-split");
    SymRef s1 = logic.declareFun("s1", logic.getSort_bool(), {logic.getSort_int()});
    SymRef s2 = logic.declareFun("s2", logic.getSort_bool(), {logic.getSort_int()});
    PTRef x = logic.mkIntVar("x");
    PTRef xp = logic.mkIntVar("xp");
    PTRef predS1Current = logic.mkUninterpFun(s1, {x});
    PTRef predS1Next = logic.mkUninterpFun(s1, {xp});
    PTRef predS2Current = logic.mkUninterpFun(s2, {x});
    PTRef predS2Next = logic.mkUninterpFun(s2, {xp});
    ChcSystem system;
    system.addUninterpretedPredicate(s1);
    system.addUninterpretedPredicate(s2);
    system.addClause(
            ChcHead{UninterpretedPredicate{predS1Next}},
            ChcBody{logic.mkEq(xp, logic.getTerm_IntZero()), {}});
    system.addClause(
            ChcHead{UninterpretedPredicate{predS1Next}},
            ChcBody{logic.mkEq(xp, logic.mkPlus(x, logic.getTerm_IntOne())), {UninterpretedPredicate{predS1Current}}}
    );
    system.addClause(
            ChcHead{UninterpretedPredicate{predS2Current}},
            ChcBody{logic.getTerm_true(), {UninterpretedPredicate{predS1Current}}}
    );
    system.addClause(
            ChcHead{UninterpretedPredicate{predS2Next}},
            ChcBody{logic.mkEq(xp, logic.mkMinus(x, logic.getTerm_IntOne())),
                    {UninterpretedPredicate{predS2Current}}}
    );
    system.addClause(
            ChcHead{UninterpretedPredicate{logic.getTerm_false()}},
            ChcBody{logic.mkLt(x, logic.getTerm_IntZero()), {UninterpretedPredicate{predS2Current}}}
    );
    auto normalizedSystem = Normalizer(logic).normalize(system);
    auto hypergraph = ChcGraphBuilder(logic).buildGraph(normalizedSystem);
    ASSERT_TRUE(hypergraph->isNormalGraph());
    auto graph = hypergraph->toNormalGraph(logic);
    TPAEngine engine(logic, options);
    auto res = engine.solve(*graph);
    ASSERT_EQ(res.getAnswer(), VerificationResult::UNSAFE);
    ChcGraphContext ctx(*graph, logic);
    SystemVerificationResult systemResult (std::move(res), ctx);
    auto validationResult = Validator(logic).validate(*normalizedSystem.normalizedSystem, systemResult);
    ASSERT_EQ(validationResult, Validator::Result::VALIDATED);
}

TEST(TPA_test, test_TPA_chain_of_two_safe) {
    ArithLogic logic {opensmt::Logic_t::QF_LIA};
    Options options;
    options.addOption(Options::LOGIC, "QF_LIA");
    options.addOption(Options::COMPUTE_WITNESS, "true");
    options.addOption(Options::ENGINE, "tpa-split");
    SymRef s1 = logic.declareFun("s1", logic.getSort_bool(), {logic.getSort_int()});
    SymRef s2 = logic.declareFun("s2", logic.getSort_bool(), {logic.getSort_int()});
    PTRef x = logic.mkIntVar("x");
    PTRef xp = logic.mkIntVar("xp");
    PTRef predS1Current = logic.mkUninterpFun(s1, {x});
    PTRef predS1Next = logic.mkUninterpFun(s1, {xp});
    PTRef predS2Current = logic.mkUninterpFun(s2, {x});
    PTRef predS2Next = logic.mkUninterpFun(s2, {xp});
    ChcSystem system;
    system.addUninterpretedPredicate(s1);
    system.addUninterpretedPredicate(s2);
    system.addClause( // x = 0 => S1(x)
            ChcHead{UninterpretedPredicate{predS1Next}},
            ChcBody{logic.mkEq(xp, logic.getTerm_IntZero()), {}});
    system.addClause( // S1(x) & x' = x + 1 => S1(x')
            ChcHead{UninterpretedPredicate{predS1Next}},
            ChcBody{logic.mkEq(xp, logic.mkPlus(x, logic.getTerm_IntOne())), {UninterpretedPredicate{predS1Current}}}
    );
    system.addClause( // S1(x) => S2(x)
            ChcHead{UninterpretedPredicate{predS2Current}},
            ChcBody{logic.getTerm_true(), {UninterpretedPredicate{predS1Current}}}
    );
    system.addClause( // S2(x) & x' = x + 2 => S2(x')
            ChcHead{UninterpretedPredicate{predS2Next}},
            ChcBody{logic.mkEq(xp, logic.mkPlus(x, logic.mkIntConst(FastRational(2)))),
                    {UninterpretedPredicate{predS2Current}}}
    );
    system.addClause( // S2(x) & x < 0 => false
            ChcHead{UninterpretedPredicate{logic.getTerm_false()}},
            ChcBody{logic.mkLt(x, logic.getTerm_IntZero()), {UninterpretedPredicate{predS2Current}}}
    );
    auto hypergraph = ChcGraphBuilder(logic).buildGraph(Normalizer(logic).normalize(system));
    ASSERT_TRUE(hypergraph->isNormalGraph());
    auto graph = hypergraph->toNormalGraph(logic);
    TPAEngine engine(logic, options);
    auto res = engine.solve(*graph);
    ASSERT_EQ(res.getAnswer(), VerificationResult::SAFE);
}

TEST(TPA_test, test_TPA_chain_regression) {
    ArithLogic logic {opensmt::Logic_t::QF_LIA};
    Options options;
    options.addOption(Options::LOGIC, "QF_LIA");
//    options.addOption(Options::COMPUTE_WITNESS, "true");
    options.addOption(Options::ENGINE, "tpa-split");
    SymRef s1 = logic.declareFun("inv1", logic.getSort_bool(), {logic.getSort_int(), logic.getSort_int()});
    SymRef s2 = logic.declareFun("inv2", logic.getSort_bool(), {logic.getSort_int(), logic.getSort_int()});
    PTRef x = logic.mkIntVar("x");
    PTRef xp = logic.mkIntVar("xp");
    PTRef y = logic.mkIntVar("y");
    PTRef yp = logic.mkIntVar("yp");
    PTRef predS1Current = logic.mkUninterpFun(s1, {x, y});
    PTRef predS1Next = logic.mkUninterpFun(s1, {xp, yp});
    PTRef predS2Current = logic.mkUninterpFun(s2, {x, y});
    PTRef predS2Next = logic.mkUninterpFun(s2, {xp, yp});
    PTRef val = logic.mkIntConst(FastRational(5));
    PTRef doubleVal = logic.mkIntConst(FastRational(10));
    ChcSystem system;
    system.addUninterpretedPredicate(s1);
    system.addUninterpretedPredicate(s2);
    system.addClause(
            ChcHead{UninterpretedPredicate{predS1Next}},
            ChcBody{logic.mkAnd(logic.mkEq(xp, logic.getTerm_IntZero()), logic.mkEq(yp, val)), {}});
    system.addClause(
            ChcHead{UninterpretedPredicate{predS1Next}},
            ChcBody{logic.mkAnd({
                logic.mkEq(xp, logic.mkPlus(x, logic.getTerm_IntOne())),
                logic.mkEq(yp, y),
                logic.mkLt(x, val)
                }),
                {UninterpretedPredicate{predS1Current}}
            }
    );
    system.addClause(
            ChcHead{UninterpretedPredicate{predS2Current}},
            ChcBody{logic.mkGeq(x, val), {UninterpretedPredicate{predS1Current}}}
    );
    system.addClause(
            ChcHead{UninterpretedPredicate{predS2Next}},
            ChcBody{logic.mkAnd(
                        logic.mkEq(xp, logic.mkPlus(x, logic.getTerm_IntOne())),
                        logic.mkEq(yp, logic.mkPlus(y, logic.getTerm_IntOne()))
                        ),
                    {UninterpretedPredicate{predS2Current}}}
    );
    system.addClause(
            ChcHead{UninterpretedPredicate{logic.getTerm_false()}},
            ChcBody{logic.mkAnd(logic.mkEq(x, doubleVal), logic.mkNot(logic.mkEq(x, y))), {UninterpretedPredicate{predS2Current}}}
    );
    auto hypergraph = ChcGraphBuilder(logic).buildGraph(Normalizer(logic).normalize(system));
    ASSERT_TRUE(hypergraph->isNormalGraph());
    auto graph = hypergraph->toNormalGraph(logic);
    TPAEngine engine(logic, options);
    auto res = engine.solve(*graph);
    ASSERT_EQ(res.getAnswer(), VerificationResult::SAFE);
}