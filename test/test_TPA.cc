//
// Created by Martin Blicha on 06.12.21.
//

#include <gtest/gtest.h>
#include "engine/TPA.h"
#include "Validator.h"

TEST(TPA_test, test_TPA_simple_safe)
{
    LIALogic logic;
    Options options;
    options.addOption(Options::LOGIC, "QF_LIA");
    options.addOption(Options::COMPUTE_WITNESS, "true");
    options.addOption(Options::ENGINE, "tpa-split");
    SymRef s1 = logic.declareFun("s1", logic.getSort_bool(), {logic.getSort_num()}, nullptr, false);
    PTRef x = logic.mkNumVar("x");
    PTRef xp = logic.mkNumVar("xp");
    PTRef current = logic.mkUninterpFun(s1, {x});
    PTRef next = logic.mkUninterpFun(s1, {xp});
    ChcSystem system;
    system.addUninterpretedPredicate(s1);
    system.addClause(
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{logic.mkEq(xp, logic.getTerm_NumZero()), {}});
    system.addClause(
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{logic.mkEq(xp, logic.mkNumPlus(x, logic.getTerm_NumOne())), {UninterpretedPredicate{current}}}
    );
    system.addClause(
            ChcHead{UninterpretedPredicate{logic.getTerm_false()}},
            ChcBody{logic.mkNumLt(x, logic.getTerm_NumZero()), {UninterpretedPredicate{current}}}
    );
    auto hypergraph = ChcGraphBuilder(logic).buildGraph(Normalizer(logic).normalize(system));
    ASSERT_TRUE(hypergraph->isNormalGraph());
    auto graph = hypergraph->toNormalGraph();
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
    LIALogic logic;
    Options options;
    options.addOption(Options::LOGIC, "QF_LIA");
    options.addOption(Options::COMPUTE_WITNESS, "true");
    options.addOption(Options::ENGINE, "tpa-split");
    SymRef s1 = logic.declareFun("s1", logic.getSort_bool(), {logic.getSort_num()}, nullptr, false);
    PTRef x = logic.mkNumVar("x");
    PTRef xp = logic.mkNumVar("xp");
    PTRef current = logic.mkUninterpFun(s1, {x});
    PTRef next = logic.mkUninterpFun(s1, {xp});
    ChcSystem system;
    system.addUninterpretedPredicate(s1);
    system.addClause(
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{logic.mkEq(xp, logic.getTerm_NumZero()), {}});
    system.addClause(
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{logic.mkEq(xp, logic.mkNumPlus(x, logic.getTerm_NumOne())), {UninterpretedPredicate{current}}}
    );
    system.addClause(
            ChcHead{UninterpretedPredicate{logic.getTerm_false()}},
            ChcBody{logic.mkNumGt(x, logic.getTerm_NumOne()), {UninterpretedPredicate{current}}}
    );
    auto hypergraph = ChcGraphBuilder(logic).buildGraph(Normalizer(logic).normalize(system));
    ASSERT_TRUE(hypergraph->isNormalGraph());
    auto graph = hypergraph->toNormalGraph();
    TPAEngine engine(logic, options);
    auto res = engine.solve(*graph);
    auto answer = res.getAnswer();
    ASSERT_EQ(answer, VerificationResult::UNSAFE);
    /* TODO: Uncomment when TPA suppports invalidity witnesses
    auto witness = res.getInvalidityWitness();
    ChcGraphContext ctx(*graph, logic);
    SystemVerificationResult systemResult (std::move(res), ctx);
    auto validationResult = Validator(logic).validate(system, systemResult);
    ASSERT_EQ(validationResult, Validator::Result::VALIDATED);
    */
}

TEST(TPA_test, test_TPA_chain_of_two) {
    LIALogic logic;
    Options options;
    options.addOption(Options::LOGIC, "QF_LIA");
    options.addOption(Options::COMPUTE_WITNESS, "true");
    options.addOption(Options::ENGINE, "tpa-split");
    SymRef s1 = logic.declareFun("s1", logic.getSort_bool(), {logic.getSort_num()}, nullptr, false);
    SymRef s2 = logic.declareFun("s2", logic.getSort_bool(), {logic.getSort_num()}, nullptr, false);
    PTRef x = logic.mkNumVar("x");
    PTRef xp = logic.mkNumVar("xp");
    PTRef predS1Current = logic.mkUninterpFun(s1, {x});
    PTRef predS1Next = logic.mkUninterpFun(s1, {xp});
    PTRef predS2Current = logic.mkUninterpFun(s2, {x});
    PTRef predS2Next = logic.mkUninterpFun(s2, {xp});
    ChcSystem system;
    system.addUninterpretedPredicate(s1);
    system.addUninterpretedPredicate(s2);
    system.addClause(
            ChcHead{UninterpretedPredicate{predS1Next}},
            ChcBody{logic.mkEq(xp, logic.getTerm_NumZero()), {}});
    system.addClause(
            ChcHead{UninterpretedPredicate{predS1Next}},
            ChcBody{logic.mkEq(xp, logic.mkNumPlus(x, logic.getTerm_NumOne())), {UninterpretedPredicate{predS1Current}}}
    );
    system.addClause(
            ChcHead{UninterpretedPredicate{predS2Current}},
            ChcBody{logic.getTerm_true(), {UninterpretedPredicate{predS1Current}}}
    );
    system.addClause(
            ChcHead{UninterpretedPredicate{predS2Next}},
            ChcBody{logic.mkEq(xp, logic.mkNumMinus(x, logic.getTerm_NumOne())),
                    {UninterpretedPredicate{predS2Current}}}
    );
    system.addClause(
            ChcHead{UninterpretedPredicate{logic.getTerm_false()}},
            ChcBody{logic.mkNumLt(x, logic.getTerm_NumZero()), {UninterpretedPredicate{predS2Current}}}
    );
    auto hypergraph = ChcGraphBuilder(logic).buildGraph(Normalizer(logic).normalize(system));
    ASSERT_TRUE(hypergraph->isNormalGraph());
    auto graph = hypergraph->toNormalGraph();
    TPAEngine engine(logic, options);
    auto res = engine.solve(*graph);
}