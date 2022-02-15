//
// Created by Martin Blicha on 06.12.21.
//

#include <gtest/gtest.h>
#include "engine/Bmc.h"
#include "Validator.h"

TEST(BMC_test, test_BMC_simple) {
    LIALogic logic;
    Options options;
    options.addOption(Options::LOGIC, "QF_LIA");
    options.addOption(Options::COMPUTE_WITNESS, "true");
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
    auto graph = hypergraph->toNormalGraph(logic);
    BMC bmc(logic, options);
    auto res = bmc.solve(*graph);
    auto answer = res.getAnswer();
    ASSERT_EQ(answer, VerificationResult::UNSAFE);
    /* TODO: uncomment when BMC produces invalidity witnesses
    auto witness = res.getInvalidityWitness();
    ChcGraphContext ctx(*graph, logic);
    SystemVerificationResult systemResult (std::move(res), ctx);
    auto validationResult = Validator(logic).validate(system, systemResult);
    ASSERT_EQ(validationResult, Validator::Result::VALIDATED);
    */
}
