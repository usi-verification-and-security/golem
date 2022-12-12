/*
 * Copyright (c) 2021-2022, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include <gtest/gtest.h>
#include "engine/Bmc.h"
#include "graph/ChcGraphBuilder.h"
#include "Validator.h"

TEST(BMC_test, test_BMC_simple) {
    ArithLogic logic {opensmt::Logic_t::QF_LIA};
    Options options;
    options.addOption(Options::LOGIC, "QF_LIA");
    options.addOption(Options::COMPUTE_WITNESS, "true");
    SymRef s1 = logic.declareFun("s1", logic.getSort_bool(), {logic.getSort_int()});
    PTRef x = logic.mkIntVar("x");
    PTRef xp = logic.mkIntVar("xp");
    PTRef current = logic.mkUninterpFun(s1, {x});
    PTRef next = logic.mkUninterpFun(s1, {xp});
    ChcSystem system;
    system.addUninterpretedPredicate(s1);
    system.addClause( // x' = 0 => s1(x')
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{{logic.mkEq(xp, logic.getTerm_IntZero())}, {}});
    system.addClause( // s1(x) and x' = x + 1 => s1(x')
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{{logic.mkEq(xp, logic.mkPlus(x, logic.getTerm_IntOne()))}, {UninterpretedPredicate{current}}}
    );
    system.addClause( // s1(x) and x > 1 => false
            ChcHead{UninterpretedPredicate{logic.getTerm_false()}},
            ChcBody{{logic.mkGt(x, logic.getTerm_IntOne())}, {UninterpretedPredicate{current}}}
    );
    auto normalizedSystem = Normalizer(logic).normalize(system);
    auto hypergraph = ChcGraphBuilder(logic).buildGraph(normalizedSystem);
    ASSERT_TRUE(hypergraph->isNormalGraph());
    auto graph = hypergraph->toNormalGraph();
    BMC bmc(logic, options);
    auto res = bmc.solve(*graph);
    auto answer = res.getAnswer();
    ASSERT_EQ(answer, VerificationAnswer::UNSAFE);
    auto witness = res.getInvalidityWitness();
    auto validationResult = Validator(logic).validate(*hypergraph, res);
    ASSERT_EQ(validationResult, Validator::Result::VALIDATED);
}
