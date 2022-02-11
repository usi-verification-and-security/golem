/*
 * Copyright (c) 2022, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include <gtest/gtest.h>

#include "Normalizer.h"
#include "ChcGraph.h"

TEST(NormalizerTest, test_boolean_equal_to_constant) {
    LIALogic logic;
    Normalizer normalizer(logic);

    SymRef s1 = logic.declareFun("s1", logic.getSort_bool(), {logic.getSort_num(), logic.getSort_bool()}, nullptr, false);
    PTRef x = logic.mkNumVar("x");
    PTRef xp = logic.mkNumVar("xp");
    PTRef b = logic.mkBoolVar("b");
    ChcSystem system;
    system.addUninterpretedPredicate(s1);

    system.addClause(
            ChcHead{UninterpretedPredicate{logic.mkUninterpFun(s1, {logic.getTerm_NumZero(), logic.getTerm_false()})}},
            ChcBody{logic.getTerm_true()}
    );

    system.addClause(
            ChcHead{UninterpretedPredicate{logic.mkUninterpFun(s1, {x, logic.getTerm_true()})}},
            ChcBody{InterpretedFla{logic.mkEq(b, logic.getTerm_false())}, {UninterpretedPredicate{logic.mkUninterpFun(s1, {x, b})}}}
    );

    system.addClause(
            ChcHead{logic.getTerm_false()},
            ChcBody{InterpretedFla{}, {UninterpretedPredicate{logic.mkUninterpFun(s1, {logic.getTerm_NumZero(), logic.getTerm_true()})}}}
    );
    ChcPrinter(logic, std::cout).print(system);
    auto normalizedSystem = normalizer.normalize(system);
    ChcPrinter(logic, std::cout).print(*normalizedSystem.normalizedSystem);
    auto graph = ChcGraphBuilder(logic).buildGraph(normalizedSystem)->toNormalGraph();
    graph->toDot(std::cout, logic);
}
