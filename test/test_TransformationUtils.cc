/*
 * Copyright (c) 2023-2025, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
*/

#include "TestTemplate.h"
#include "TransformationUtils.h"
#include <gtest/gtest.h>

using namespace golem;

class TransformationUtils_Test : public LIAEngineTest {
};

TEST_F(TransformationUtils_Test, test_DAGWithExtraEdge) {
    SymRef s1 = mkPredicateSymbol("s1", {intSort()});
    PTRef current = instantiatePredicate(s1, {x});
    PTRef next = instantiatePredicate(s1, {xp});
    std::vector<ChClause> clauses{
        {
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{{logic->mkEq(xp, zero)}, {}}},
        {
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{{logic->mkEq(xp, logic->mkPlus(x, one))}, {UninterpretedPredicate{current}}}
        },
        {
            ChcHead{UninterpretedPredicate{logic->getTerm_false()}},
            ChcBody{{logic->mkLt(x, zero)}, {UninterpretedPredicate{current}}}
        },
        {
            ChcHead{UninterpretedPredicate{logic->getTerm_false()}},
            ChcBody{{logic->mkLt(y, zero)}, {}}
        }
    };
    for (auto const & clause : clauses) { system.addClause(clause); }

    Logic & logic = *this->logic;
    auto normalizedSystem = Normalizer(logic).normalize(system);
    auto hypergraph = ChcGraphBuilder(logic).buildGraph(normalizedSystem);
    ASSERT_TRUE(hypergraph->isNormalGraph());
    auto graph = hypergraph->toNormalGraph();
    EXPECT_FALSE(isTransitionSystem(*graph));
    EXPECT_FALSE(isTransitionSystemDAG(*graph)); // Because of the extra edge from entry to exit
}

