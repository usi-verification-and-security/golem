/*
 * Copyright (c) 2022, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include <gtest/gtest.h>

#include "Normalizer.h"
#include "ChcGraph.h"

TEST(NormalizerTest, test_boolean_equal_to_constant) {
    ArithLogic logic {opensmt::Logic_t::QF_LIA};

    SymRef s1 = logic.declareFun("s1", logic.getSort_bool(), {logic.getSort_int(), logic.getSort_bool()});
    PTRef x = logic.mkIntVar("x");
    PTRef xp = logic.mkIntVar("xp");
    PTRef b = logic.mkBoolVar("b");
    ChcSystem system;
    system.addUninterpretedPredicate(s1);

    system.addClause(
            ChcHead{UninterpretedPredicate{logic.mkUninterpFun(s1, {logic.getTerm_IntZero(), logic.getTerm_false()})}},
            ChcBody{logic.getTerm_true()}
    );

    system.addClause(
            ChcHead{UninterpretedPredicate{logic.mkUninterpFun(s1, {x, logic.getTerm_true()})}},
            ChcBody{InterpretedFla{logic.mkEq(b, logic.getTerm_false())}, {UninterpretedPredicate{logic.mkUninterpFun(s1, {x, b})}}}
    );

    system.addClause(
            ChcHead{logic.getTerm_false()},
            ChcBody{InterpretedFla{}, {UninterpretedPredicate{logic.mkUninterpFun(s1, {logic.getTerm_IntZero(), logic.getTerm_true()})}}}
    );
    ChcPrinter(logic, std::cout).print(system);
    auto normalizedSystem = Normalizer(logic).normalize(system);
    ChcPrinter(logic, std::cout).print(*normalizedSystem.normalizedSystem);
    auto graph = ChcGraphBuilder(logic).buildGraph(normalizedSystem)->toNormalGraph(logic);
    graph->toDot(std::cout, logic);
}

TEST(NormalizerTest, test_ModConstraint) {
    ArithLogic logic {opensmt::Logic_t::QF_LIA};

    SymRef s1 = logic.declareFun("s1", logic.getSort_bool(), {logic.getSort_int()});
    PTRef x = logic.mkIntVar("x");
    PTRef c = logic.mkIntVar("c");
    PTRef d = logic.mkIntVar("d");
    PTRef zero = logic.getTerm_IntZero();
    ChcSystem system;
    system.addUninterpretedPredicate(s1);

    system.addClause(
        ChcHead{UninterpretedPredicate{logic.mkUninterpFun(s1, {x})}},
        ChcBody{logic.mkAnd(logic.mkEq(c, zero), logic.mkEq(x, logic.mkPlus(c,logic.mkTimes(d, logic.mkIntConst(3))))), {}}
    );
    system.addClause(
        ChcHead{UninterpretedPredicate{logic.getTerm_false()}},
        ChcBody{logic.mkEq(zero, logic.mkMod(x,logic.mkIntConst(2))), {UninterpretedPredicate{logic.mkUninterpFun(s1, {x})}}}
    );
    ChcPrinter(logic, std::cout).print(system);
    auto normalizedSystem = Normalizer(logic).normalize(system);
    auto const & clauses = normalizedSystem.normalizedSystem->getClauses();
    ChcPrinter(logic, std::cout).print(*normalizedSystem.normalizedSystem);
    ASSERT_NE(clauses[0].body.interpretedPart.fla, logic.getTerm_true());
//    auto graph = ChcGraphBuilder(logic).buildGraph(normalizedSystem)->toNormalGraph(logic);
//    graph->toDot(std::cout, logic);
}
