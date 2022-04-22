/*
 * Copyright (c) 2022, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include <gtest/gtest.h>
#include "transformers/SimpleChainSummarizer.h"
#include "Validator.h"

TEST(Transformer_test, test_SingleChain_NoLoop) {
    ArithLogic logic {opensmt::Logic_t::QF_LIA};
    SymRef s1 = logic.declareFun("s1", logic.getSort_bool(), {logic.getSort_int()});
    SymRef s2 = logic.declareFun("s2", logic.getSort_bool(), {logic.getSort_int()});
    SymRef s3 = logic.declareFun("s3", logic.getSort_bool(), {logic.getSort_int()});
    PTRef x = logic.mkIntVar("x");
    PTRef xp = logic.mkIntVar("xp");
    PTRef y = logic.mkIntVar("y");
    PTRef currentS1 = logic.mkUninterpFun(s1, {x});
    PTRef currentS2 = logic.mkUninterpFun(s2, {x});
    PTRef nextS1 = logic.mkUninterpFun(s1, {xp});
    PTRef nextS2 = logic.mkUninterpFun(s2, {xp});
    ChcSystem system;
    system.addUninterpretedPredicate(s1);
    system.addUninterpretedPredicate(s2);
    system.addUninterpretedPredicate(s3);
    system.addClause( // x' >= 0 => S1(x')
        ChcHead{UninterpretedPredicate{nextS1}},
        ChcBody{{logic.mkGeq(xp, logic.getTerm_IntZero())}, {}});
    system.addClause( // S1(x) and x' = x + 1 => S2(x')
        ChcHead{UninterpretedPredicate{nextS2}},
        ChcBody{{logic.mkEq(xp, logic.mkPlus(x, logic.getTerm_IntOne()))}, {UninterpretedPredicate{currentS1}}}
    );
    system.addClause( // S2(x) => S3(2*x)
        ChcHead{UninterpretedPredicate{logic.mkUninterpFun(s3, {logic.mkTimes(x, logic.mkIntConst(2))})}},
        ChcBody{{logic.getTerm_true()}, {UninterpretedPredicate{currentS2}}}
    );
    system.addClause( // S3(y) and y < 0 => false
        ChcHead{UninterpretedPredicate{logic.getTerm_false()}},
        ChcBody{{logic.mkLt(y, logic.getTerm_IntZero())}, {UninterpretedPredicate{logic.mkUninterpFun(s3, {y})}}}
    );
    auto hypergraph = ChcGraphBuilder(logic).buildGraph(Normalizer(logic).normalize(system));
    auto [newGraph, translator] = SimpleChainSummarizer(logic).transform(std::move(hypergraph));
    ValidityWitness witness{};
    auto translatedWitness = translator->translate(witness);
    Validator validator(logic);
    SystemVerificationResult result(GraphVerificationResult(VerificationResult::SAFE, translatedWitness));
    ASSERT_EQ(validator.validate(system, result), Validator::Result::VALIDATED);
}

