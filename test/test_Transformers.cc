/*
 * Copyright (c) 2022, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include <gtest/gtest.h>
#include "transformers/SimpleChainSummarizer.h"
#include "Validator.h"
#include "engine/Spacer.h"

class Transformer_test : public ::testing::Test {
protected:
    ArithLogic logic {opensmt::Logic_t::QF_LIA};
    PTRef x,xp;
    PTRef y,yp;
    PTRef z;
    PTRef zero;
    PTRef one;
    PTRef two;
    SymRef s1,s2,s3;
    PTRef currentS1, currentS2, nextS1, nextS2;
    Transformer_test() {
        x = logic.mkIntVar("x");
        xp = logic.mkIntVar("xp");
        y = logic.mkIntVar("y");
        yp = logic.mkIntVar("yp");
        z = logic.mkIntVar("z");
        zero = logic.getTerm_IntZero();
        one = logic.getTerm_IntOne();
        two = logic.mkIntConst(2);
        s1 = logic.declareFun("s1", logic.getSort_bool(), {logic.getSort_int()});
        s2 = logic.declareFun("s2", logic.getSort_bool(), {logic.getSort_int()});
        s3 = logic.declareFun("s3", logic.getSort_bool(), {logic.getSort_int()});
        currentS1 = logic.mkUninterpFun(s1, {x});
        currentS2 = logic.mkUninterpFun(s2, {x});
        nextS1 = logic.mkUninterpFun(s1, {xp});
        nextS2 = logic.mkUninterpFun(s2, {xp});
    }
public:
    std::unique_ptr<ChcDirectedHyperGraph> systemToGraph(ChcSystem const & system) {
        return ChcGraphBuilder(logic).buildGraph(Normalizer(logic).normalize(system));
    }
};

TEST_F(Transformer_test, test_SingleChain_NoLoop) {
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
    auto hypergraph = systemToGraph(system);
    auto [newGraph, translator] = SimpleChainSummarizer(logic).transform(std::move(hypergraph));
    ValidityWitness witness{};
    auto translatedWitness = translator->translate(witness);
    Validator validator(logic);
    SystemVerificationResult result(GraphVerificationResult(VerificationResult::SAFE, translatedWitness));
    ASSERT_EQ(validator.validate(system, result), Validator::Result::VALIDATED);
}

TEST_F(Transformer_test, test_TwoChains_WithLoop) {
    ChcSystem system;
    system.addUninterpretedPredicate(s1);
    system.addUninterpretedPredicate(s2);
    system.addUninterpretedPredicate(s3);
    system.addClause( // x' >= -2 => S1(x')
        ChcHead{UninterpretedPredicate{nextS1}},
        ChcBody{{logic.mkGeq(xp, logic.mkIntConst(-2))}, {}});
    system.addClause( // S1(x) and x' = x + 2 => S2(x')
        ChcHead{UninterpretedPredicate{nextS2}},
        ChcBody{{logic.mkEq(xp, logic.mkPlus(x, two))}, {UninterpretedPredicate{currentS1}}}
    );
    system.addClause( // S2(x) and x' = x + 1 => S2(x')
        ChcHead{UninterpretedPredicate{nextS2}},
        ChcBody{{logic.mkEq(xp, logic.mkPlus(x, one))}, {UninterpretedPredicate{currentS2}}}
    );
    system.addClause( // S2(x) => S3(x/2)
        ChcHead{UninterpretedPredicate{logic.mkUninterpFun(s3, {logic.mkIntDiv(x, two)})}},
        ChcBody{{logic.getTerm_true()}, {UninterpretedPredicate{currentS2}}}
    );
    system.addClause( // S3(y) and y < 0 => false
        ChcHead{UninterpretedPredicate{logic.getTerm_false()}},
        ChcBody{{logic.mkLt(y, logic.getTerm_IntZero())}, {UninterpretedPredicate{logic.mkUninterpFun(s3, {y})}}}
    );
    auto hypergraph = systemToGraph(system);
    auto [newGraph, translator] = SimpleChainSummarizer(logic).transform(std::move(hypergraph));
    VersionManager manager{logic};
    PTRef predicate = manager.sourceFormulaToBase(newGraph->getStateVersion(s2));
    PTRef var = logic.getPterm(predicate)[0];
    ValidityWitness witness{{{predicate, logic.mkGeq(var,zero)}}};
    auto translatedWitness = translator->translate(witness);
    Validator validator(logic);
    SystemVerificationResult result(GraphVerificationResult(VerificationResult::SAFE, translatedWitness));
    ASSERT_EQ(validator.validate(system, result), Validator::Result::VALIDATED);
}

TEST_F(Transformer_test, test_OutputFromEngine) {
    ChcSystem system;
    Options options;
    system.addUninterpretedPredicate(s1);
    system.addUninterpretedPredicate(s2);
    system.addUninterpretedPredicate(s3);
    system.addClause( // x' >= -2 => S1(x')
        ChcHead{UninterpretedPredicate{nextS1}},
        ChcBody{{logic.mkGeq(xp, logic.mkIntConst(-2))}, {}});
    system.addClause( // S1(x) and x' = x + 2 => S2(x')
        ChcHead{UninterpretedPredicate{nextS2}},
        ChcBody{{logic.mkEq(xp, logic.mkPlus(x, two))}, {UninterpretedPredicate{currentS1}}}
    );
    system.addClause( // S2(x) and x' = x + 1 => S2(x')
        ChcHead{UninterpretedPredicate{nextS2}},
        ChcBody{{logic.mkEq(xp, logic.mkPlus(x, one))}, {UninterpretedPredicate{currentS2}}}
    );
    system.addClause( // S2(x) => S3(x/2)
        ChcHead{UninterpretedPredicate{logic.mkUninterpFun(s3, {logic.mkIntDiv(x, two)})}},
        ChcBody{{logic.getTerm_true()}, {UninterpretedPredicate{currentS2}}}
    );
    system.addClause( // S3(y) and y < 0 => false
        ChcHead{UninterpretedPredicate{logic.getTerm_false()}},
        ChcBody{{logic.mkLt(y, logic.getTerm_IntZero())}, {UninterpretedPredicate{logic.mkUninterpFun(s3, {y})}}}
    );
    auto hypergraph = systemToGraph(system);
    auto [newGraph, translator] = SimpleChainSummarizer(logic).transform(std::move(hypergraph));
    hypergraph = std::move(newGraph);
//    hypergraph->forEachEdge([&](auto const & edge) {
//       std::cout << logic.pp(edge.fla.fla) << std::endl;
//    });
    auto res = Spacer(logic, options).solve(*hypergraph);
    ASSERT_EQ(res.getAnswer(), VerificationResult::SAFE);
    res = translator->translate(res);
    Validator validator(logic);
    SystemVerificationResult result(std::move(res));
    EXPECT_EQ(validator.validate(system, result), Validator::Result::VALIDATED);
}