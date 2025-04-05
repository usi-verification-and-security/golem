/*
 * Copyright (c) 2022-2025, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include <gtest/gtest.h>
#include "TestTemplate.h"

#include "Validator.h"
#include "engine/Common.h"
#include "engine/IMC.h"
#include "engine/Spacer.h"
#include "engine/TPA.h"
#include "graph/ChcGraphBuilder.h"
#include "transformers/BasicTransformationPipelines.h"
#include "transformers/ConstraintSimplifier.h"
#include "transformers/EdgeInliner.h"
#include "transformers/FalseClauseRemoval.h"
#include "transformers/MultiEdgeMerger.h"
#include "transformers/NestedLoopTransformation.h"
#include "transformers/NodeEliminator.h"
#include "transformers/RemoveUnreachableNodes.h"
#include "transformers/SimpleChainSummarizer.h"
#include "transformers/TransformationPipeline.h"
#include "utils/SmtSolver.h"

using namespace golem;

class Transformer_New_Test : public LIAEngineTest {
};

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
    PTRef currentS1, currentS2, currentS3, nextS1, nextS2, nextS3;
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
        currentS3 = logic.mkUninterpFun(s3, {x});
        nextS1 = logic.mkUninterpFun(s1, {xp});
        nextS2 = logic.mkUninterpFun(s2, {xp});
        nextS3 = logic.mkUninterpFun(s3, {xp});
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
    auto hyperGraph = systemToGraph(system);
    auto originalGraph = *hyperGraph;
    auto [summarizedGraph, translator] = SimpleChainSummarizer().transform(std::move(hyperGraph));
    ValidityWitness witness{
        {{summarizedGraph->getEntry(), logic.getTerm_true()}, {summarizedGraph->getExit(), logic.getTerm_false()}}
    };
    auto translatedWitness = translator->translate(witness);
    Validator validator(logic);
    VerificationResult result(VerificationAnswer::SAFE, translatedWitness);
    ASSERT_EQ(validator.validate(originalGraph, result), Validator::Result::VALIDATED);
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
    auto originalGraph = *hypergraph;
    TransformationPipeline::pipeline_t pipeline;
    pipeline.push_back(std::make_unique<ConstraintSimplifier>());
    pipeline.push_back(std::make_unique<SimpleChainSummarizer>());
    TransformationPipeline transformations(std::move(pipeline));
    auto [newGraph, translator] = transformations.transform(std::move(hypergraph));
    VersionManager manager{logic};
    PTRef predicate = manager.sourceFormulaToBase(newGraph->getStateVersion(s2));
    PTRef var = logic.getPterm(predicate)[0];
    ValidityWitness witness{
        {
            {newGraph->getEntry(), logic.getTerm_true()}, {s2, logic.mkGeq(var, zero)},
            {newGraph->getExit(), logic.getTerm_false()}
        }
    };
    auto translatedWitness = translator->translate(witness);
    Validator validator(logic);
    VerificationResult result(VerificationAnswer::SAFE, translatedWitness);
    ASSERT_EQ(validator.validate(originalGraph, result), Validator::Result::VALIDATED);
}

TEST_F(Transformer_test, test_DoNotSummarizeLoop_TwoVertices) {
    ChcSystem system;
    system.addUninterpretedPredicate(s1);
    system.addUninterpretedPredicate(s2);
    system.addClause( // x = 0 => S1(x)
        ChcHead{UninterpretedPredicate{currentS1}},
        ChcBody{{logic.mkEq(x, zero)}, {}});
    system.addClause( // S1(x) and x = 1 and x' = 0 => S2(x')
        ChcHead{UninterpretedPredicate{nextS2}},
        ChcBody{{logic.mkAnd(logic.mkEq(xp, zero), logic.mkEq(x, one))}, {UninterpretedPredicate{currentS1}}}
    );
    system.addClause( // S2(x) and x' = 1 and x = 0 => S1(x')
        ChcHead{UninterpretedPredicate{nextS1}},
        ChcBody{{logic.mkAnd(logic.mkEq(xp, one), logic.mkEq(x, zero))}, {UninterpretedPredicate{currentS2}}}
    );
    system.addClause( // S1(x) and x = 1 => false
        ChcHead{UninterpretedPredicate{logic.getTerm_false()}},
        ChcBody{{logic.mkEq(x, one)}, {UninterpretedPredicate{currentS1}}}
    );
    auto hypergraph = systemToGraph(system);
    auto originalGraph = *hypergraph;
    TransformationPipeline::pipeline_t pipeline;
    pipeline.push_back(std::make_unique<ConstraintSimplifier>());
    pipeline.push_back(std::make_unique<SimpleChainSummarizer>());
    TransformationPipeline transformations(std::move(pipeline));
    auto [newGraph, translator] = transformations.transform(std::move(hypergraph));
    auto vertices = newGraph->getVertices();
    // Simple chain summarizer MUST NOT summarize the loop s1->s2->s1!
    EXPECT_EQ(vertices.size(), 4);
    Options options;
    options.addOption(Options::COMPUTE_WITNESS, "true");
    auto res = Spacer(logic, options).solve(*newGraph);
    ASSERT_EQ(res.getAnswer(), VerificationAnswer::SAFE);
    res = translator->translate(std::move(res));
    Validator validator(logic);
    EXPECT_EQ(validator.validate(originalGraph, res), Validator::Result::VALIDATED);
}

TEST_F(Transformer_test, test_DoNotSummarizeLoop_ThreeVertices) {
    ChcSystem system;
    system.addUninterpretedPredicate(s1);
    system.addUninterpretedPredicate(s2);
    system.addUninterpretedPredicate(s3);
    system.addClause( // x = 0 => S1(x)
        ChcHead{UninterpretedPredicate{currentS1}},
        ChcBody{{logic.mkEq(x, zero)}, {}});
    system.addClause( // S1(x) and x = 1 and x' = 0 => S2(x')
        ChcHead{UninterpretedPredicate{nextS2}},
        ChcBody{{logic.mkAnd(logic.mkEq(xp, zero), logic.mkEq(x, one))}, {UninterpretedPredicate{currentS1}}}
    );
    system.addClause( // S2(x) and x = 0 and x' = 0 => S3(x')
        ChcHead{UninterpretedPredicate{nextS3}},
        ChcBody{{logic.mkAnd(logic.mkEq(xp, zero), logic.mkEq(x, zero))}, {UninterpretedPredicate{currentS2}}}
    );
    system.addClause( // S3(x) and x' = 1 and x = 0 => S1(x')
        ChcHead{UninterpretedPredicate{nextS1}},
        ChcBody{{logic.mkAnd(logic.mkEq(xp, one), logic.mkEq(x, zero))}, {UninterpretedPredicate{currentS3}}}
    );
    system.addClause( // S1(x) and x = 1 => false
        ChcHead{UninterpretedPredicate{logic.getTerm_false()}},
        ChcBody{{logic.mkEq(x, one)}, {UninterpretedPredicate{currentS1}}}
    );
    auto hypergraph = systemToGraph(system);
    auto originalGraph = *hypergraph;
    TransformationPipeline::pipeline_t pipeline;
    pipeline.push_back(std::make_unique<ConstraintSimplifier>());
    pipeline.push_back(std::make_unique<SimpleChainSummarizer>());
    TransformationPipeline transformations(std::move(pipeline));
    auto [newGraph, translator] = transformations.transform(std::move(hypergraph));
    auto vertices = newGraph->getVertices();
    // Simple chain summarizer MUST NOT summarize the full loop s1->s2->s3->s1!
    EXPECT_GT(vertices.size(), 3);
    Options options;
    options.addOption(Options::COMPUTE_WITNESS, "true");
    auto res = Spacer(logic, options).solve(*newGraph);
    ASSERT_EQ(res.getAnswer(), VerificationAnswer::SAFE);
    res = translator->translate(std::move(res));
    Validator validator(logic);
    EXPECT_EQ(validator.validate(originalGraph, res), Validator::Result::VALIDATED);
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
    auto originalGraph = *hypergraph;
    TransformationPipeline::pipeline_t pipeline;
    pipeline.push_back(std::make_unique<ConstraintSimplifier>());
    pipeline.push_back(std::make_unique<SimpleChainSummarizer>());
    TransformationPipeline transformations(std::move(pipeline));
    auto [newGraph, translator] = transformations.transform(std::move(hypergraph));
    hypergraph = std::move(newGraph);
    auto res = Spacer(logic, options).solve(*hypergraph);
    ASSERT_EQ(res.getAnswer(), VerificationAnswer::SAFE);
    res = translator->translate(std::move(res));
    Validator validator(logic);
    EXPECT_EQ(validator.validate(originalGraph, res), Validator::Result::VALIDATED);
}

TEST_F(Transformer_test, test_ChainSummarizer_TwoStepChain_Unsafe) {
    ChcSystem system;
    system.addUninterpretedPredicate(s1);
    system.addClause( // x' >= 0 => S1(x')
        ChcHead{UninterpretedPredicate{nextS1}},
        ChcBody{{logic.mkGeq(xp, zero)}, {}});
    system.addClause( // S1(y) and y >= 10 => false
        ChcHead{UninterpretedPredicate{logic.getTerm_false()}},
        ChcBody{{logic.mkGeq(y, logic.mkIntConst(10))}, {UninterpretedPredicate{logic.mkUninterpFun(s1, {y})}}}
    );
    auto hyperGraph = systemToGraph(system);
    auto originalGraph = *hyperGraph;
    auto [summarizedGraph, translator] = SimpleChainSummarizer().transform(std::move(hyperGraph));
    Options options;
    options.addOption(Options::COMPUTE_WITNESS, "true");
    auto res = Spacer(logic, options).solve(*summarizedGraph);
    ASSERT_EQ(res.getAnswer(), VerificationAnswer::UNSAFE);
    Validator validator(logic);
    ASSERT_EQ(validator.validate(*summarizedGraph, res), Validator::Result::VALIDATED);
    auto translatedWitness = translator->translate(res.getInvalidityWitness());
    VerificationResult result(VerificationAnswer::UNSAFE, translatedWitness);
    ASSERT_EQ(validator.validate(originalGraph, result), Validator::Result::VALIDATED);
}

TEST_F(Transformer_test, test_ChainSummarizer_ThreeStepChain_Unsafe) {
    ChcSystem system;
    system.addUninterpretedPredicate(s1);
    system.addUninterpretedPredicate(s2);
    system.addClause( // x' < 0 => S1(x')
        ChcHead{UninterpretedPredicate{nextS1}},
        ChcBody{{logic.mkLt(xp, zero)}, {}});
    system.addClause( // S1(x) and x' = x - 1 => S2(x')
        ChcHead{UninterpretedPredicate{nextS2}},
        ChcBody{{logic.mkEq(xp, logic.mkMinus(x, one))}, {UninterpretedPredicate{currentS1}}}
    );
    system.addClause( // S2(y) and y < -10 => false
        ChcHead{UninterpretedPredicate{logic.getTerm_false()}},
        ChcBody{{logic.mkLt(y, logic.mkIntConst(-10))}, {UninterpretedPredicate{logic.mkUninterpFun(s2, {y})}}}
    );
    auto hyperGraph = systemToGraph(system);
    auto originalGraph = *hyperGraph;
    auto [summarizedGraph, translator] = SimpleChainSummarizer().transform(std::move(hyperGraph));
    Options options;
    options.addOption(Options::COMPUTE_WITNESS, "true");
    auto res = Spacer(logic, options).solve(*summarizedGraph);
    ASSERT_EQ(res.getAnswer(), VerificationAnswer::UNSAFE);
    Validator validator(logic);
    ASSERT_EQ(validator.validate(*summarizedGraph, res), Validator::Result::VALIDATED);
    auto translatedWitness = translator->translate(res.getInvalidityWitness());
    VerificationResult result(VerificationAnswer::UNSAFE, translatedWitness);
    ASSERT_EQ(validator.validate(originalGraph, result), Validator::Result::VALIDATED);
}

TEST_F(Transformer_test, test_ChainSummarizer_TwoChains_Unsafe) {
    ChcSystem system;
    SymRef s4 = logic.declareFun("s4", logic.getSort_bool(), {logic.getSort_int()});
    system.addUninterpretedPredicate(s1);
    system.addUninterpretedPredicate(s2);
    system.addUninterpretedPredicate(s3);
    system.addUninterpretedPredicate(s4);
    system.addClause( // x' < 0 => S1(x')
        ChcHead{UninterpretedPredicate{nextS1}},
        ChcBody{{logic.mkLt(xp, zero)}, {}});
    system.addClause( // S1(x) and x' = x - 1 => S2(x')
        ChcHead{UninterpretedPredicate{nextS2}},
        ChcBody{{logic.mkEq(xp, logic.mkMinus(x, one))}, {UninterpretedPredicate{currentS1}}}
    );
    system.addClause( // x' > 0 => S3(x')
        ChcHead{UninterpretedPredicate{logic.mkUninterpFun(s3, {xp})}},
        ChcBody{{logic.mkGt(xp, zero)}, {}});
    system.addClause( // S3(x) and x' = x + 1 => S4(x')
        ChcHead{UninterpretedPredicate{logic.mkUninterpFun(s4,{xp})}},
        ChcBody{{logic.mkEq(xp, logic.mkPlus(x, one))}, {UninterpretedPredicate{logic.mkUninterpFun(s3, {x})}}}
    );
    system.addClause( // S2(x) and S4(y) and x + y = 0 => false
        ChcHead{UninterpretedPredicate{logic.getTerm_false()}},
        ChcBody{{logic.mkEq(logic.mkPlus(x,y), zero)}, {UninterpretedPredicate{logic.mkUninterpFun(s2, {x})}, UninterpretedPredicate{logic.mkUninterpFun(s4, {y})}}}
    );
    auto hyperGraph = systemToGraph(system);
    auto originalGraph = *hyperGraph;
    auto [summarizedGraph, translator] = SimpleChainSummarizer().transform(std::move(hyperGraph));
    Options options;
    options.addOption(Options::COMPUTE_WITNESS, "true");
    auto res = Spacer(logic, options).solve(*summarizedGraph);
    ASSERT_EQ(res.getAnswer(), VerificationAnswer::UNSAFE);
    Validator validator(logic);
//    res.getInvalidityWitness().print(std::cout, logic);
    ASSERT_EQ(validator.validate(*summarizedGraph, res), Validator::Result::VALIDATED);
    auto translatedWitness = translator->translate(res.getInvalidityWitness());
//    translatedWitness.print(std::cout, logic);
    VerificationResult result(VerificationAnswer::UNSAFE, translatedWitness);
    ASSERT_EQ(validator.validate(originalGraph, result), Validator::Result::VALIDATED);
}

TEST_F(Transformer_test, test_ChainSummarizer_SameChainTwice_SafeFact_Unsafe) {
    ChcSystem system;
    system.addUninterpretedPredicate(s1);
    system.addClause( // x' >= 0 => S1(x')
        ChcHead{UninterpretedPredicate{nextS1}},
        ChcBody{{logic.mkGeq(xp, zero)}, {}});
    system.addClause( // S1(x) and x' = x + 1 => S2(x')
        ChcHead{UninterpretedPredicate{nextS2}},
        ChcBody{{logic.mkEq(xp, logic.mkPlus(x, one))}, {UninterpretedPredicate{currentS1}}}
    );
    system.addClause( // S2(x) and  S2(y) and x = y => false
        ChcHead{UninterpretedPredicate{logic.getTerm_false()}},
        ChcBody{{logic.mkEq(x,y)}, {UninterpretedPredicate{currentS2}, UninterpretedPredicate{logic.mkUninterpFun(s2, {y})}}}
    );
    auto hyperGraph = systemToGraph(system);
    auto originalGraph = *hyperGraph;
    auto [summarizedGraph, translator] = SimpleChainSummarizer().transform(std::move(hyperGraph));
    Options options;
    options.addOption(Options::COMPUTE_WITNESS, "true");
    auto res = Spacer(logic, options).solve(*summarizedGraph);
    ASSERT_EQ(res.getAnswer(), VerificationAnswer::UNSAFE);
//    res.getInvalidityWitness().print(std::cout, logic);
    Validator validator(logic);
    ASSERT_EQ(validator.validate(*summarizedGraph, res), Validator::Result::VALIDATED);
    auto translatedWitness = translator->translate(res.getInvalidityWitness());
//    translatedWitness.print(std::cout, logic);
    VerificationResult result(VerificationAnswer::UNSAFE, translatedWitness);
    ASSERT_EQ(validator.validate(originalGraph, result), Validator::Result::VALIDATED);
}

TEST_F(Transformer_test, test_ChainSummarizer_SameChainTwice_DifferentFact_Unsafe) {
    ChcSystem system;
    system.addUninterpretedPredicate(s1);
    system.addClause( // x' >= 0 => S1(x')
        ChcHead{UninterpretedPredicate{nextS1}},
        ChcBody{{logic.mkGeq(xp, zero)}, {}});
    system.addClause( // S1(x) and x' = x + 1 => S2(x')
        ChcHead{UninterpretedPredicate{nextS2}},
        ChcBody{{logic.mkEq(xp, logic.mkPlus(x, one))}, {UninterpretedPredicate{currentS1}}}
    );
    system.addClause( // S2(x) and  S2(y) and x != y => false
        ChcHead{UninterpretedPredicate{logic.getTerm_false()}},
        ChcBody{{logic.mkNot(logic.mkEq(x,y))}, {UninterpretedPredicate{currentS2}, UninterpretedPredicate{logic.mkUninterpFun(s2, {y})}}}
    );
    auto hyperGraph = systemToGraph(system);
    auto originalGraph = *hyperGraph;
    auto [summarizedGraph, translator] = SimpleChainSummarizer().transform(std::move(hyperGraph));
    Options options;
    options.addOption(Options::COMPUTE_WITNESS, "true");
    auto res = Spacer(logic, options).solve(*summarizedGraph);
    ASSERT_EQ(res.getAnswer(), VerificationAnswer::UNSAFE);
//    res.getInvalidityWitness().print(std::cout, logic);
    Validator validator(logic);
    ASSERT_EQ(validator.validate(*summarizedGraph, res), Validator::Result::VALIDATED);
    auto translatedWitness = translator->translate(res.getInvalidityWitness());
//    translatedWitness.print(std::cout, logic);
    VerificationResult result(VerificationAnswer::UNSAFE, translatedWitness);
    ASSERT_EQ(validator.validate(originalGraph, result), Validator::Result::VALIDATED);
}

TEST_F(Transformer_test, test_ChainSummarizer_UnreachableLoop) {
    ChcSystem system;
    system.addUninterpretedPredicate(s1);
    system.addClause( // S1(x) and x' = x + 1 => S1(x')
        ChcHead{UninterpretedPredicate{nextS1}},
        ChcBody{{logic.mkEq(xp, logic.mkPlus(x, one))}, {UninterpretedPredicate{currentS1}}}
    );
    system.addClause( // true => false
        ChcHead{UninterpretedPredicate{logic.getTerm_false()}},
        ChcBody{{logic.getTerm_true()}, {}}
    );
    auto hyperGraph = systemToGraph(system);
    auto originalGraph = *hyperGraph;
    auto [summarizedGraph, translator] = SimpleChainSummarizer().transform(std::move(hyperGraph));
    ASSERT_EQ(summarizedGraph->getEdges().size(), 2);
}

TEST_F(Transformer_test, test_NodeEliminator_PredicateWithoutVariables) {
    SymRef t_sym = logic.declareFun("t", logic.getSort_bool(), {});
    PTRef t = logic.mkUninterpFun(t_sym, {});
    ChcSystem system;
    system.addUninterpretedPredicate(s1);
    system.addClause( // x' >= 0 => S1(x')
        ChcHead{UninterpretedPredicate{nextS1}},
        ChcBody{{logic.mkGeq(xp, zero)}, {}});
    system.addClause( // S1(x) and x < 0 => S2(x)
        ChcHead{UninterpretedPredicate{currentS2}},
        ChcBody{{logic.mkLt(x, zero)}, {UninterpretedPredicate{currentS1}}});
    system.addClause( // S2(x) => T
        ChcHead{UninterpretedPredicate{t}},
        ChcBody{{logic.getTerm_true()}, {UninterpretedPredicate{currentS2}}});
    system.addClause( // T => false
        ChcHead{UninterpretedPredicate{logic.getTerm_false()}},
        ChcBody{{logic.getTerm_true()}, {UninterpretedPredicate{t}}}
    );
    auto hyperGraph = systemToGraph(system);
    auto originalGraph = *hyperGraph;
    SimpleNodeEliminator transformation;
    auto [transformedGraph, backtranslator] = transformation.transform(std::move(hyperGraph));
    ASSERT_EQ(transformedGraph->getEdges().size(), 1);
    ValidityWitness witness = backtranslator->translate(ValidityWitness::trivialWitness(*transformedGraph));
    Validator validator(logic);
    auto res = validator.validate(originalGraph, VerificationResult(VerificationAnswer::SAFE, witness));
    ASSERT_EQ(res, Validator::Result::VALIDATED);
}

TEST_F(Transformer_New_Test, test_NodeEliminator_SecondEdgeUsed) {
    SymRef p = mkPredicateSymbol("P", {intSort()});
    PTRef current = instantiatePredicate(p, {x});
    PTRef next = instantiatePredicate(p, {xp});

    // x = 0 => P(x)
    // x = 1 => P(x)
    // P(x) and x = 1 => false
    std::vector<ChClause> clauses{
        {
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{{logic->mkEq(xp, zero)}, {}}
        },
        {
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{{logic->mkEq(xp, one)}, {}}
        },
        {
            ChcHead{UninterpretedPredicate{logic->getTerm_false()}},
            ChcBody{{logic->mkEq(x, one)}, {UninterpretedPredicate{current}}}
        }};

    for (auto const & clause : clauses) { system.addClause(clause); }
    Logic & logic = *this->logic;
    auto normalizedSystem = Normalizer(logic).normalize(system);
    auto hyperGraph = ChcGraphBuilder(logic).buildGraph(normalizedSystem);
    auto originalGraph = *hyperGraph;
    SimpleNodeEliminator transformation;
    auto [transformedGraph, translator] = transformation.transform(std::move(hyperGraph));
    ASSERT_EQ(transformedGraph->getEdges().size(), 2);
    options.addOption(Options::COMPUTE_WITNESS, "true");
    auto res = IMC(logic, options).solve(*transformedGraph);
    auto answer = res.getAnswer();
    ASSERT_EQ(answer, VerificationAnswer::UNSAFE);
    auto translatedWitness = translator->translate(res.getInvalidityWitness());
    VerificationResult translatedResult(VerificationAnswer::UNSAFE, translatedWitness);
    EXPECT_EQ(Validator(logic).validate(originalGraph, translatedResult), Validator::Result::VALIDATED);
}

TEST_F(Transformer_New_Test, test_SimpleNodeEliminator_HyperEdge_Safe) {
    Options options;
    options.addOption(Options::LOGIC, "QF_LIA");
    options.addOption(Options::COMPUTE_WITNESS, "true");
    SymRef s1 = mkPredicateSymbol("s1", {intSort()});
    SymRef s2 = mkPredicateSymbol("s2", {intSort()});
    PTRef currentOne = instantiatePredicate(s1, {x});
    PTRef currentTwo = instantiatePredicate(s2, {y});
    // x > 0 => S1(x)
    // y > 0 => S2(y)
    // S1(x) and S2(y) and x + y < 0 => false

    std::vector<ChClause> clauses{
        {
            ChcHead{UninterpretedPredicate{currentOne}},
            ChcBody{{logic->mkGt(x, zero)}, {}}
        },
        {
            ChcHead{UninterpretedPredicate{currentTwo}},
            ChcBody{{logic->mkGt(y, zero)}, {}}
        },
        {
            ChcHead{UninterpretedPredicate{logic->getTerm_false()}},
            ChcBody{{logic->mkLt(logic->mkPlus(x, y), zero)}, {UninterpretedPredicate{currentOne}, UninterpretedPredicate{currentTwo}}}
        }};

    for (auto const & clause : clauses) { system.addClause(clause); }

    Logic & logic = *this->logic;
    auto normalizedSystem = Normalizer(logic).normalize(system);
    auto hyperGraph = ChcGraphBuilder(logic).buildGraph(normalizedSystem);
    auto originalGraph = *hyperGraph;
    SimpleNodeEliminator transformation;
    auto [transformedGraph, translator] = transformation.transform(std::move(hyperGraph));
    ASSERT_EQ(transformedGraph->getEdges().size(), 1);
    auto edge = transformedGraph->getEdges().at(0);
    ASSERT_EQ(edge.to, transformedGraph->getExit());
    ASSERT_EQ(edge.from.size(), 1);
    ASSERT_EQ(edge.from.at(0), transformedGraph->getEntry());
    auto translatedWitness = translator->translate(ValidityWitness::trivialWitness(*transformedGraph));
    VerificationResult translatedResult(VerificationAnswer::SAFE, translatedWitness);
    Validator validator(logic);
    EXPECT_EQ(validator.validate(originalGraph, translatedResult), Validator::Result::VALIDATED);
}

TEST_F(Transformer_New_Test, test_SimpleNodeEliminator_HyperEdge_Unsafe) {
    Options options;
    options.addOption(Options::LOGIC, "QF_LIA");
    options.addOption(Options::COMPUTE_WITNESS, "true");
    SymRef s1 = mkPredicateSymbol("s1", {intSort()});
    SymRef s2 = mkPredicateSymbol("s2", {intSort()});
    PTRef currentOne = instantiatePredicate(s1, {x});
    PTRef currentTwo = instantiatePredicate(s2, {y});
    // x > 0 => S1(x)
    // y > 0 => S2(y)
    // S1(x) and S2(y) and x + y > 1 => false

    std::vector<ChClause> clauses{
        {
            ChcHead{UninterpretedPredicate{currentOne}},
            ChcBody{{logic->mkGt(x, zero)}, {}}
        },
        {
            ChcHead{UninterpretedPredicate{currentTwo}},
            ChcBody{{logic->mkGt(y, zero)}, {}}
        },
        {
            ChcHead{UninterpretedPredicate{logic->getTerm_false()}},
            ChcBody{{logic->mkGt(logic->mkPlus(x, y), one)}, {UninterpretedPredicate{currentOne}, UninterpretedPredicate{currentTwo}}}
        }};

    for (auto const & clause : clauses) { system.addClause(clause); }

    Logic & logic = *this->logic;
    auto normalizedSystem = Normalizer(logic).normalize(system);
    auto hyperGraph = ChcGraphBuilder(logic).buildGraph(normalizedSystem);
    auto originalGraph = *hyperGraph;
    SimpleNodeEliminator transformation;
    auto [transformedGraph, translator] = transformation.transform(std::move(hyperGraph));
    ASSERT_EQ(transformedGraph->getEdges().size(), 1);
    auto edge = transformedGraph->getEdges().at(0);
    ASSERT_EQ(edge.to, transformedGraph->getExit());
    ASSERT_EQ(edge.from.size(), 1);
    ASSERT_EQ(edge.from.at(0), transformedGraph->getEntry());
    auto normalGraph = transformedGraph->toNormalGraph();
    auto res = solveTrivial(*normalGraph);
    ASSERT_EQ(res.getAnswer(), VerificationAnswer::UNSAFE);
    auto translatedWitness = translator->translate(res.getInvalidityWitness());
    VerificationResult translatedResult(VerificationAnswer::UNSAFE, translatedWitness);
    Validator validator(logic);
    EXPECT_EQ(validator.validate(originalGraph, translatedResult), Validator::Result::VALIDATED);
}

TEST_F(Transformer_New_Test, test_SimpleNodeEliminator_HyperEdgeBooleanConstraint_Safe) {
    Options options;
    options.addOption(Options::LOGIC, "QF_LIA");
    options.addOption(Options::COMPUTE_WITNESS, "true");
    SymRef s1 = mkPredicateSymbol("s1", {intSort()});
    SymRef s2 = mkPredicateSymbol("s2", {boolSort()});
    PTRef b = mkBoolVar("b");
    PTRef currentOne = instantiatePredicate(s1, {x});
    PTRef currentTwo = instantiatePredicate(s2, {b});
    // x > 0 => S1(x)
    // b => S2(b)
    // S1(x) and S2(b) and x = 1 and ~b => false

    std::vector<ChClause> clauses{
        {
            ChcHead{UninterpretedPredicate{currentTwo}},
            ChcBody{{b}, {}}
        },
        {
            ChcHead{UninterpretedPredicate{currentOne}},
            ChcBody{{logic->mkGt(x, zero)}, {}}
        },
        {
            ChcHead{UninterpretedPredicate{logic->getTerm_false()}},
            ChcBody{{logic->mkAnd(logic->mkNot(b), logic->mkEq(x, one))}, {UninterpretedPredicate{currentOne}, UninterpretedPredicate{currentTwo}}}
        }};

    for (auto const & clause : clauses) { system.addClause(clause); }

    Logic & logic = *this->logic;
    auto normalizedSystem = Normalizer(logic).normalize(system);
    auto hyperGraph = ChcGraphBuilder(logic).buildGraph(normalizedSystem);
    auto originalGraph = *hyperGraph;
    SimpleNodeEliminator transformation;
    auto [transformedGraph, translator] = transformation.transform(std::move(hyperGraph));
    ASSERT_EQ(transformedGraph->getEdges().size(), 1);
    auto edge = transformedGraph->getEdges().at(0);
    ASSERT_EQ(edge.to, transformedGraph->getExit());
    ASSERT_EQ(edge.from.size(), 1);
    ASSERT_EQ(edge.from.at(0), transformedGraph->getEntry());
    auto translatedWitness = translator->translate(ValidityWitness::trivialWitness(*transformedGraph));
    VerificationResult translatedResult(VerificationAnswer::SAFE, translatedWitness);
    Validator validator(logic);
    EXPECT_EQ(validator.validate(originalGraph, translatedResult), Validator::Result::VALIDATED);
}

TEST_F(Transformer_New_Test, test_SimpleNodeEliminator_AuxiliaryVariables) {
    Options options;
    options.addOption(Options::LOGIC, "QF_LIA");
    options.addOption(Options::COMPUTE_WITNESS, "true");
    PTRef z = logic->mkIntVar("z");
    SymRef s1 = mkPredicateSymbol("s1", {intSort(), intSort()});
    SymRef s2 = mkPredicateSymbol("s2", {intSort(), intSort()});
    PTRef a1 = logic->mkBoolVar("a1");
    PTRef a2 = logic->mkBoolVar("a2");
    // x < y => S1(x,y)
    // S1(x,y) and x > z => S2(z,y)
    // S2(1,3) => A1
    // S2(0,2) => A2
    // A1 and A2 => false

    std::vector<ChClause> clauses{
        {
            ChcHead{UninterpretedPredicate{instantiatePredicate(s1, {x,y})}},
            ChcBody{{logic->mkLt(x,y)}, {}}
        },
        {
            ChcHead{UninterpretedPredicate{instantiatePredicate(s2, {z,y})}},
            ChcBody{{logic->mkGt(x, z)}, {UninterpretedPredicate{instantiatePredicate(s1, {x,y})}}}
        },
        {
            ChcHead{UninterpretedPredicate{a1}},
            ChcBody{{logic->getTerm_true()}, {UninterpretedPredicate{instantiatePredicate(s2, {one, logic->mkIntConst(3)})}}}
        },
        {
            ChcHead{UninterpretedPredicate{a2}},
            ChcBody{{logic->getTerm_true()}, {UninterpretedPredicate{instantiatePredicate(s2, {zero, logic->mkIntConst(2)})}}}
        },
        {
            ChcHead{UninterpretedPredicate{logic->getTerm_false()}},
            ChcBody{{logic->getTerm_true()}, {UninterpretedPredicate{a1}, UninterpretedPredicate{a2}}}
        }
    };

    for (auto const & clause : clauses) { system.addClause(clause); }

    Logic & logic = *this->logic;
    auto normalizedSystem = Normalizer(logic).normalize(system);
    auto hyperGraph = ChcGraphBuilder(logic).buildGraph(normalizedSystem);
    auto originalGraph = *hyperGraph;
    // We first apply SimpleChainSummarizer to obtain an edge with auxiliary variables that do not have a name starting with "aux"
    TransformationPipeline::pipeline_t pipeline;
    pipeline.push_back(std::make_unique<SimpleChainSummarizer>());
    pipeline.push_back(std::make_unique<SimpleNodeEliminator>());
    TransformationPipeline transformations(std::move(pipeline));
    auto [transformedGraph, translator] = transformations.transform(std::move(hyperGraph));
    ASSERT_EQ(transformedGraph->getEdges().size(), 1);
    auto edge = transformedGraph->getEdges().at(0);
    ASSERT_EQ(edge.to, transformedGraph->getExit());
    ASSERT_EQ(edge.from.size(), 1);
    ASSERT_EQ(edge.from.at(0), transformedGraph->getEntry());
    // The edge has to be satisfiable
    SMTSolver solver(logic);
    solver.assertProp(edge.fla.fla);
    ASSERT_EQ(solver.check(), SMTSolver::Answer::SAT);
}

TEST_F(Transformer_New_Test, test_SimpleNodeEliminator_AuxiliaryVariables2) {
    Options options;
    options.addOption(Options::LOGIC, "QF_LIA");
    options.addOption(Options::COMPUTE_WITNESS, "true");
    SymRef s1 = mkPredicateSymbol("s1", {intSort(), intSort()});
    SymRef s2 = mkPredicateSymbol("s2", {intSort()});
    PTRef a1 = logic->mkBoolVar("a1");
    // x < y => S1(x,y)
    // S1(x,1) => A1
    // A1 and S1(x,7) and x > y => S2(y)
    // S2(3) => false

    std::vector<ChClause> clauses{
        {
            ChcHead{UninterpretedPredicate{instantiatePredicate(s1, {x,y})}},
            ChcBody{{logic->mkLt(x,y)}, {}}
        },
        {
            ChcHead{UninterpretedPredicate{a1}},
            ChcBody{{logic->getTerm_true()}, {UninterpretedPredicate{instantiatePredicate(s1, {x, one})}}}
        },
        {
            ChcHead{UninterpretedPredicate{instantiatePredicate(s2, {y})}},
            ChcBody{{logic->mkGt(x,y)}, {UninterpretedPredicate{instantiatePredicate(s1, {x, logic->mkIntConst(7)})}, UninterpretedPredicate{a1}}}
        },
        {
            ChcHead{UninterpretedPredicate{logic->getTerm_false()}},
            ChcBody{{logic->getTerm_true()}, {UninterpretedPredicate{instantiatePredicate(s2, {logic->mkIntConst(3)})}}}
        }
    };

    for (auto const & clause : clauses) { system.addClause(clause); }

    Logic & logic = *this->logic;
    auto normalizedSystem = Normalizer(logic).normalize(system);
    auto hyperGraph = ChcGraphBuilder(logic).buildGraph(normalizedSystem);
    auto originalGraph = *hyperGraph;
    TransformationPipeline::pipeline_t pipeline;
    pipeline.push_back(std::make_unique<SimpleNodeEliminator>());
    TransformationPipeline transformations(std::move(pipeline));
    auto [transformedGraph, translator] = transformations.transform(std::move(hyperGraph));
    ASSERT_EQ(transformedGraph->getEdges().size(), 1);
    auto edge = transformedGraph->getEdges().at(0);
    ASSERT_EQ(edge.to, transformedGraph->getExit());
    ASSERT_EQ(edge.from.size(), 1);
    ASSERT_EQ(edge.from.at(0), transformedGraph->getEntry());
    // The edge has to be satisfiable
    SMTSolver solver(logic);
    solver.assertProp(edge.fla.fla);
    ASSERT_EQ(solver.check(), SMTSolver::Answer::SAT);
}

TEST_F(Transformer_New_Test, test_SimpleNodeEliminator_PredicateClash_Unsafe) {
    Options options;
    options.addOption(Options::LOGIC, "QF_LIA");
    options.addOption(Options::COMPUTE_WITNESS, "true");
    SymRef p1 = mkPredicateSymbol("p1", {intSort(), intSort()});
    SymRef p2 = mkPredicateSymbol("p2", {intSort()});
    SymRef p3 = mkPredicateSymbol("p3", {intSort()});
    PTRef one = instantiatePredicate(p1, {x, y});
    PTRef two = instantiatePredicate(p2, {x});
    PTRef three = instantiatePredicate(p3, {y});
    // x < y => P1(x,y)
    // P1(x,y) => P2(x)
    // P1(x,y) => P3(y)
    // P2(x) and P3(y) and x = y => false

    std::vector<ChClause> clauses{
        {
            ChcHead{UninterpretedPredicate{one}},
            ChcBody{{logic->mkLt(x,y)}, {}}
        },
        {
            ChcHead{UninterpretedPredicate{two}},
            ChcBody{{logic->getTerm_true()}, {UninterpretedPredicate{one}}}
        },
        {
            ChcHead{UninterpretedPredicate{three}},
            ChcBody{{logic->getTerm_true()}, {UninterpretedPredicate{one}}}
        },
        {
            ChcHead{UninterpretedPredicate{logic->getTerm_false()}},
            ChcBody{{logic->mkEq(x,y)}, {UninterpretedPredicate{two}, UninterpretedPredicate{three}}}
        }};

    for (auto const & clause : clauses) { system.addClause(clause); }

    Logic & logic = *this->logic;
    auto normalizedSystem = Normalizer(logic).normalize(system);
    auto hyperGraph = ChcGraphBuilder(logic).buildGraph(normalizedSystem);
    auto originalGraph = *hyperGraph;
    SimpleNodeEliminator transformation;
    auto [transformedGraph, translator] = transformation.transform(std::move(hyperGraph));
    Spacer engine(logic, options);
    auto res = engine.solve(*transformedGraph);
    ASSERT_EQ(res.getAnswer(), VerificationAnswer::UNSAFE);
    auto translatedWitness = translator->translate(res.getInvalidityWitness());
    VerificationResult translatedResult(VerificationAnswer::UNSAFE, translatedWitness);
    Validator validator(logic);
    EXPECT_EQ(validator.validate(originalGraph, translatedResult), Validator::Result::VALIDATED);
}

TEST_F(Transformer_New_Test, test_MultiEdgeMerger_SimpleUnsafe) {
    Options options;
    options.addOption(Options::LOGIC, "QF_LIA");
    options.addOption(Options::COMPUTE_WITNESS, "true");
    SymRef s1 = mkPredicateSymbol("s1", {intSort(), intSort()});
    PTRef current = instantiatePredicate(s1, {x,y});
    PTRef next = instantiatePredicate(s1, {xp,yp});
    PTRef val = logic->mkIntConst(2);
    // x = 0 and y = 0 => S1(x,y)
    // S1(x,y) and x' = x + 1 => S1(x',y)
    // S1(x,y) and y' = y + 1 => S1(x,y')
    // S1(x,y) and y > 2 and x > 2 => false

    std::vector<ChClause> clauses{
        {
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{{logic->mkAnd(logic->mkEq(xp, zero), logic->mkEq(yp, zero))}, {}}
        },
        {
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{{logic->mkAnd(logic->mkEq(xp, logic->mkPlus(x, one)), logic->mkEq(yp, y))}, {UninterpretedPredicate{current}}}
        },
        {
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{{logic->mkAnd(logic->mkEq(yp, logic->mkPlus(y, one)), logic->mkEq(xp, x))}, {UninterpretedPredicate{current}}}
        },
        {
            ChcHead{UninterpretedPredicate{logic->getTerm_false()}},
            ChcBody{{logic->mkAnd(logic->mkGt(y, val), logic->mkGt(x, val))}, {UninterpretedPredicate{current}}}
        }};

    for (auto const & clause : clauses) { system.addClause(clause); }

    Logic & logic = *this->logic;
    auto normalizedSystem = Normalizer(logic).normalize(system);
    auto hyperGraph = ChcGraphBuilder(logic).buildGraph(normalizedSystem);
    auto originalGraph = *hyperGraph;
    MultiEdgeMerger transformation;
    auto [transformedGraph, translator] = transformation.transform(std::move(hyperGraph));
    ASSERT_EQ(transformedGraph->getEdges().size(), 3);
    auto res = Spacer(logic, options).solve(*transformedGraph);
    auto answer = res.getAnswer();
    ASSERT_EQ(answer, VerificationAnswer::UNSAFE);
    auto translatedWitness = translator->translate(res.getInvalidityWitness());
    VerificationResult translatedResult(VerificationAnswer::UNSAFE, translatedWitness);
    Validator validator(logic);
    EXPECT_EQ(validator.validate(originalGraph, res), Validator::Result::NOT_VALIDATED);
    EXPECT_EQ(validator.validate(originalGraph, translatedResult), Validator::Result::VALIDATED);
}

TEST_F(Transformer_New_Test, test_MultiEdgeMerger_UnsafeWithAuxVars) {
    Options options;
    options.addOption(Options::LOGIC, "QF_LIA");
    options.addOption(Options::COMPUTE_WITNESS, "true");
    SymRef s1 = mkPredicateSymbol("s1", {intSort(), intSort()});
    PTRef current = instantiatePredicate(s1, {x,y});
    PTRef next = instantiatePredicate(s1, {xp,yp});
    PTRef c = mkIntVar("c");
    PTRef val = logic->mkIntConst(2);
    // x = 0 and y = 0 => S1(x,y)
    // S1(x,y) and x' = x + c and c > 0 => S1(x',y)
    // S1(x,y) and y' = y + 1 => S1(x,y')
    // S1(x,y) and y > 2 and x > 2 => false

    std::vector<ChClause> clauses{
        {
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{{logic->mkAnd(logic->mkEq(xp, zero), logic->mkEq(yp, zero))}, {}}
        },
        {
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{{logic->mkAnd({logic->mkEq(xp, logic->mkPlus(x, c)), logic->mkEq(yp, y), logic->mkGt(c, zero)})}, {UninterpretedPredicate{current}}}
        },
        {
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{{logic->mkAnd(logic->mkEq(yp, logic->mkPlus(y, one)), logic->mkEq(xp, x))}, {UninterpretedPredicate{current}}}
        },
        {
            ChcHead{UninterpretedPredicate{logic->getTerm_false()}},
            ChcBody{{logic->mkAnd(logic->mkGt(y, val), logic->mkGt(x, val))}, {UninterpretedPredicate{current}}}
        }};

    for (auto const & clause : clauses) { system.addClause(clause); }

    Logic & logic = *this->logic;
    auto normalizedSystem = Normalizer(logic).normalize(system);
    auto hyperGraph = ChcGraphBuilder(logic).buildGraph(normalizedSystem);
    auto originalGraph = *hyperGraph;
    MultiEdgeMerger transformation;
    auto [transformedGraph, translator] = transformation.transform(std::move(hyperGraph));
    ASSERT_EQ(transformedGraph->getEdges().size(), 3);
    auto res = Spacer(logic, options).solve(*transformedGraph);
    auto answer = res.getAnswer();
    ASSERT_EQ(answer, VerificationAnswer::UNSAFE);
    auto translatedWitness = translator->translate(res.getInvalidityWitness());
    VerificationResult translatedResult(VerificationAnswer::UNSAFE, translatedWitness);
    Validator validator(logic);
    EXPECT_EQ(validator.validate(originalGraph, translatedResult), Validator::Result::VALIDATED);
}

TEST_F(Transformer_New_Test, test_SummarizerAndUnreachable_WitnessBacktranslation) {
    Options options;
    options.addOption(Options::LOGIC, "QF_LIA");
    options.addOption(Options::COMPUTE_WITNESS, "true");
    SymRef s1 = mkPredicateSymbol("s1", {intSort()});
    SymRef s2 = mkPredicateSymbol("s2", {intSort()});
    SymRef s3 = mkPredicateSymbol("s3", {intSort()});
    SymRef s4 = mkPredicateSymbol("s4", {intSort()});
    SymRef s5 = mkPredicateSymbol("s5", {intSort()});
    PTRef current1 = instantiatePredicate(s1, {x});
    PTRef next1 = instantiatePredicate(s1, {xp});
    PTRef current2 = instantiatePredicate(s2, {x});
    PTRef next2 = instantiatePredicate(s2, {xp});
    PTRef current3 = instantiatePredicate(s3, {x});
    PTRef current4 = instantiatePredicate(s4, {x});
    PTRef current5 = instantiatePredicate(s5, {x});
    // x = 0 => S1(x)
    // x = 0 => S2(x)
    // S1(x) => S3(x)
    // S2(x) => S3(x)
    // S3(x) => S4(x)
    // S4(x) => S5(x)
    // S1(x) and x > 0 => false
    // S2(x) and x > 0 => false

    std::vector<ChClause> clauses{
        {
            ChcHead{UninterpretedPredicate{next1}},
            ChcBody{{logic->mkEq(xp, zero)}, {}}
        },
        {
            ChcHead{UninterpretedPredicate{next2}},
            ChcBody{{logic->mkEq(xp, zero)}, {}}
        },
        {
            ChcHead{UninterpretedPredicate{current3}},
            ChcBody{{logic->getTerm_true()}, {UninterpretedPredicate{current1}}}
        },
        {
            ChcHead{UninterpretedPredicate{current3}},
            ChcBody{{logic->getTerm_true()}, {UninterpretedPredicate{current2}}}
        },
        {
            ChcHead{UninterpretedPredicate{current4}},
            ChcBody{{logic->getTerm_true()}, {UninterpretedPredicate{current3}}}
        },
        {
            ChcHead{UninterpretedPredicate{current5}},
            ChcBody{{logic->getTerm_true()}, {UninterpretedPredicate{current4}}}
        },
        {
            ChcHead{UninterpretedPredicate{logic->getTerm_false()}},
            ChcBody{{logic->mkGt(x, zero)}, {UninterpretedPredicate{current1}}}
        },
        {
            ChcHead{UninterpretedPredicate{logic->getTerm_false()}},
            ChcBody{{logic->mkGt(x, zero)}, {UninterpretedPredicate{current2}}}
        }};

    for (auto const & clause : clauses) { system.addClause(clause); }

    Logic & logic = *this->logic;
    auto normalizedSystem = Normalizer(logic).normalize(system);
    auto hyperGraph = ChcGraphBuilder(logic).buildGraph(normalizedSystem);
    auto originalGraph = *hyperGraph;
    TransformationPipeline::pipeline_t pipeline;
    pipeline.push_back(std::make_unique<SimpleChainSummarizer>());
    pipeline.push_back(std::make_unique<RemoveUnreachableNodes>());
    TransformationPipeline transformations(std::move(pipeline));

    auto [transformedGraph, translator] = transformations.transform(std::move(hyperGraph));
    auto res = Spacer(logic, options).solve(*transformedGraph);
    auto answer = res.getAnswer();
    ASSERT_EQ(answer, VerificationAnswer::SAFE);
    auto translatedWitness = translator->translate(res.getValidityWitness());
    VerificationResult translatedResult(VerificationAnswer::SAFE, translatedWitness);
    Validator validator(logic);
    EXPECT_EQ(validator.validate(originalGraph, translatedResult), Validator::Result::VALIDATED);
}


TEST_F(Transformer_New_Test, test_NestedLoopMerger_SimpleSafe) {
    Options options;
    options.addOption(Options::LOGIC, "QF_LIA");
    options.addOption(Options::COMPUTE_WITNESS, "true");
    options.addOption(Options::SIMPLIFY_NESTED, "true");
    SymRef s1 = mkPredicateSymbol("s1", {intSort(), intSort()});
    SymRef s2 = mkPredicateSymbol("s2", {intSort(), intSort()});
    SymRef s3 = mkPredicateSymbol("s3", {intSort(), intSort()});
    PTRef currentS1 = instantiatePredicate(s1, {x,y});
    PTRef nextS1 = instantiatePredicate(s1, {xp,yp});
    PTRef currentS2 = instantiatePredicate(s2, {x,y});
    PTRef nextS2 = instantiatePredicate(s2, {xp,yp});
    PTRef currentS3 = instantiatePredicate(s3, {x,y});
    PTRef nextS3 = instantiatePredicate(s3, {xp,yp});
    PTRef ten = logic->mkIntConst(10);
    PTRef seven = logic->mkIntConst(7);
    // 0 <= x <= 10 and 0 <= y <= 5 => S1(x,y)
    // S1(x,y) and y < 10 => S2(x,y,z)
    // S2(x,y) and x < 7 and x' = x + 1 and y' = y + 1 => S2(x',y')
    // S2(x,y) and x >= 7 => S3(x,y)
    // S3(x,y) and y > 0 and x' = x - 1 => S3(x',y)
    // S3(x,y) and y <= 0 and y' = y + 1 => S1(x,y')
    // S1(x,y) and y >= 10 and x <= 0 => false

    std::vector<ChClause> clauses{
        {
            ChcHead{UninterpretedPredicate{nextS1}},
            ChcBody{{logic->mkAnd(logic->mkAnd(logic->mkLeq(xp, ten), logic->mkGeq(xp, zero)),
                                  logic->mkAnd(logic->mkLeq(yp, logic->mkIntConst(5)), logic->mkGeq(yp, zero)))}, {}}
        },
        {
            ChcHead{UninterpretedPredicate{nextS2}},
            ChcBody{{logic->mkLt(y, ten)}, {UninterpretedPredicate{currentS1}}}
        },
        {
            ChcHead{UninterpretedPredicate{nextS2}},
            ChcBody{{logic->mkAnd(
                            {logic->mkLt(x, seven),
                            logic->mkEq(xp, logic->mkPlus(x, one)),
                            logic->mkEq(yp, logic->mkPlus(y, one))})},
                    {UninterpretedPredicate{currentS2}}}
        },
        {
            ChcHead{UninterpretedPredicate{nextS3}},
            ChcBody{{logic->mkGeq(x,seven)}, {UninterpretedPredicate{currentS2}}}
        },
        {
            ChcHead{UninterpretedPredicate{nextS3}},
            ChcBody{{logic->mkAnd( logic->mkGt(y, zero), logic->mkEq(xp, logic->mkMinus(x, one)))},
                         {UninterpretedPredicate{currentS3}}}
        },
        {
            ChcHead{UninterpretedPredicate{nextS1}},
            ChcBody{{logic->mkAnd( logic->mkLeq(y, zero), logic->mkEq(yp, logic->mkPlus(y, one)))},
                    {UninterpretedPredicate{currentS3}}}
        },
        {
            ChcHead{UninterpretedPredicate{logic->getTerm_false()}},
            ChcBody{{logic->mkAnd(logic->mkGeq(y, ten), logic->mkLeq(x, zero))}, {UninterpretedPredicate{currentS1}}}
        }};

    for (auto const & clause : clauses) { system.addClause(clause); }

    Logic & logic = *this->logic;
    auto normalizedSystem = Normalizer(logic).normalize(system);
    auto hyperGraph = ChcGraphBuilder(logic).buildGraph(normalizedSystem);
    NestedLoopTransformation NLTransformation;
    auto properGraph = *hyperGraph->toNormalGraph();
    ASSERT_EQ(properGraph.getEdges().size(), 7);
    auto [transformedGraph, preTranslator]= NLTransformation.transform(properGraph);
    ASSERT_EQ(transformedGraph->getEdges().size(), 3);
    auto res = TPAEngine(logic, options, TPACore::SPLIT).solve(*hyperGraph);
    auto answer = res.getAnswer();
    ASSERT_EQ(answer, VerificationAnswer::SAFE);
    Validator validator(logic);
    EXPECT_EQ(validator.validate(*hyperGraph, res), Validator::Result::VALIDATED);
}

TEST_F(Transformer_New_Test, test_NestedLoopMerger_SimpleUnsafe) {
    Options options;
    options.addOption(Options::LOGIC, "QF_LIA");
    options.addOption(Options::COMPUTE_WITNESS, "true");
    options.addOption(Options::SIMPLIFY_NESTED, "true");
    SymRef s1 = mkPredicateSymbol("s1", {intSort(), intSort()});
    SymRef s2 = mkPredicateSymbol("s2", {intSort(), intSort()});
    SymRef s3 = mkPredicateSymbol("s3", {intSort(), intSort()});
    PTRef currentS1 = instantiatePredicate(s1, {x,y});
    PTRef nextS1 = instantiatePredicate(s1, {xp,yp});
    PTRef currentS2 = instantiatePredicate(s2, {x,y});
    PTRef nextS2 = instantiatePredicate(s2, {xp,yp});
    PTRef currentS3 = instantiatePredicate(s3, {x,y});
    PTRef nextS3 = instantiatePredicate(s3, {xp,yp});
    PTRef ten = logic->mkIntConst(10);
    PTRef seven = logic->mkIntConst(7);
    // 0 <= x <= 10 and 0 <= y <= 5 => S1(x,y)
    // S1(x,y) and y < 10 => S2(x,y,z)
    // S2(x,y) and x < 7 and x' = x + 1 and y' = y + 1 => S2(x',y')
    // S2(x,y) and x >= 7 => S3(x,y)
    // S3(x,y) and x > 0 and x' = x - 1 => S3(x',y)
    // S3(x,y) and x <= 0 and y' = y + 1 => S1(x,y')
    // S1(x,y) and y >= 10 and x <= 0 => false

    std::vector<ChClause> clauses{
        {
            ChcHead{UninterpretedPredicate{nextS1}},
            ChcBody{{logic->mkAnd(logic->mkAnd(logic->mkLeq(xp, ten), logic->mkGeq(xp, zero)),
                                  logic->mkAnd(logic->mkLeq(yp, logic->mkIntConst(5)), logic->mkGeq(yp, zero)))}, {}}
        },
        {
            ChcHead{UninterpretedPredicate{nextS2}},
            ChcBody{{logic->mkLt(y, ten)}, {UninterpretedPredicate{currentS1}}}
        },
        {
            ChcHead{UninterpretedPredicate{nextS2}},
            ChcBody{{logic->mkAnd(
                        {logic->mkLt(x, seven),
                         logic->mkEq(xp, logic->mkPlus(x, one)),
                         logic->mkEq(yp, logic->mkPlus(y, one))})},
                    {UninterpretedPredicate{currentS2}}}
        },
        {
            ChcHead{UninterpretedPredicate{nextS3}},
            ChcBody{{logic->mkGeq(x,seven)}, {UninterpretedPredicate{currentS2}}}
        },
        {
            ChcHead{UninterpretedPredicate{nextS3}},
            ChcBody{{logic->mkAnd( logic->mkGt(x, zero), logic->mkEq(xp, logic->mkMinus(x, one)))},
                    {UninterpretedPredicate{currentS3}}}
        },
        {
            ChcHead{UninterpretedPredicate{nextS1}},
            ChcBody{{logic->mkAnd( logic->mkLeq(x, zero), logic->mkEq(yp, logic->mkPlus(y, one)))},
                    {UninterpretedPredicate{currentS3}}}
        },
        {
            ChcHead{UninterpretedPredicate{logic->getTerm_false()}},
            ChcBody{{logic->mkAnd(logic->mkGeq(y, ten), logic->mkLeq(x, zero))}, {UninterpretedPredicate{currentS1}}}
        }};

    for (auto const & clause : clauses) { system.addClause(clause); }

    Logic & logic = *this->logic;
    auto normalizedSystem = Normalizer(logic).normalize(system);
    auto hyperGraph = ChcGraphBuilder(logic).buildGraph(normalizedSystem);
    NestedLoopTransformation NLTransformation;
    auto properGraph = *hyperGraph->toNormalGraph();
    ASSERT_EQ(properGraph.getEdges().size(), 7);
    auto [transformedGraph, preTranslator] = NLTransformation.transform(properGraph);
    ASSERT_EQ(transformedGraph->getEdges().size(), 3);
    auto res = TPAEngine(logic, options, TPACore::SPLIT).solve(*hyperGraph);
    auto answer = res.getAnswer();
    ASSERT_EQ(answer, VerificationAnswer::UNSAFE);
    Validator validator(logic);
    EXPECT_EQ(validator.validate(*hyperGraph, res), Validator::Result::VALIDATED);
}

TEST_F(Transformer_New_Test, test_EdgeInliner_OutgoingLoop) {
    SymRef s1 = mkPredicateSymbol("s1", {intSort(), intSort()});
    PTRef dz = instantiatePredicate(s1, {zero,zero});
    PTRef current = instantiatePredicate(s1, {x,y});
    PTRef next = instantiatePredicate(s1, {xp,yp});
    // x = 1 => S1(x,y)
    // S1(x,y) and x = 1 and y != 0 => S1(0,0)
    // S1(0,0) => false
    std::vector<ChClause> clauses{
        {
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{{logic->mkEq(xp, one)}, {}}
        },
        {
            ChcHead{UninterpretedPredicate{dz}},
            ChcBody{{logic->mkAnd(logic->mkEq(x, one), logic->mkNot(logic->mkEq(y, zero)))}, {UninterpretedPredicate{current}}}
        },
        {
            ChcHead{UninterpretedPredicate{logic->getTerm_false()}},
            ChcBody{{logic->getTerm_true()}, {UninterpretedPredicate{dz}}}
        }};

    for (auto const & clause : clauses) { system.addClause(clause); }

    Logic & logic = *this->logic;
    auto normalizedSystem = Normalizer(logic).normalize(system);
    auto hyperGraph = ChcGraphBuilder(logic).buildGraph(normalizedSystem);
    auto originalGraph = *hyperGraph;
    TransformationPipeline::pipeline_t stages;
    stages.push_back(std::make_unique<EdgeInliner>());
    stages.push_back(std::make_unique<FalseClauseRemoval>());
    stages.push_back(std::make_unique<RemoveUnreachableNodes>());
    auto [transformedGraph, translator] = TransformationPipeline(std::move(stages)).transform(std::move(hyperGraph));
    ASSERT_EQ(transformedGraph->getEdges().size(), 1);
}