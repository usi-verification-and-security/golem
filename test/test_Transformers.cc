/*
 * Copyright (c) 2022-2023, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include <gtest/gtest.h>
#include "graph/ChcGraphBuilder.h"
#include "transformers/SimpleChainSummarizer.h"
#include "transformers/NodeEliminator.h"
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
    auto hyperGraph = systemToGraph(system);
    auto originalGraph = *hyperGraph;
    auto [summarizedGraph, translator] = SimpleChainSummarizer().transform(std::move(hyperGraph));
    ValidityWitness witness{};
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
    auto [newGraph, translator] = SimpleChainSummarizer().transform(std::move(hypergraph));
    VersionManager manager{logic};
    PTRef predicate = manager.sourceFormulaToBase(newGraph->getStateVersion(s2));
    PTRef var = logic.getPterm(predicate)[0];
    ValidityWitness witness{{{predicate, logic.mkGeq(var,zero)}}};
    auto translatedWitness = translator->translate(witness);
    Validator validator(logic);
    VerificationResult result(VerificationAnswer::SAFE, translatedWitness);
    ASSERT_EQ(validator.validate(originalGraph, result), Validator::Result::VALIDATED);
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
    auto [newGraph, translator] = SimpleChainSummarizer().transform(std::move(hypergraph));
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

TEST_F(Transformer_test, test_NonLoopEliminator_SuccessfulElimination) {
    ChcSystem system;
    system.addUninterpretedPredicate(s1);
    system.addClause( // x' >= 0 => S1(x')
        ChcHead{UninterpretedPredicate{nextS1}},
        ChcBody{{logic.mkGeq(xp, zero)}, {}});
    system.addClause( // S1(x) => false
        ChcHead{UninterpretedPredicate{logic.getTerm_false()}},
        ChcBody{{logic.getTerm_true()}, {UninterpretedPredicate{currentS1}}}
    );
    auto hyperGraph = systemToGraph(system);
    auto entry = hyperGraph->getEntry();
    auto exit = hyperGraph->getExit();
    ASSERT_EQ(hyperGraph->getEdges().size(), 2);
    NonLoopEliminator transformation;
    auto [transformedGraph, backtranslator] = transformation.transform(std::move(hyperGraph));
    auto edges = transformedGraph->getEdges();
    ASSERT_EQ(edges.size(), 1);
    auto const & edge = edges[0];
    ASSERT_EQ(edge.from.size(), 1);
    EXPECT_EQ(edge.to, exit);
    EXPECT_EQ(edge.from[0], entry);
}

TEST_F(Transformer_test, test_NonLoopEliminator_NoElimination) {
    ChcSystem system;
    system.addUninterpretedPredicate(s1);
    system.addClause( // x' >= 0 => S1(x')
        ChcHead{UninterpretedPredicate{nextS1}},
        ChcBody{{logic.mkGeq(xp, zero)}, {}});
    system.addClause( // S1(x) and x' = x + 1 => S1(x')
        ChcHead{UninterpretedPredicate{nextS1}},
        ChcBody{{logic.mkEq(xp, logic.mkPlus(x, one))}, {UninterpretedPredicate{currentS1}}});
    system.addClause( // S1(x) => false
        ChcHead{UninterpretedPredicate{logic.getTerm_false()}},
        ChcBody{{logic.getTerm_true()}, {UninterpretedPredicate{currentS1}}}
    );
    auto hyperGraph = systemToGraph(system);
    ASSERT_EQ(hyperGraph->getEdges().size(), 3);
    NonLoopEliminator transformation;
    auto [transformedGraph, backtranslator] = transformation.transform(std::move(hyperGraph));
    auto edges = transformedGraph->getEdges();
    ASSERT_EQ(edges.size(), 3);
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
    ValidityWitness witness = backtranslator->translate(ValidityWitness());
    Validator validator(logic);
    auto res = validator.validate(originalGraph, VerificationResult(VerificationAnswer::SAFE, witness));
    ASSERT_EQ(res, Validator::Result::VALIDATED);
}