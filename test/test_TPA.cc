/*
 * Copyright (c) 2021-2022, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "TestTemplate.h"

#include "engine/TPA.h"

class TPATest : public LIAEngineTest {
};

TEST_F(TPATest, test_TPA_simple_safe)
{
    options.addOption(Options::COMPUTE_WITNESS, "true");
    options.addOption(Options::ENGINE, TPAEngine::SPLIT_TPA);
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
        }};
    TPAEngine engine(*logic, options, TPACore::SPLIT);
    solveSystem(clauses, engine, VerificationAnswer::SAFE, true);
}

TEST_F(TPATest, test_TPA_simple_unsafe)
{
    options.addOption(Options::LOGIC, "QF_LIA");
    options.addOption(Options::COMPUTE_WITNESS, "true");
    options.addOption(Options::ENGINE, TPAEngine::SPLIT_TPA);
    SymRef s1 = mkPredicateSymbol("s1",{intSort()});
    PTRef current = instantiatePredicate(s1, {x});
    PTRef next = instantiatePredicate(s1, {xp});
    std::vector<ChClause> clauses{{
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{{logic->mkEq(xp, zero)}, {}}},
        {
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{{logic->mkEq(xp, logic->mkPlus(x, one))}, {UninterpretedPredicate{current}}}
        },
        {
            ChcHead{UninterpretedPredicate{logic->getTerm_false()}},
            ChcBody{{logic->mkGt(x, one)}, {UninterpretedPredicate{current}}}
        }};
    TPAEngine engine(*logic, options, TPACore::SPLIT);
    solveSystem(clauses, engine, VerificationAnswer::UNSAFE, true);
}

TEST_F(TPATest, test_TPA_CEX_zero) {
    Options options;
    options.addOption(Options::LOGIC, "QF_LIA");
    options.addOption(Options::COMPUTE_WITNESS, "true");
    options.addOption(Options::ENGINE, TPAEngine::TPA);
    SymRef s1 = mkPredicateSymbol("s1", {intSort()});
    PTRef current = instantiatePredicate(s1, {x});
    PTRef next = instantiatePredicate(s1, {xp});
    std::vector<ChClause> clauses{{ // x' = 0 => S1(x')
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{{logic->mkEq(xp, zero)}, {}}
        },
        { // S1(x) and x' = x + 1 => S1(x')
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{{logic->mkEq(xp, logic->mkPlus(x, one))}, {UninterpretedPredicate{current}}}
        },
        { // S1(x) and x = 0 => false
            ChcHead{UninterpretedPredicate{logic->getTerm_false()}},
            ChcBody{{logic->mkEq(x, zero)}, {UninterpretedPredicate{current}}}
        }};
    TPAEngine engine(*logic, options, TPACore::BASIC);
    solveSystem(clauses, engine, VerificationAnswer::UNSAFE, true);
}

TEST_F(TPATest, test_TPA_CEX_one) {
    Options options;
    options.addOption(Options::LOGIC, "QF_LIA");
    options.addOption(Options::COMPUTE_WITNESS, "true");
    options.addOption(Options::ENGINE, TPAEngine::TPA);
    SymRef s1 = mkPredicateSymbol("s1", {intSort()});
    PTRef current = instantiatePredicate(s1, {x});
    PTRef next = instantiatePredicate(s1, {xp});
    std::vector<ChClause> clauses{{ // x' = 0 => S1(x')
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{{logic->mkEq(xp, zero)}, {}}
        },
        { // S1(x) and x' = x + 1 => S1(x')
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{{logic->mkEq(xp, logic->mkPlus(x, one))}, {UninterpretedPredicate{current}}}
        },
        { // S1(x) and x = 1 => false
            ChcHead{UninterpretedPredicate{logic->getTerm_false()}},
            ChcBody{{logic->mkEq(x, one)}, {UninterpretedPredicate{current}}}
        }};
    TPAEngine engine(*logic, options, TPACore::BASIC);
    solveSystem(clauses, engine, VerificationAnswer::UNSAFE, true);
}

TEST_F(TPATest, test_TPA_CEX_six) {
    Options options;
    options.addOption(Options::LOGIC, "QF_LIA");
    options.addOption(Options::COMPUTE_WITNESS, "true");
    options.addOption(Options::ENGINE, TPAEngine::TPA);
    SymRef s1 = mkPredicateSymbol("s1", {intSort()});
    PTRef current = instantiatePredicate(s1, {x});
    PTRef next = instantiatePredicate(s1, {xp});
    std::vector<ChClause> clauses{{ // x' = 0 => S1(x')
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{{logic->mkEq(xp, zero)}, {}}
        },
        { // S1(x) and x' = x + 1 => S1(x')
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{{logic->mkEq(xp, logic->mkPlus(x, one))}, {UninterpretedPredicate{current}}}
        },
        { // S1(x) and x = 6 => false
            ChcHead{UninterpretedPredicate{logic->getTerm_false()}},
            ChcBody{{logic->mkEq(x, logic->mkIntConst(6))}, {UninterpretedPredicate{current}}}
        }};
    TPAEngine engine(*logic, options, TPACore::BASIC);
    solveSystem(clauses, engine, VerificationAnswer::UNSAFE, true);
}

TEST_F(TPATest, test_TPA_chain_of_two_unsafe) {
    Options options;
    options.addOption(Options::LOGIC, "QF_LIA");
    options.addOption(Options::COMPUTE_WITNESS, "true");
    options.addOption(Options::ENGINE, TPAEngine::SPLIT_TPA);
    SymRef s1 = mkPredicateSymbol("s1", {intSort()});
    SymRef s2 = mkPredicateSymbol("s2", {intSort()});
    PTRef predS1Current = instantiatePredicate(s1, {x});
    PTRef predS1Next = instantiatePredicate(s1, {xp});
    PTRef predS2Current = instantiatePredicate(s2, {x});
    PTRef predS2Next = instantiatePredicate(s2, {xp});
    std::vector<ChClause> clauses{{
            ChcHead{UninterpretedPredicate{predS1Next}},
            ChcBody{{logic->mkEq(xp, zero)}, {}}
        },
        {
            ChcHead{UninterpretedPredicate{predS1Next}},
            ChcBody{{logic->mkEq(xp, logic->mkPlus(x, one))}, {UninterpretedPredicate{predS1Current}}}
        },
        {
            ChcHead{UninterpretedPredicate{predS2Current}},
            ChcBody{{logic->getTerm_true()}, {UninterpretedPredicate{predS1Current}}}
        },
        {
            ChcHead{UninterpretedPredicate{predS2Next}},
            ChcBody{{logic->mkEq(xp, logic->mkMinus(x, one))},
                {UninterpretedPredicate{predS2Current}}}
        },
        {
            ChcHead{UninterpretedPredicate{logic->getTerm_false()}},
            ChcBody{{logic->mkLt(x, zero)}, {UninterpretedPredicate{predS2Current}}}
        }};
    TPAEngine engine(*logic, options, TPACore::SPLIT);
    solveSystem(clauses, engine, VerificationAnswer::UNSAFE, true);
}

TEST_F(TPATest, test_TPA_graph_of_two_unsafe) {
    Options options;
    options.addOption(Options::LOGIC, "QF_LIA");
    options.addOption(Options::COMPUTE_WITNESS, "true");
    options.addOption(Options::ENGINE, TPAEngine::SPLIT_TPA);
    SymRef s1 = mkPredicateSymbol("s1", {intSort()});
    SymRef s2 = mkPredicateSymbol("s2", {intSort()});
    PTRef predS1Current = instantiatePredicate(s1, {x});
    PTRef predS1Next = instantiatePredicate(s1, {xp});
    PTRef predS2Current = instantiatePredicate(s2, {x});
    PTRef predS2Next = instantiatePredicate(s2, {xp});
    std::vector<ChClause> clauses{{ // x = 0 => S1(x)
                                          ChcHead{UninterpretedPredicate{predS1Current}},
                                          ChcBody{{logic->mkEq(x, zero)}, {}}
                                  },
                                  { // x = 0 => S2(x)
                                          ChcHead{UninterpretedPredicate{predS2Current}},
                                          ChcBody{{logic->mkEq(x, zero)}, {}}
                                  },
                                  { // S2(x) & x' = x + 1 => S2(x')
                                          ChcHead{UninterpretedPredicate{predS2Next}},
                                          ChcBody{{logic->mkEq(xp, logic->mkPlus(x, one))},
                                                  {UninterpretedPredicate{predS2Current}}}
                                  },
                                  { // S1(x) & x' = x + 1 => S1(x')
                                          ChcHead{UninterpretedPredicate{predS1Next}},
                                          ChcBody{{logic->mkEq(xp, logic->mkPlus(x, one))},
                                                  {UninterpretedPredicate{predS1Current}}}
                                  },
                                  { // S1(x) & x < 0 => false
                                          ChcHead{UninterpretedPredicate{logic->getTerm_false()}},
                                          ChcBody{{logic->mkLt(x, zero)}, {UninterpretedPredicate{predS1Current}}}
                                  },
                                  { // S2(x) & x <= 0 => false
                                          ChcHead{UninterpretedPredicate{logic->getTerm_false()}},
                                          ChcBody{{logic->mkLeq(x, zero)}, {UninterpretedPredicate{predS2Current}}}
                                  }};
    TPAEngine engine(*logic, options, TPACore::SPLIT);
    solveSystem(clauses, engine, VerificationAnswer::UNSAFE, true);
}


TEST_F(TPATest, test_TPA_graph_of_three_unsafe) {
    Options options;
    options.addOption(Options::LOGIC, "QF_LIA");
    options.addOption(Options::COMPUTE_WITNESS, "true");
    options.addOption(Options::ENGINE, TPAEngine::SPLIT_TPA);
    SymRef s1 = mkPredicateSymbol("s1", {intSort()});
    SymRef s2 = mkPredicateSymbol("s2", {intSort()});
    SymRef s3 = mkPredicateSymbol("s3", {intSort()});
    PTRef predS1Current = instantiatePredicate(s1, {x});
    PTRef predS1Next = instantiatePredicate(s1, {xp});
    PTRef predS2Current = instantiatePredicate(s2, {x});
    PTRef predS2Next = instantiatePredicate(s2, {xp});
    PTRef predS3Current = instantiatePredicate(s3, {x});
    PTRef predS3Next = instantiatePredicate(s3, {xp});
    std::vector<ChClause> clauses{{ // x = 0 => S1(x)
                                          ChcHead{UninterpretedPredicate{predS1Current}},
                                          ChcBody{{logic->mkEq(x, zero)}, {}}
                                  },
                                  { // S1(x) & x' = x + 1 => S1(x')
                                          ChcHead{UninterpretedPredicate{predS1Next}},
                                          ChcBody{{logic->mkEq(xp, logic->mkPlus(x, one))},
                                                  {UninterpretedPredicate{predS1Current}}}
                                  },
                                  { // S1(x) => S2(x)
                                          ChcHead{UninterpretedPredicate{predS2Current}},
                                          ChcBody{{}, {UninterpretedPredicate{predS1Current}}}
                                  },
                                  { // S1(x) => S3(x)

                                          ChcHead{UninterpretedPredicate{predS3Current}},
                                          ChcBody{{},{UninterpretedPredicate{predS1Current}}}
                                  },
                                  { // S2(x) & x' = x + 1 => S2(x')
                                          ChcHead{UninterpretedPredicate{predS2Next}},
                                          ChcBody{{logic->mkEq(xp, logic->mkPlus(x, one))},
                                                  {UninterpretedPredicate{predS2Current}}}
                                  },
                                  { // S3(x) & x' = x + 1 => S3(x')
                                          ChcHead{UninterpretedPredicate{predS3Next}},
                                          ChcBody{{logic->mkEq(xp, logic->mkPlus(x, one))},
                                                  {UninterpretedPredicate{predS3Current}}}
                                  },
                                  { // S1(x) & x < 0 => false
                                          ChcHead{UninterpretedPredicate{logic->getTerm_false()}},
                                          ChcBody{{logic->mkLt(x, zero)}, {UninterpretedPredicate{predS3Current}}}
                                  },
                                  { // S2(x) & x > 0 => false
                                          ChcHead{UninterpretedPredicate{logic->getTerm_false()}},
                                          ChcBody{{logic->mkGt(x, zero)}, {UninterpretedPredicate{predS2Current}}}
                                  }};
    TPAEngine engine(*logic, options, TPACore::SPLIT);
    solveSystem(clauses, engine, VerificationAnswer::UNSAFE, true);
}

TEST_F(TPATest, test_TPA_chain_of_two_safe) {
    Options options;
    options.addOption(Options::LOGIC, "QF_LIA");
    options.addOption(Options::COMPUTE_WITNESS, "true");
    options.addOption(Options::ENGINE, TPAEngine::SPLIT_TPA);
    SymRef s1 = mkPredicateSymbol("s1", {intSort()});
    SymRef s2 = mkPredicateSymbol("s2", {intSort()});
    PTRef predS1Current = instantiatePredicate(s1, {x});
    PTRef predS1Next = instantiatePredicate(s1, {xp});
    PTRef predS2Current = instantiatePredicate(s2, {x});
    PTRef predS2Next = instantiatePredicate(s2, {xp});
    std::vector<ChClause> clauses{{ // x = 0 => S1(x)
            ChcHead{UninterpretedPredicate{predS1Next}},
            ChcBody{{logic->mkEq(xp, zero)}, {}}
        },
        { // S1(x) & x' = x + 1 => S1(x')
            ChcHead{UninterpretedPredicate{predS1Next}},
            ChcBody{{logic->mkEq(xp, logic->mkPlus(x, one))}, {UninterpretedPredicate{predS1Current}}}
        },
        { // S1(x) => S2(x)
            ChcHead{UninterpretedPredicate{predS2Current}},
            ChcBody{{logic->getTerm_true()}, {UninterpretedPredicate{predS1Current}}}
        },
        { // S2(x) & x' = x + 2 => S2(x')
            ChcHead{UninterpretedPredicate{predS2Next}},
            ChcBody{{logic->mkEq(xp, logic->mkPlus(x, logic->mkIntConst(FastRational(2))))},
                {UninterpretedPredicate{predS2Current}}}
        },
        { // S2(x) & x < 0 => false
            ChcHead{UninterpretedPredicate{logic->getTerm_false()}},
            ChcBody{{logic->mkLt(x, zero)}, {UninterpretedPredicate{predS2Current}}}
        }};
    TPAEngine engine(*logic, options, TPACore::SPLIT);
    solveSystem(clauses, engine, VerificationAnswer::SAFE, true);
}

TEST_F(TPATest, test_TPA_chain_regression) {
    Options options;
    options.addOption(Options::LOGIC, "QF_LIA");
    options.addOption(Options::COMPUTE_WITNESS, "true");
    options.addOption(Options::ENGINE, TPAEngine::SPLIT_TPA);
    SymRef s1 = mkPredicateSymbol("inv1", {intSort(), intSort()});
    SymRef s2 = mkPredicateSymbol("inv2", {intSort(), intSort()});
    PTRef y = mkIntVar("y");
    PTRef yp = mkIntVar("yp");
    PTRef predS1Current = instantiatePredicate(s1, {x, y});
    PTRef predS1Next = instantiatePredicate(s1, {xp, yp});
    PTRef predS2Current = instantiatePredicate(s2, {x, y});
    PTRef predS2Next = instantiatePredicate(s2, {xp, yp});
    PTRef val = logic->mkIntConst(FastRational(5));
    PTRef doubleVal = logic->mkIntConst(FastRational(10));
    std::vector<ChClause> clauses{{ // x = 0 and y = 5 => S1(x,y)
            ChcHead{UninterpretedPredicate{predS1Next}},
            ChcBody{{logic->mkAnd(logic->mkEq(xp, zero), logic->mkEq(yp, val))}, {}}
        },
        { // S1(x,y) and x < 5 and x' = x + 1 and y' = y => S1(x',y')
            ChcHead{UninterpretedPredicate{predS1Next}},
            ChcBody{{logic->mkAnd({logic->mkEq(xp, logic->mkPlus(x, one)),logic->mkEq(yp, y),logic->mkLt(x, val)})},
                {UninterpretedPredicate{predS1Current}}
            }
        },
        { // S1(x,y) and x >= 5 => S2(x,y)
            ChcHead{UninterpretedPredicate{predS2Current}},
            ChcBody{{logic->mkGeq(x, val)}, {UninterpretedPredicate{predS1Current}}}
        },
        { // S2(x,y) and x' = x + 1 and y' = y + 1 => S2(x',y')
            ChcHead{UninterpretedPredicate{predS2Next}},
            ChcBody{{logic->mkAnd(
                logic->mkEq(xp, logic->mkPlus(x, one)),
                logic->mkEq(yp, logic->mkPlus(y, one))
            )
            },
                {UninterpretedPredicate{predS2Current}}}
        },
        { // S2(x,y) and x = 10 and x != y => false
            ChcHead{UninterpretedPredicate{logic->getTerm_false()}},
            ChcBody{{logic->mkAnd(logic->mkEq(x, doubleVal), logic->mkNot(logic->mkEq(x, y)))},
                {UninterpretedPredicate{predS2Current}}}
        }};
    TPAEngine engine(*logic, options, TPACore::SPLIT);
    solveSystem(clauses, engine, VerificationAnswer::SAFE, true);
}

TEST_F(TPATest, test_TPA_chain_regression_2) {
    Options options;
    options.addOption(Options::LOGIC, "QF_LIA");
    options.addOption(Options::COMPUTE_WITNESS, "true");
    options.addOption(Options::ENGINE, TPAEngine::SPLIT_TPA);
    SymRef s1 = mkPredicateSymbol("inv1", {intSort()});
    SymRef s2 = mkPredicateSymbol("inv2", {intSort()});
    PTRef predS1Current = instantiatePredicate(s1, {x});
    PTRef predS1Next = instantiatePredicate(s1, {xp});
    PTRef predS2Current = instantiatePredicate(s2, {x});
    PTRef predS2Next = instantiatePredicate(s2, {xp});
    PTRef five = logic->mkIntConst(FastRational(5));
    PTRef three = logic->mkIntConst(FastRational(3));
    std::vector<ChClause> clauses{{ // x = 5 => S1(x)
        ChcHead{UninterpretedPredicate{predS1Next}},
        ChcBody{{logic->mkEq(xp, five)}, {}}
    },
        { // S1(x) and (x' = x + 1 or x' = x - 1) => S1(x')
            ChcHead{UninterpretedPredicate{predS1Next}},
            ChcBody{{logic->mkOr({logic->mkEq(xp, logic->mkPlus(x, one)), logic->mkEq(xp, logic->mkMinus(x, one))})},
                {UninterpretedPredicate{predS1Current}}
            }
        },
        { // S1(x) => S2(x)
            ChcHead{UninterpretedPredicate{predS2Current}},
            ChcBody{{logic->getTerm_true()}, {UninterpretedPredicate{predS1Current}}}
        },
        { // S2(x) and x > 5 and x' = x + 1 => S2(x')
            ChcHead{UninterpretedPredicate{predS2Next}},
            ChcBody{{logic->mkAnd(
                logic->mkGt(x, five),
                logic->mkEq(xp, logic->mkPlus(x, one))
            )
            },
                {UninterpretedPredicate{predS2Current}}}
        },
        { // S2(x) and x = 3 => false
            ChcHead{UninterpretedPredicate{logic->getTerm_false()}},
            ChcBody{{logic->mkEq(x, three)},
                {UninterpretedPredicate{predS2Current}}}
        }};
    TPAEngine engine(*logic, options, TPACore::SPLIT);
    solveSystem(clauses, engine, VerificationAnswer::UNSAFE);
}

TEST_F(TPATest, test_TPA_chain_unsatisfiable_transition) {
    Options options;
    options.addOption(Options::LOGIC, "QF_LIA");
    options.addOption(Options::COMPUTE_WITNESS, "true");
    options.addOption(Options::ENGINE, TPAEngine::SPLIT_TPA);
    SymRef s1 = mkPredicateSymbol("inv1", {intSort()});
    SymRef s2 = mkPredicateSymbol("inv2", {intSort(), intSort()});
    PTRef y = mkIntVar("y");
    PTRef yp = mkIntVar("yp");
    PTRef predS1Current = instantiatePredicate(s1, {x});
    PTRef predS1Next = instantiatePredicate(s1, {xp});
    PTRef predS2Current = instantiatePredicate(s2, {x, y});
    PTRef predS2Next = instantiatePredicate(s2, {xp, yp});
    PTRef two = logic->mkIntConst(FastRational(2));
    std::vector<ChClause> clauses{{ // x' <= 1 => S1(x')
        ChcHead{UninterpretedPredicate{predS1Next}},
        ChcBody{{logic->mkLeq(xp, one)}, {}}
    },
        { // S1(x) and (x' = x + 2 and x' > 1) => S1(x')
            ChcHead{UninterpretedPredicate{predS1Next}},
            ChcBody{{logic->mkAnd(logic->mkEq(xp, logic->mkPlus(x, two)), logic->mkGt(xp, one))},
                {UninterpretedPredicate{predS1Current}}
            }
        },
        { // S1(x) and x' <= 1 and y' > 1 and y' = x => S2(x',y')
            ChcHead{UninterpretedPredicate{predS2Next}},
            ChcBody{{logic->mkAnd({logic->mkLeq(xp, one), logic->mkGt(yp, one), logic->mkEq(x, yp)})}, {UninterpretedPredicate{predS1Current}}}
        },
        { // S2(x,y) and x > 1 and y > 1 => S2(x,y)
            ChcHead{UninterpretedPredicate{predS2Current}},
            ChcBody{{logic->mkAnd(
                logic->mkGt(x, one),
                logic->mkGt(y, one)
            )
            },
                {UninterpretedPredicate{predS2Current}}}
        },
        { // S2(x,y) and x = y and x > 0 => false
            ChcHead{UninterpretedPredicate{logic->getTerm_false()}},
            ChcBody{{logic->mkAnd(logic->mkEq(x, y), logic->mkGt(x, zero))},
                {UninterpretedPredicate{predS2Current}}}
        }};
    TPAEngine engine(*logic, options, TPACore::SPLIT);
    solveSystem(clauses, engine, VerificationAnswer::SAFE, true);
}

TEST_F(TPATest, test_transformContractVertex_safe) {
    Options options;
    options.addOption(Options::LOGIC, "QF_LIA");
    options.addOption(Options::COMPUTE_WITNESS, "true");
    options.addOption(Options::ENGINE, TPAEngine::SPLIT_TPA);
    SymRef s1 = mkPredicateSymbol("s1", {intSort()});
    SymRef s2 = mkPredicateSymbol("s2", {intSort()});
    PTRef predS1Current = instantiatePredicate(s1, {x});
    PTRef predS1Next = instantiatePredicate(s1, {xp});
    PTRef predS2Current = instantiatePredicate(s2, {x});
    PTRef predS2Next = instantiatePredicate(s2, {xp});
    std::vector<ChClause> clauses{
        { // x < 0 => S1(x)
        ChcHead{UninterpretedPredicate{predS1Next}},
        ChcBody{{logic->mkLt(xp, zero)}, {}}
        },
        { // x > 0 => S1(x)
            ChcHead{UninterpretedPredicate{predS1Next}},
            ChcBody{{logic->mkGt(xp, zero)}, {}}
        },
        { // S1(x) => S2(x)
            ChcHead{UninterpretedPredicate{predS2Current}},
            ChcBody{{logic->getTerm_true()}, {UninterpretedPredicate{predS1Current}}}
        },
        { // S2(x) and (x < 0 => x' = x - 1) and (x > 0 => x' = x + 1 => S2(x')
            ChcHead{UninterpretedPredicate{predS2Next}},
            ChcBody{{logic->mkAnd(
                logic->mkImpl(logic->mkLt(x, zero), logic->mkEq(xp, logic->mkMinus(x, one))),
                logic->mkImpl(logic->mkGt(x, zero), logic->mkEq(xp, logic->mkPlus(x, one)))
                )},
                {UninterpretedPredicate{predS2Current}}}
        },
        { // S2(x) & x = 0 => false
            ChcHead{UninterpretedPredicate{logic->getTerm_false()}},
            ChcBody{{logic->mkEq(x, zero)}, {UninterpretedPredicate{predS2Current}}}
        }};
    TPAEngine engine(*logic, options, TPACore::SPLIT);
    solveSystem(clauses, engine, VerificationAnswer::SAFE, true);
}


TEST_F(TPATest, test_transformContractVertex_unsafe) {
    Options options;
    options.addOption(Options::LOGIC, "QF_LIA");
    options.addOption(Options::COMPUTE_WITNESS, "true");
    options.addOption(Options::ENGINE, TPAEngine::SPLIT_TPA);
    SymRef s1 = mkPredicateSymbol("s1", {intSort()});
    SymRef s2 = mkPredicateSymbol("s2", {intSort()});
    PTRef predS1Current = instantiatePredicate(s1, {x});
    PTRef predS1Next = instantiatePredicate(s1, {xp});
    PTRef predS2Current = instantiatePredicate(s2, {x});
    PTRef predS2Next = instantiatePredicate(s2, {xp});
    std::vector<ChClause> clauses{
        { // x > 0 => S1(x)
            ChcHead{UninterpretedPredicate{predS1Next}},
            ChcBody{{logic->mkGt(xp, zero)}, {}}
        },
        { // S1(x) => S2(x)
            ChcHead{UninterpretedPredicate{predS2Current}},
            ChcBody{{logic->getTerm_true()}, {UninterpretedPredicate{predS1Current}}}
        },
        { // S2(x) and x' = x - 1 => S2(x')
            ChcHead{UninterpretedPredicate{predS2Next}},
            ChcBody{{logic->mkEq(xp, logic->mkMinus(x, one))},{UninterpretedPredicate{predS2Current}}}
        },
        { // S2(x) & x = 0 => false
            ChcHead{UninterpretedPredicate{logic->getTerm_false()}},
            ChcBody{{logic->mkEq(x, zero)}, {UninterpretedPredicate{predS2Current}}}
        }};
    TPAEngine engine(*logic, options, TPACore::SPLIT);
    solveSystem(clauses, engine, VerificationAnswer::UNSAFE, true);
}

TEST_F(TPATest, test_trivialSystem_unsafe) {
    Options options;
    options.addOption(Options::LOGIC, "QF_LIA");
    options.addOption(Options::COMPUTE_WITNESS, "true");
    options.addOption(Options::ENGINE, TPAEngine::SPLIT_TPA);
    std::vector<ChClause> clauses{
        { // x > 0  => false
            ChcHead{UninterpretedPredicate{logic->getTerm_false()}},
            ChcBody{{logic->mkGt(xp, zero)}, {}}
        }};
    TPAEngine engine(*logic, options, TPACore::SPLIT);
    solveSystem(clauses, engine, VerificationAnswer::UNSAFE, true);
}

TEST_F(TPATest, test_trivialSystem_safe) {
    Options options;
    options.addOption(Options::LOGIC, "QF_LIA");
    options.addOption(Options::COMPUTE_WITNESS, "true");
    options.addOption(Options::ENGINE, TPAEngine::SPLIT_TPA);
    std::vector<ChClause> clauses{
        { // x > 0  and x < -1 => false
            ChcHead{UninterpretedPredicate{logic->getTerm_false()}},
            ChcBody{{logic->mkAnd(logic->mkGt(xp, zero), logic->mkLt(xp, logic->mkNeg(one)))}, {}}
        }};
    TPAEngine engine(*logic, options, TPACore::SPLIT);
    solveSystem(clauses, engine, VerificationAnswer::SAFE, true);
}



TEST_F(TPATest, test_nextQueryVersion) {
    Options options;
    options.addOption(Options::LOGIC, "QF_LIA");
    options.addOption(Options::COMPUTE_WITNESS, "true");
    options.addOption(Options::ENGINE, TPAEngine::SPLIT_TPA);
    SymRef itp = mkPredicateSymbol("itp", {intSort(), intSort(), intSort()});


    PTRef ten = logic->mkIntConst(FastRational(10));
    PTRef seven = logic->mkIntConst(FastRational(7));
    PTRef five = logic->mkIntConst(FastRational(5));
    PTRef three = logic->mkIntConst(FastRational(3));

    PTRef y = logic->mkIntVar("y");
    PTRef z = logic->mkIntVar("z");
    PTRef k = logic->mkIntVar("k");
    PTRef l = logic->mkIntVar("l");
    PTRef predItpCurrent1 = instantiatePredicate(itp, {x, y, z});
    PTRef predItpCurrent2 = instantiatePredicate(itp, {x, y, l});
    PTRef predItpCurrent3 = instantiatePredicate(itp, {z, k, l});
    PTRef predItpCurrent4 = instantiatePredicate(itp, {x, z, y});
    std::vector<ChClause> clauses{
        { // (x = 0) and (not (5 <= z)) and (not (z <= 0)) and (y = (z * 3))) => itp(x, y, z)
         ChcHead{UninterpretedPredicate{predItpCurrent1}},
         ChcBody{{logic->mkAnd({ logic->mkEq(x, zero), logic->mkNot(logic->mkLeq(five, z)),
                                 logic->mkNot(logic->mkLeq(five, zero)), logic->mkEq(y, logic->mkTimes(z, three)) })}, {}}
        },
        { // itp(x,y,l) and (z = (1 + x)) and (not (x <= 10)) and (k = (y + 1))) => itp(z, k, l)
         ChcHead{UninterpretedPredicate{predItpCurrent3}},
         ChcBody{{logic->mkAnd({ logic->mkEq(z, logic->mkPlus(x, one)), logic->mkNot(logic->mkLeq(ten, x)),
                                 logic->mkEq(k, logic->mkPlus(y, one)) })}, {UninterpretedPredicate{predItpCurrent2}}}
        },
        { // itp(x, z, y) and (not (z <= 7)) and (not (z >= 3)) => false
         ChcHead{UninterpretedPredicate{logic->getTerm_false()}},
         ChcBody{{logic->mkAnd(logic->mkNot(logic->mkLeq(z, seven)), logic->mkNot(logic->mkGeq(z, three)))},
                 {UninterpretedPredicate{predItpCurrent4}}}
        }};
    TPAEngine engine(*logic, options, TPACore::SPLIT);
    solveSystem(clauses, engine, VerificationAnswer::SAFE, true);
}

TEST_F(TPATest, test_TPA_BeyondTransitionSystemDAG_Unsafe)
{
    Options options;
    options.addOption(Options::LOGIC, "QF_LIA");
    options.addOption(Options::COMPUTE_WITNESS, "true");
    options.addOption(Options::ENGINE, TPAEngine::SPLIT_TPA);
    SymRef s1 = mkPredicateSymbol("s1", {intSort(), intSort()});
    SymRef s2 = mkPredicateSymbol("s2", {intSort(), intSort()});
    PTRef current1 = instantiatePredicate(s1, {x,y});
    PTRef next1 = instantiatePredicate(s1, {xp,yp});
    PTRef current2 = instantiatePredicate(s2, {x,y});
    PTRef next2 = instantiatePredicate(s2, {xp,yp});
    // x = 0 and y = 0 => S1(x,y)
    // S1(x,y) and x' = x + 1 => S1(x',y)
    // S1(x,y) and x > 2 => S2(x,y)
    // S2(x,y) and y' = y + 1 => S2(x,y')
    // S2(x,y) and y > 2 => S1(x,y)
    // S1(x,y) and y > 0 and x = 5 => false
    std::vector<ChClause> clauses{
        {
            ChcHead{UninterpretedPredicate{next1}},
            ChcBody{{logic->mkAnd(logic->mkEq(xp, zero), logic->mkEq(yp, zero))}, {}}
        },
        {
            ChcHead{UninterpretedPredicate{next1}},
            ChcBody{{logic->mkAnd(logic->mkEq(xp, logic->mkPlus(x, one)), logic->mkEq(yp, y))}, {UninterpretedPredicate{current1}}}
        },
        {
            ChcHead{UninterpretedPredicate{current2}},
            ChcBody{{logic->mkGt(x, logic->mkIntConst(2))}, {UninterpretedPredicate{current1}}}
        },
        {
            ChcHead{UninterpretedPredicate{next2}},
            ChcBody{{logic->mkAnd(logic->mkEq(yp, logic->mkPlus(y, one)), logic->mkEq(xp, x))}, {UninterpretedPredicate{current2}}}
        },
        {
            ChcHead{UninterpretedPredicate{current1}},
            ChcBody{{logic->mkGt(y, logic->mkIntConst(2))}, {UninterpretedPredicate{current2}}}
        },
        {
            ChcHead{UninterpretedPredicate{logic->getTerm_false()}},
            ChcBody{{logic->mkAnd(logic->mkGt(y, zero), logic->mkEq(x, logic->mkIntConst(5)))}, {UninterpretedPredicate{current1}}}
        }};
    TPAEngine engine(*logic, options, TPACore::SPLIT);
    solveSystem(clauses, engine, VerificationAnswer::UNSAFE, true);
}

TEST_F(TPATest, test_TPA_BeyondTransitionSystemDAG_Safe)
{
    Options options;
    options.addOption(Options::LOGIC, "QF_LIA");
    options.addOption(Options::COMPUTE_WITNESS, "true");
    options.addOption(Options::ENGINE, TPAEngine::SPLIT_TPA);
    SymRef s1 = mkPredicateSymbol("s1", {intSort(), intSort()});
    SymRef s2 = mkPredicateSymbol("s2", {intSort(), intSort()});
    PTRef current1 = instantiatePredicate(s1, {x,y});
    PTRef next1 = instantiatePredicate(s1, {xp,yp});
    PTRef current2 = instantiatePredicate(s2, {x,y});
    PTRef next2 = instantiatePredicate(s2, {xp,yp});
    // x = 0 and y = 0 => S1(x,y)
    // S1(x,y) and x' = x + 1 => S1(x',y)
    // S1(x,y) and x >= 2 => S2(x,y)
    // S2(x,y) and y' = y + 1 => S2(x,y')
    // S2(x,y) and y >= 2 => S1(x,y)
    // S1(x,y) and y < 0 or x < 0 => false
    std::vector<ChClause> clauses{
        {
            ChcHead{UninterpretedPredicate{next1}},
            ChcBody{{logic->mkAnd(logic->mkEq(xp, zero), logic->mkEq(yp, zero))}, {}}
        },
        {
            ChcHead{UninterpretedPredicate{next1}},
            ChcBody{{logic->mkAnd(logic->mkEq(xp, logic->mkPlus(x, one)), logic->mkEq(yp, y))}, {UninterpretedPredicate{current1}}}
        },
        {
            ChcHead{UninterpretedPredicate{current2}},
            ChcBody{{logic->mkGeq(x, logic->mkIntConst(2))}, {UninterpretedPredicate{current1}}}
        },
        {
            ChcHead{UninterpretedPredicate{next2}},
            ChcBody{{logic->mkAnd(logic->mkEq(yp, logic->mkPlus(y, one)), logic->mkEq(xp, x))}, {UninterpretedPredicate{current2}}}
        },
        {
            ChcHead{UninterpretedPredicate{current1}},
            ChcBody{{logic->mkGeq(y, logic->mkIntConst(2))}, {UninterpretedPredicate{current2}}}
        },
        {
            ChcHead{UninterpretedPredicate{logic->getTerm_false()}},
            ChcBody{{logic->mkOr(logic->mkLt(y, zero), logic->mkLt(x, zero))}, {UninterpretedPredicate{current1}}}
        }};
    TPAEngine engine(*logic, options, TPACore::SPLIT);
    solveSystem(clauses, engine, VerificationAnswer::SAFE, true);
}

TEST_F(TPATest, test_TPA_BeyondTransitionSystemDAG_Branching_Unsafe)
{
    Options options;
    options.addOption(Options::LOGIC, "QF_LIA");
    options.addOption(Options::COMPUTE_WITNESS, "true");
    options.addOption(Options::ENGINE, TPAEngine::SPLIT_TPA);
    SymRef s1 = mkPredicateSymbol("s1", {intSort(), intSort()});
    SymRef s2 = mkPredicateSymbol("s2", {intSort(), intSort()});
    SymRef s3 = mkPredicateSymbol("s3", {intSort(), intSort()});
    SymRef s4 = mkPredicateSymbol("s4", {intSort(), intSort()});
    PTRef current1 = instantiatePredicate(s1, {x,y});
    PTRef next1 = instantiatePredicate(s1, {xp,yp});
    PTRef current2 = instantiatePredicate(s2, {x,y});
    PTRef next2 = instantiatePredicate(s2, {xp,yp});
    PTRef current3 = instantiatePredicate(s3, {x,y});
    PTRef current4 = instantiatePredicate(s4, {x,y});
    // x = 1 and y = 2 => S1(x,y)
    // S1(x,y) and x' = x + 1 and y' = y + 4 => S1(x',y')
    // S1(x,y) and  y > 10 => S4(x,y)
    // S4(x,y) and  x > 5 => S2(x,y)
    // S4(x,y) and  x <= 5 => S3(x,y)
    // S2(x,y) and x > y and x' = x - 1 => S2(x,y')
    // S2(x,y) and y >= x => S3(x,y)
    // S3(x,y) and x < y+20 => false
    std::vector<ChClause> clauses{
        {
            ChcHead{UninterpretedPredicate{next1}},
            ChcBody{{logic->mkAnd(logic->mkEq(xp, one), logic->mkEq(yp, logic->mkIntConst(2)))}, {}}
        },
        {
            ChcHead{UninterpretedPredicate{current4}},
            ChcBody{{logic->mkGeq(y,logic->mkIntConst(10))}, {UninterpretedPredicate{current1}}}
        },
        {
            ChcHead{UninterpretedPredicate{next1}},
            ChcBody{{logic->mkAnd({logic->mkLt(y,logic->mkIntConst(10)),logic->mkEq(xp, logic->mkPlus(x, one)), logic->mkEq(yp, logic->mkPlus(y,logic->mkIntConst(4)))})}, {UninterpretedPredicate{current1}}}
        },
        {
            ChcHead{UninterpretedPredicate{current2}},
            ChcBody{{logic->mkGt(x,logic->mkIntConst(5))}, {UninterpretedPredicate{current4}}}
        },
        {
            ChcHead{UninterpretedPredicate{current3}},
            ChcBody{{logic->mkLeq(x,logic->mkIntConst(5))}, {UninterpretedPredicate{current4}}}
        },
        {
            ChcHead{UninterpretedPredicate{current3}},
            ChcBody{{logic->mkLeq(x,y)}, {UninterpretedPredicate{current2}}}
        },
        {
            ChcHead{UninterpretedPredicate{next2}},
            ChcBody{{logic->mkAnd({logic->mkGt(x,y),logic->mkEq(xp, logic->mkMinus(x, one)), logic->mkEq(yp, y)})}, {UninterpretedPredicate{current2}}}
        },
        {
            ChcHead{UninterpretedPredicate{logic->getTerm_false()}},
            ChcBody{{logic->mkLt(x, logic->mkIntConst(5))}, {UninterpretedPredicate{current3}}}
        }};
    TPAEngine engine(*logic, options, TPACore::SPLIT);
    solveSystem(clauses, engine, VerificationAnswer::UNSAFE, true);
}

TEST_F(TPATest, test_TPA_BeyondTransitionSystemDAG_Branching_Unsafe2)
{
    Options options;
    options.addOption(Options::LOGIC, "QF_LIA");
    options.addOption(Options::COMPUTE_WITNESS, "true");
    options.addOption(Options::ENGINE, TPAEngine::SPLIT_TPA);
    SymRef h1 = mkPredicateSymbol("h1", {intSort()});
    SymRef h2 = mkPredicateSymbol("h2", {intSort()});
    SymRef s1 = mkPredicateSymbol("s1", {intSort(), intSort()});
    SymRef s2 = mkPredicateSymbol("s2", {intSort()});
    SymRef s3 = mkPredicateSymbol("s3", {intSort()});
    PTRef currentH1 = instantiatePredicate(h1, {y});
    PTRef nextH1 = instantiatePredicate(h1, {yp});
    PTRef currentH2 = instantiatePredicate(h2, {y});
    PTRef nextH2 = instantiatePredicate(h2, {yp});
    PTRef current1 = instantiatePredicate(s1, {x, y});
    PTRef next1 = instantiatePredicate(s1, {xp, y});
    PTRef current2 = instantiatePredicate(s2, {x});
    PTRef current3 = instantiatePredicate(s3, {x});
    PTRef next3 = instantiatePredicate(s3, {xp});
    // y > 0 => H2(y)
    // y < 0 => H1(y)
    // H1(y) and yp = y - 1 => H1(yp)
    // H2(y) and yp = y + 1 => H2(yp)
    // H1(y) and x = 0 => S1(x,y)
    // H2(y) and x = 0 => S1(x,y)
    // S1(x, y) and x' = x + 1 => S1(x', y)
    // S1(x,y) => S3(x)
    // S3(x) and x' = x + 1 => S3(x')
    // S1(x, y) and y > 0 => S2(x)
    // S2(x) => S2(x)
    // S2(x) and x > 0 => false
    // S3(x) and x < 0 => false
    std::vector<ChClause> clauses{
        {
            ChcHead{UninterpretedPredicate{currentH2}},
            ChcBody{{logic->mkGt(y, zero)}, {}}
        },
        {
            ChcHead{UninterpretedPredicate{currentH1}},
            ChcBody{{logic->mkLt(y, zero)}, {}}
        },
        {
            ChcHead{UninterpretedPredicate{nextH1}},
            ChcBody{{logic->mkEq(yp, logic->mkMinus(y, one))}, {UninterpretedPredicate{currentH1}}}
        },
        {
            ChcHead{UninterpretedPredicate{nextH2}},
            ChcBody{{logic->mkEq(yp, logic->mkPlus(y, one))}, {UninterpretedPredicate{currentH2}}}
        },
        {
            ChcHead{UninterpretedPredicate{current1}},
            ChcBody{{logic->mkEq(x, zero)}, {UninterpretedPredicate{currentH1}}}
        },
        {
            ChcHead{UninterpretedPredicate{current1}},
            ChcBody{{logic->mkEq(x, zero)}, {UninterpretedPredicate{currentH2}}}
        },
        {
            ChcHead{UninterpretedPredicate{next1}},
            ChcBody{{logic->mkEq(xp, logic->mkPlus(x, one))}, {UninterpretedPredicate{current1}}}
        },
        {
            ChcHead{UninterpretedPredicate{current3}},
            ChcBody{{logic->getTerm_true()}, {UninterpretedPredicate{current1}}}
        },
        {
            ChcHead{UninterpretedPredicate{next3}},
            ChcBody{{logic->mkEq(xp, logic->mkPlus(x, one))}, {UninterpretedPredicate{current3}}}
        },
        {
            ChcHead{UninterpretedPredicate{current2}},
            ChcBody{{logic->mkGt(y, zero)}, {UninterpretedPredicate{current1}}}
        },
        {
            ChcHead{UninterpretedPredicate{current2}},
            ChcBody{{logic->getTerm_true()}, {UninterpretedPredicate{current2}}}
        },
        {
            ChcHead{UninterpretedPredicate{logic->getTerm_false()}},
            ChcBody{{logic->mkGt(x, zero)}, {UninterpretedPredicate{current2}}}
        },
        {
            ChcHead{UninterpretedPredicate{logic->getTerm_false()}},
            ChcBody{{logic->mkLt(x, zero)}, {UninterpretedPredicate{current3}}}
        }};
    TPAEngine engine(*logic, options, TPACore::SPLIT);
    solveSystem(clauses, engine, VerificationAnswer::UNSAFE, true);
}