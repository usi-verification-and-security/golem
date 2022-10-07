/*
 * Copyright (c) 2021-2022, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include <gtest/gtest.h>
#include "engine/TPA.h"
#include "Validator.h"

class TPATest : public ::testing::Test {
protected:
    ArithLogic logic{opensmt::Logic_t::QF_LIA};
    Options options;
    ChcSystem system;
    PTRef zero;
    PTRef one;
    PTRef two;
    PTRef x, xp;

    TPATest() {
        zero = logic.getTerm_IntZero();
        one = logic.getTerm_IntOne();
        two = logic.mkIntConst(2);
        x = mkIntVar("x");
        xp = mkIntVar("xp");
    }

    PTRef mkIntVar(char const * const name) { return logic.mkIntVar(name); }

    PTRef mkBoolVar(char const * const name) { return logic.mkBoolVar(name); }

    SRef boolSort() const { return logic.getSort_bool(); }

    SRef intSort() const { return logic.getSort_int(); }

    SymRef mkPredicateSymbol(std::string const & name, vec<SRef> const & argSorts) {
        SymRef sym = logic.declareFun(name, boolSort(), argSorts);
        system.addUninterpretedPredicate(sym);
        return sym;
    }

    PTRef instantiatePredicate(SymRef symbol, vec<PTRef> const & args) { return logic.mkUninterpFun(symbol, args); }

    void solveSystem(std::vector<ChClause> const & clauses, Engine & engine, VerificationResult expectedResult, bool validate) {
        for (auto const & clause : clauses) { system.addClause(clause); }

        auto normalizedSystem = Normalizer(logic).normalize(system);
        auto hypergraph = ChcGraphBuilder(logic).buildGraph(normalizedSystem);
        auto res = engine.solve(*hypergraph);
        auto answer = res.getAnswer();
        ASSERT_EQ(answer, expectedResult);
        if (validate) {
            SystemVerificationResult systemResult(std::move(res), *hypergraph);
            auto validationResult = Validator(logic).validate(*normalizedSystem.normalizedSystem, systemResult);
            ASSERT_EQ(validationResult, Validator::Result::VALIDATED);
        }
    }
};

TEST_F(TPATest, test_TPA_simple_safe)
{
    Options options;
    options.addOption(Options::LOGIC, "QF_LIA");
    options.addOption(Options::COMPUTE_WITNESS, "true");
    options.addOption(Options::ENGINE, TPAEngine::SPLIT_TPA);
    SymRef s1 = mkPredicateSymbol("s1", {intSort()});
    PTRef current = instantiatePredicate(s1, {x});
    PTRef next = instantiatePredicate(s1, {xp});
    std::vector<ChClause> clauses{{
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{{logic.mkEq(xp, zero)}, {}}},
        {
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{{logic.mkEq(xp, logic.mkPlus(x, one))}, {UninterpretedPredicate{current}}}
        },
        {
            ChcHead{UninterpretedPredicate{logic.getTerm_false()}},
            ChcBody{{logic.mkLt(x, zero)}, {UninterpretedPredicate{current}}}
        }};
    TPAEngine engine(logic, options);
    solveSystem(clauses, engine, VerificationResult::SAFE, true);
}

TEST_F(TPATest, test_TPA_simple_unsafe)
{
    Options options;
    options.addOption(Options::LOGIC, "QF_LIA");
    options.addOption(Options::COMPUTE_WITNESS, "true");
    options.addOption(Options::ENGINE, TPAEngine::SPLIT_TPA);
    SymRef s1 = mkPredicateSymbol("s1",{intSort()});
    PTRef current = instantiatePredicate(s1, {x});
    PTRef next = instantiatePredicate(s1, {xp});
    std::vector<ChClause> clauses{{
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{{logic.mkEq(xp, zero)}, {}}},
        {
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{{logic.mkEq(xp, logic.mkPlus(x, one))}, {UninterpretedPredicate{current}}}
        },
        {
            ChcHead{UninterpretedPredicate{logic.getTerm_false()}},
            ChcBody{{logic.mkGt(x, one)}, {UninterpretedPredicate{current}}}
        }};
    TPAEngine engine(logic, options);
    solveSystem(clauses, engine, VerificationResult::UNSAFE, true);
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
            ChcBody{{logic.mkEq(xp, zero)}, {}}
        },
        { // S1(x) and x' = x + 1 => S1(x')
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{{logic.mkEq(xp, logic.mkPlus(x, one))}, {UninterpretedPredicate{current}}}
        },
        { // S1(x) and x = 0 => false
            ChcHead{UninterpretedPredicate{logic.getTerm_false()}},
            ChcBody{{logic.mkEq(x, zero)}, {UninterpretedPredicate{current}}}
        }};
    TPAEngine engine(logic, options);
    solveSystem(clauses, engine, VerificationResult::UNSAFE, true);
}

TEST_F(TPATest, test_TPA_CEX_one) {
    Options options;
    options.addOption(Options::LOGIC, "QF_LIA");
    options.addOption(Options::COMPUTE_WITNESS, "true");
    options.addOption(Options::ENGINE, TPAEngine::TPA);
    SymRef s1 = mkPredicateSymbol("s1", {logic.getSort_int()});
    PTRef current = instantiatePredicate(s1, {x});
    PTRef next = instantiatePredicate(s1, {xp});
    std::vector<ChClause> clauses{{ // x' = 0 => S1(x')
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{{logic.mkEq(xp, zero)}, {}}
        },
        { // S1(x) and x' = x + 1 => S1(x')
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{{logic.mkEq(xp, logic.mkPlus(x, one))}, {UninterpretedPredicate{current}}}
        },
        { // S1(x) and x = 1 => false
            ChcHead{UninterpretedPredicate{logic.getTerm_false()}},
            ChcBody{{logic.mkEq(x, one)}, {UninterpretedPredicate{current}}}
        }};
    TPAEngine engine(logic, options);
    solveSystem(clauses, engine, VerificationResult::UNSAFE, true);
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
            ChcBody{{logic.mkEq(xp, zero)}, {}}
        },
        { // S1(x) and x' = x + 1 => S1(x')
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{{logic.mkEq(xp, logic.mkPlus(x, one))}, {UninterpretedPredicate{current}}}
        },
        { // S1(x) and x = 6 => false
            ChcHead{UninterpretedPredicate{logic.getTerm_false()}},
            ChcBody{{logic.mkEq(x, logic.mkIntConst(6))}, {UninterpretedPredicate{current}}}
        }};
    TPAEngine engine(logic, options);
    solveSystem(clauses, engine, VerificationResult::UNSAFE, true);
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
            ChcBody{{logic.mkEq(xp, zero)}, {}}
        },
        {
            ChcHead{UninterpretedPredicate{predS1Next}},
            ChcBody{{logic.mkEq(xp, logic.mkPlus(x, one))}, {UninterpretedPredicate{predS1Current}}}
        },
        {
            ChcHead{UninterpretedPredicate{predS2Current}},
            ChcBody{{logic.getTerm_true()}, {UninterpretedPredicate{predS1Current}}}
        },
        {
            ChcHead{UninterpretedPredicate{predS2Next}},
            ChcBody{{logic.mkEq(xp, logic.mkMinus(x, one))},
                {UninterpretedPredicate{predS2Current}}}
        },
        {
            ChcHead{UninterpretedPredicate{logic.getTerm_false()}},
            ChcBody{{logic.mkLt(x, zero)}, {UninterpretedPredicate{predS2Current}}}
        }};
    TPAEngine engine(logic, options);
    solveSystem(clauses, engine, VerificationResult::UNSAFE, true);
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
            ChcBody{{logic.mkEq(xp, zero)}, {}}
        },
        { // S1(x) & x' = x + 1 => S1(x')
            ChcHead{UninterpretedPredicate{predS1Next}},
            ChcBody{{logic.mkEq(xp, logic.mkPlus(x, one))}, {UninterpretedPredicate{predS1Current}}}
        },
        { // S1(x) => S2(x)
            ChcHead{UninterpretedPredicate{predS2Current}},
            ChcBody{{logic.getTerm_true()}, {UninterpretedPredicate{predS1Current}}}
        },
        { // S2(x) & x' = x + 2 => S2(x')
            ChcHead{UninterpretedPredicate{predS2Next}},
            ChcBody{{logic.mkEq(xp, logic.mkPlus(x, logic.mkIntConst(FastRational(2))))},
                {UninterpretedPredicate{predS2Current}}}
        },
        { // S2(x) & x < 0 => false
            ChcHead{UninterpretedPredicate{logic.getTerm_false()}},
            ChcBody{{logic.mkLt(x, zero)}, {UninterpretedPredicate{predS2Current}}}
        }};
    TPAEngine engine(logic, options);
    solveSystem(clauses, engine, VerificationResult::SAFE, false);
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
    PTRef val = logic.mkIntConst(FastRational(5));
    PTRef doubleVal = logic.mkIntConst(FastRational(10));
    std::vector<ChClause> clauses{{ // x = 0 and y = 5 => S1(x,y)
            ChcHead{UninterpretedPredicate{predS1Next}},
            ChcBody{{logic.mkAnd(logic.mkEq(xp, zero), logic.mkEq(yp, val))}, {}}
        },
        { // S1(x,y) and x < 5 and x' = x + 1 and y' = y => S1(x',y')
            ChcHead{UninterpretedPredicate{predS1Next}},
            ChcBody{{logic.mkAnd({logic.mkEq(xp, logic.mkPlus(x, one)),logic.mkEq(yp, y),logic.mkLt(x, val)})},
                {UninterpretedPredicate{predS1Current}}
            }
        },
        { // S1(x,y) and x >= 5 => S2(x,y)
            ChcHead{UninterpretedPredicate{predS2Current}},
            ChcBody{{logic.mkGeq(x, val)}, {UninterpretedPredicate{predS1Current}}}
        },
        { // S2(x,y) and x' = x + 1 and y' = y + 1 => S2(x',y')
            ChcHead{UninterpretedPredicate{predS2Next}},
            ChcBody{{logic.mkAnd(
                logic.mkEq(xp, logic.mkPlus(x, one)),
                logic.mkEq(yp, logic.mkPlus(y, one))
            )
            },
                {UninterpretedPredicate{predS2Current}}}
        },
        { // S2(x,y) and x = 10 and x != y => false
            ChcHead{UninterpretedPredicate{logic.getTerm_false()}},
            ChcBody{{logic.mkAnd(logic.mkEq(x, doubleVal), logic.mkNot(logic.mkEq(x, y)))},
                {UninterpretedPredicate{predS2Current}}}
        }};
    TPAEngine engine(logic, options);
    solveSystem(clauses, engine, VerificationResult::SAFE, false);
}

TEST_F(TPATest, test_transformContractVertex) {
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
    std::vector<ChClause> clauses{{ // x < 0 => S1(x)
        ChcHead{UninterpretedPredicate{predS1Next}},
        ChcBody{{logic.mkLt(xp, zero)}, {}}
    },
        { // x > 0 => S1(x)
            ChcHead{UninterpretedPredicate{predS1Next}},
            ChcBody{{logic.mkGt(xp, zero)}, {}}
        },
        { // S1(x) => S2(x)
            ChcHead{UninterpretedPredicate{predS2Current}},
            ChcBody{{logic.getTerm_true()}, {UninterpretedPredicate{predS1Current}}}
        },
        { // S2(x) and (x < 0 => x' = x - 1) and (x > 0 => x' = x + 1 => S2(x')
            ChcHead{UninterpretedPredicate{predS2Next}},
            ChcBody{{logic.mkAnd(
                logic.mkImpl(logic.mkLt(x, zero), logic.mkEq(xp, logic.mkMinus(x, one))),
                logic.mkImpl(logic.mkGt(x, zero), logic.mkEq(xp, logic.mkPlus(x, one)))
                )},
                {UninterpretedPredicate{predS2Current}}}
        },
        { // S2(x) & x = 0 => false
            ChcHead{UninterpretedPredicate{logic.getTerm_false()}},
            ChcBody{{logic.mkEq(x, zero)}, {UninterpretedPredicate{predS2Current}}}
        }};
    TPAEngine engine(logic, options);
    // FIXME: Enable validation when TPA can compute witnesses for chains
    solveSystem(clauses, engine, VerificationResult::SAFE, true);
}