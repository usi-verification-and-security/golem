/*
 * Copyright (c) 2022, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include <gtest/gtest.h>
#include "engine/Kind.h"
#include "Validator.h"


class KindTest : public ::testing::Test {
protected:
    ArithLogic logic{opensmt::Logic_t::QF_LIA};
    Options options;
    ChcSystem system;
    PTRef zero;
    PTRef one;
    PTRef two;
    PTRef x, xp;

    KindTest() {
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

TEST_F(KindTest, test_KIND_simple_safe)
{
    Options options;
    options.addOption(Options::LOGIC, "QF_LIA");
//    options.addOption(Options::COMPUTE_WITNESS, "true");
    SymRef s1 = mkPredicateSymbol("s1", {intSort()});
    PTRef current = instantiatePredicate(s1, {x});
    PTRef next = instantiatePredicate(s1, {xp});
    // x = 0 => S1(x)
    // S1(x) and x' = x + 1 => S1(x')
    // S1(x) and x < 0 => false
    std::vector<ChClause> clauses{
        {
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{{logic.mkEq(xp, zero)}, {}}
        },
        {
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{{logic.mkEq(xp, logic.mkPlus(x, one))}, {UninterpretedPredicate{current}}}
        },
        {
            ChcHead{UninterpretedPredicate{logic.getTerm_false()}},
            ChcBody{{logic.mkLt(x, zero)}, {UninterpretedPredicate{current}}}
        }};
    Kind engine(logic, options);
    solveSystem(clauses, engine, VerificationResult::SAFE, false);
}

TEST_F(KindTest, test_KIND_moreInductionForward_safe)
{
    Options options;
    options.addOption(Options::LOGIC, "QF_LIA");
//    options.addOption(Options::COMPUTE_WITNESS, "true");
    SymRef s1 = mkPredicateSymbol("s1", {intSort()});
    PTRef current = instantiatePredicate(s1, {x});
    PTRef next = instantiatePredicate(s1, {xp});
    // x = 0 => S1(x)
    // S1(x) and x' = ite(x = 10, 0, x + 1) => S1(x')
    // S1(x) and x = 15 => false
    std::vector<ChClause> clauses{
        {
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{{logic.mkEq(xp, zero)}, {}}
        },
        {
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{{logic.mkEq(xp, logic.mkIte(logic.mkEq(x, logic.mkIntConst(10)), zero, logic.mkPlus(x, one)))}, {UninterpretedPredicate{current}}}
        },
        {
            ChcHead{UninterpretedPredicate{logic.getTerm_false()}},
            ChcBody{{logic.mkEq(x, logic.mkIntConst(15))}, {UninterpretedPredicate{current}}}
        }};
    Kind engine(logic, options);
    solveSystem(clauses, engine, VerificationResult::SAFE, false);
}

TEST_F(KindTest, test_KIND_moreInductionBackward_safe)
{
    Options options;
    options.addOption(Options::LOGIC, "QF_LIA");
//    options.addOption(Options::COMPUTE_WITNESS, "true");
    SymRef s1 = mkPredicateSymbol("s1", {intSort()});
    PTRef current = instantiatePredicate(s1, {x});
    PTRef next = instantiatePredicate(s1, {xp});
    // x = 0 => S1(x)
    // S1(x) and x' = ite(x = 5, 0, x + 1) => S1(x')
    // S1(x) and x = 15 => false
    std::vector<ChClause> clauses{
        {
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{{logic.mkEq(xp, zero)}, {}}
        },
        {
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{{logic.mkEq(xp, logic.mkIte(logic.mkEq(x, logic.mkIntConst(5)), zero, logic.mkPlus(x, one)))}, {UninterpretedPredicate{current}}}
        },
        {
            ChcHead{UninterpretedPredicate{logic.getTerm_false()}},
            ChcBody{{logic.mkEq(x, logic.mkIntConst(15))}, {UninterpretedPredicate{current}}}
        }};
    Kind engine(logic, options);
    solveSystem(clauses, engine, VerificationResult::SAFE, false);
}