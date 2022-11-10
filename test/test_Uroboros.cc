/*
 * Copyright (c) 2021-2022, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include <gtest/gtest.h>
#include "engine/Uroboros.h"
#include "Validator.h"



class UroborosTest : public ::testing::Test {
protected:
    ArithLogic logic{opensmt::Logic_t::QF_LIA};
    Options options;
    ChcSystem system;
    PTRef zero;
    PTRef one;
    PTRef two;
    PTRef x, xp;

    UroborosTest() {
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


TEST_F(UroborosTest, test_Uroboros_simple) {
    ArithLogic logic {opensmt::Logic_t::QF_LIA};
    Options options;
    options.addOption(Options::LOGIC, "QF_LIA");
    options.addOption(Options::COMPUTE_WITNESS, "true");
    SymRef s1 = logic.declareFun("s1", logic.getSort_bool(), {logic.getSort_int()});
    PTRef x = logic.mkIntVar("x");
    PTRef xp = logic.mkIntVar("xp");
    PTRef current = logic.mkUninterpFun(s1, {x});
    PTRef next = logic.mkUninterpFun(s1, {xp});
    ChcSystem system;
    system.addUninterpretedPredicate(s1);
    system.addClause( // x' = 0 => s1(x')
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{{logic.mkEq(xp, logic.getTerm_IntZero())}, {}});
    system.addClause( // s1(x) and x' = x + 1 => s1(x')
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{{logic.mkEq(xp, logic.mkPlus(x, logic.getTerm_IntOne()))}, {UninterpretedPredicate{current}}}
    );
    system.addClause( // s1(x) and x > 1 => false
            ChcHead{UninterpretedPredicate{logic.getTerm_false()}},
            ChcBody{{logic.mkGt(x, logic.getTerm_IntOne())}, {UninterpretedPredicate{current}}}
    );
    auto normalizedSystem = Normalizer(logic).normalize(system);
    auto hypergraph = ChcGraphBuilder(logic).buildGraph(normalizedSystem);
    ASSERT_TRUE(hypergraph->isNormalGraph());
    auto graph = hypergraph->toNormalGraph();
    Uroboros uroboros(logic, options);
    auto res = uroboros.solve(*graph);
    auto answer = res.getAnswer();
    ASSERT_EQ(answer, VerificationResult::UNSAFE);
    auto witness = res.getInvalidityWitness();
    SystemVerificationResult systemResult (std::move(res), *hypergraph);
    auto validationResult = Validator(logic).validate(*normalizedSystem.normalizedSystem, systemResult);
    ASSERT_EQ(validationResult, Validator::Result::VALIDATED);
}


TEST_F(UroborosTest, test_Uroboros_simple_safe)
{
    Options options;
    options.addOption(Options::LOGIC, "QF_LIA");
    options.addOption(Options::COMPUTE_WITNESS, "true");
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
    Uroboros engine(logic, options);
    solveSystem(clauses, engine, VerificationResult::SAFE, true);
}

TEST_F(UroborosTest, test_Uroboros_moreInductionForward_safe)
{
    Options options;
    options.addOption(Options::LOGIC, "QF_LIA");
    options.addOption(Options::COMPUTE_WITNESS, "true");
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
    Uroboros engine(logic, options);
    solveSystem(clauses, engine, VerificationResult::SAFE, true);
}

TEST_F(UroborosTest, test_Uroboros_moreInductionBackward_safe)
{
    Options options;
    options.addOption(Options::LOGIC, "QF_LIA");
    options.addOption(Options::COMPUTE_WITNESS, "true");
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
    Uroboros engine(logic, options);
    solveSystem(clauses, engine, VerificationResult::SAFE, true);
}