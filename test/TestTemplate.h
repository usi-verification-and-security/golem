/*
 * Copyright (c) 2022, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef GOLEM_TESTTEMPLATE_H
#define GOLEM_TESTTEMPLATE_H

#include "engine/Engine.h"
#include "Validator.h"

#include <gtest/gtest.h>

#include <memory>

class EngineTest : public ::testing::Test {
protected:
    Options options;
    ChcSystem system;
    std::unique_ptr<ArithLogic> logic;

    PTRef mkBoolVar(char const * const name) { return logic->mkBoolVar(name); }

    SRef boolSort() const { return logic->getSort_bool(); }

    SymRef mkPredicateSymbol(std::string const & name, vec<SRef> const & argSorts) {
        SymRef sym = logic->declareFun(name, boolSort(), argSorts);
        system.addUninterpretedPredicate(sym);
        return sym;
    }

    PTRef instantiatePredicate(SymRef symbol, vec<PTRef> const & args) { return logic->mkUninterpFun(symbol, args); }

    void solveSystem(std::vector<ChClause> const & clauses, Engine & engine, VerificationAnswer expectedAnswer, bool validate = true) {
        for (auto const & clause : clauses) { system.addClause(clause); }

        Logic & logic = *this->logic;
        auto normalizedSystem = Normalizer(logic).normalize(system);
        auto hypergraph = ChcGraphBuilder(logic).buildGraph(normalizedSystem);
        auto res = engine.solve(*hypergraph);
        auto answer = res.getAnswer();
        ASSERT_EQ(answer, expectedAnswer);
        if (validate) {
            auto validationResult = Validator(logic).validate(*hypergraph, res);
            ASSERT_EQ(validationResult, Validator::Result::VALIDATED);
        }
    }
};

class LIAEngineTest : public EngineTest {
protected:
    PTRef zero;
    PTRef one;
    PTRef two;
    PTRef x, xp;

    LIAEngineTest() {
        logic = std::make_unique<ArithLogic>(opensmt::Logic_t::QF_LIA);
        zero = logic->getTerm_IntZero();
        one = logic->getTerm_IntOne();
        two = logic->mkIntConst(2);
        x = mkIntVar("x");
        xp = mkIntVar("xp");
    }

    PTRef mkIntVar(char const * const name) { return logic->mkIntVar(name); }

    SRef intSort() const { return logic->getSort_int(); }
};

class LRAEngineTest : public EngineTest {
protected:
    PTRef zero;
    PTRef one;
    PTRef two;
    PTRef x, xp;

    LRAEngineTest() {
        logic = std::make_unique<ArithLogic>(opensmt::Logic_t::QF_LRA);
        zero = logic->getTerm_RealZero();
        one = logic->getTerm_RealOne();
        two = logic->mkRealConst(2);
        x = mkRealVar("x");
        xp = mkRealVar("xp");
    }

    PTRef mkRealVar(char const * const name) { return logic->mkRealVar(name); }

    SRef realSort() const { return logic->getSort_real(); }
};

#endif //GOLEM_TESTTEMPLATE_H