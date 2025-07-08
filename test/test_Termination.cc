/*
 * Copyright (c) 2025, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include <gtest/gtest.h>

#include "osmt_terms.h"

#include "TransitionSystem.h"
#include "termination/LassoDetector.h"

using namespace opensmt;
using namespace golem;
using namespace golem::termination;

class TerminationTest : public ::testing::Test {
public:
    TerminationTest() : logic(Logic_t::QF_LIA) {}

    ArithLogic logic;
};

TEST_F(TerminationTest, Basic_Lasso) {
    // Init: i = 0
    // Tr: i >= 0 and i' = i + j
    auto systemType = std::make_unique<SystemType>(std::vector{logic.getSort_int()}, std::vector{logic.getSort_int()}, logic);
    PTRef i = systemType->getStateVars()[0];
    PTRef ip = systemType->getNextStateVars()[0];
    PTRef j = systemType->getAuxiliaryVars()[0];
    PTRef zero = logic.getTerm_IntZero();
    PTRef init = logic.mkEq(i, zero);
    PTRef tr = logic.mkAnd(logic.mkGeq(i, zero), logic.mkEq(ip, logic.mkPlus(i, j)));
    TransitionSystem ts(logic, std::move(systemType), init, tr, logic.getTerm_true());
    Options options;
    LassoDetector detector(options);
    auto res = detector.find_lasso(ts);
    EXPECT_EQ(LassoDetector::Answer::LASSO, res);
}

TEST_F(TerminationTest, Basic_NoLasso) {
    // Init: i = 0
    // Tr: i >= 0 and j > 0 and i' = i + j
    auto systemType = std::make_unique<SystemType>(std::vector{logic.getSort_int()}, std::vector{logic.getSort_int()}, logic);
    PTRef i = systemType->getStateVars()[0];
    PTRef ip = systemType->getNextStateVars()[0];
    PTRef j = systemType->getAuxiliaryVars()[0];
    PTRef zero = logic.getTerm_IntZero();
    PTRef init = logic.mkEq(i, zero);
    PTRef tr = logic.mkAnd({logic.mkGeq(i, zero), logic.mkGt(j, zero), logic.mkEq(ip, logic.mkPlus(i, j))});
    TransitionSystem ts(logic, std::move(systemType), init, tr, logic.getTerm_true());
    Options options;
    LassoDetector detector(options);
    auto res = detector.find_lasso(ts);
    EXPECT_EQ(LassoDetector::Answer::NO_LASSO, res);
}