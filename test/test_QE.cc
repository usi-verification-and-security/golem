/*
 * Copyright (c) 2021-2025, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include <TermUtils.h>
#include <gtest/gtest.h>
#include "QuantifierElimination.h"

using namespace golem;

class QE_RealTest : public ::testing::Test {
protected:
    ArithLogic logic {opensmt::Logic_t::QF_LRA};
    PTRef x;
    PTRef y;
    PTRef z;
    PTRef a;
    PTRef b;
    PTRef c;
    PTRef zero;
    PTRef one;
    QE_RealTest() {
        x = logic.mkRealVar("x");
        y = logic.mkRealVar("y");
        z = logic.mkRealVar("z");
        a = logic.mkBoolVar("a");
        b = logic.mkBoolVar("b");
        c = logic.mkBoolVar("c");
        zero = logic.getTerm_RealZero();
        one = logic.getTerm_RealOne();
    }
};

TEST_F(QE_RealTest, test_singleVar_Equality) {
    PTRef fla = logic.mkEq(y, x);
    QuantifierElimination qe(logic);
    PTRef res = qe.eliminate(fla, x);
    EXPECT_EQ(res, logic.getTerm_true());
    fla = logic.mkAnd(fla, logic.mkEq(x, zero));
    res = qe.eliminate(fla, x);
    std::cout << logic.printTerm(res) << std::endl;
    EXPECT_TRUE(res == logic.mkEq(y, zero) or res == logic.mkAnd(logic.mkLeq(y, zero), logic.mkGeq(y, zero)));
}

TEST_F(QE_RealTest, test_singleBoolVar) {
    /*
     * F = (and (or a b) (or (not a) c)
     * after elimination of a: (or b c)
     */
    PTRef fla = logic.mkAnd(
        logic.mkOr(a,b),
        logic.mkOr(logic.mkNot(a),c)
    );
    QuantifierElimination qe(logic);
    PTRef res = qe.eliminate(fla, a);
//    std::cout << logic.printTerm(res) << std::endl;
    EXPECT_EQ(res, logic.mkOr(b,c));
}

TEST_F(QE_RealTest, test_strictInequalities) {
    PTRef lit1 = logic.mkLeq(zero, x);
    PTRef lit2 = logic.mkLeq(x, logic.mkMinus(y, one));
    PTRef lit3 = logic.mkGeq(x, logic.mkMinus(y, one));
    PTRef lit4 = logic.mkNot(logic.mkEq(y, one));
    PTRef fla = logic.mkAnd({lit1, lit2, lit3, lit4});
    PTRef res = QuantifierElimination(logic).eliminate(fla, y);
    std::cout << logic.printTerm(res) << std::endl;
//    EXPECT_EQ(res, logic.mkNumLt(zero, x));
    // The result is equivalent to x > 0, but we are missing arithmetic simplifications to get it to that form
    // Current result is x >= 0 and x > 0 which is equivalent to x > 0;
    EXPECT_EQ(res, logic.mkAnd(logic.mkLt(zero, x), logic.mkLeq(zero, x)));
}

class TrivialQE_IntTest : public ::testing::Test {
protected:
    ArithLogic logic {opensmt::Logic_t::QF_ALIA};
    PTRef x;
    PTRef y;
    PTRef xp;
    PTRef yp;
    PTRef zero;
    PTRef one;
    TrivialQE_IntTest() :
    x {logic.mkIntVar("x")},
    y {logic.mkIntVar("y")},
    xp {logic.mkIntVar("xp")},
    yp {logic.mkIntVar("yp")},
    zero {logic.getTerm_IntZero()},
    one {logic.getTerm_IntOne()}
    { }
};

TEST_F(TrivialQE_IntTest, test_TwoIncrementedVariables) {
    PTRef base = logic.mkEq(x,y);
    PTRef inc1 = logic.mkEq(xp, logic.mkPlus(x, one));
    PTRef inc2 = logic.mkEq(yp, logic.mkPlus(y, one));
    PTRef fla = logic.mkAnd({base, inc1, inc2});
    PTRef res = TrivialQuantifierElimination(logic).tryEliminateVarsExcept(vec{xp, yp}, fla);
    // std::cout << logic.printTerm(res) << std::endl;
    EXPECT_EQ(res, logic.mkEq(xp, yp));
}

TEST_F(TrivialQE_IntTest, test_TwoDecrementedVariables) {
    PTRef base = logic.mkEq(x,y);
    PTRef dec1 = logic.mkEq(xp, logic.mkMinus(x, one));
    PTRef dec2 = logic.mkEq(yp, logic.mkMinus(y, one));
    PTRef fla = logic.mkAnd({base, dec1, dec2});
    PTRef res = TrivialQuantifierElimination(logic).tryEliminateVarsExcept(vec{xp, yp}, fla);
    // std::cout << logic.printTerm(res) << std::endl;
    EXPECT_EQ(res, logic.mkEq(xp, yp));
}

TEST_F(TrivialQE_IntTest, test_BooleanVaribles) {
    PTRef b1 = logic.mkBoolVar("b1");
    PTRef b2 = logic.mkBoolVar("b2");
    PTRef fla = logic.mkEq(b1,b2);
    PTRef res1 = TrivialQuantifierElimination(logic).tryEliminateVarsExcept(vec{b1}, fla);
    EXPECT_EQ(res1, logic.getTerm_true());
    PTRef res2 = TrivialQuantifierElimination(logic).tryEliminateVarsExcept(vec{b2}, fla);
    EXPECT_EQ(res2, logic.getTerm_true());
}

TEST_F(TrivialQE_IntTest, test_ShiftedVarAndArrayAccess) {
    SRef const arraySort = logic.getArraySort(logic.getSort_int(), logic.getSort_int());
    PTRef const s1 = logic.mkVar(arraySort, "s1");
    PTRef const s2 = logic.mkIntVar("s2");
    PTRef const a1 = logic.mkIntVar("a1");
    PTRef const a2 = logic.mkIntVar("a2");
    PTRef const fla = logic.mkAnd({logic.mkEq(a1,a2), logic.mkEq(logic.mkPlus(s2, one), a1), logic.mkEq(logic.mkSelect({s1, a2}), one)});
    PTRef const res = TrivialQuantifierElimination(logic).tryEliminateVarsExcept(vec{s1,s2}, fla);
    EXPECT_EQ(res, logic.mkEq(logic.mkSelect({s1, logic.mkPlus(s2, one)}), one));
}