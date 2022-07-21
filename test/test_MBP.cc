//
// Created by Martin Blicha on 09.06.21.
//

#include <gtest/gtest.h>
#include "ModelBasedProjection.h"

class MBP_RealTest : public ::testing::Test {
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
    PTRef trueTerm;
    ModelBasedProjection mbp;
    MBP_RealTest() : mbp(logic) {
        x = logic.mkRealVar("x");
        y = logic.mkRealVar("y");
        z = logic.mkRealVar("z");
        a = logic.mkBoolVar("a");
        b = logic.mkBoolVar("b");
        c = logic.mkBoolVar("c");
        zero = logic.getTerm_RealZero();
        one = logic.getTerm_RealOne();
        trueTerm = logic.getTerm_true();
    }

    using Assignment = std::vector<std::pair<PTRef, PTRef>>;
    auto getModel(Assignment const & values) {
        ModelBuilder builder(logic);
        for (auto const & entry : values) {
            builder.addVarValue(entry.first, entry.second);
        }
        return builder.build();
    }
};

TEST_F(MBP_RealTest, test_AllEqualBounds) {
    PTRef x0 = logic.mkRealVar("x0");
    PTRef x1 = logic.mkRealVar("x1");
    // x0 = 0 and x1 = x0 + 1
    // (and (<= x0 0) (<= 0 x0) (<= (- x1 x0) 1) (<= 1 (- x1 x0)))
    PTRef lit1 = logic.mkLeq(x0, zero);
    PTRef lit2 = logic.mkGeq(x0, zero);
    PTRef lit3 = logic.mkLeq(logic.mkMinus(x1, x0), one);
    PTRef lit4 = logic.mkGeq(logic.mkMinus(x1, x0), one);
    auto model = getModel({{x0, zero}, {x1, one}});
    PTRef result = mbp.project(logic.mkAnd({lit1, lit2, lit3, lit4}), {x0}, *model);
    // result should be equivalent to "x1 = 1"
    std::cout << logic.printTerm(result) << std::endl;
    ASSERT_EQ(result, logic.mkAnd(logic.mkLeq(one, x1), logic.mkLeq(x1, one)));
}

TEST_F(MBP_RealTest, test_AllEqualBoundsTwoVars) {
    // x = y and y = z
    PTRef eq1 = logic.mkEq(x, y);
    PTRef eq2 = logic.mkEq(y, z);
    auto model = getModel({{x,zero}, {y,zero}, {z,zero}});
    PTRef result = mbp.project(logic.mkAnd(eq1, eq2), {x,y}, *model);
    // result should be equivalent to true
    std::cout << logic.printTerm(result) << std::endl;
    ASSERT_EQ(result, logic.getTerm_true());
}

TEST_F(MBP_RealTest, test_SimpleDisjunction) {
    PTRef x0 = logic.mkRealVar("x0");
    PTRef x1 = logic.mkRealVar("x1");
    // (a or b) and (x0 <= 0) and (x0 >= x1))
    PTRef part1 = logic.mkOr(a,b);
    PTRef part2 = logic.mkLeq(x0, zero);
    PTRef part3 = logic.mkLeq(x1, x0);
    auto model = getModel({{x0,zero}, {x1, zero}, {a, trueTerm}, {b, trueTerm}});
    PTRef result = mbp.project(logic.mkAnd({part1, part2, part3}), {x0}, *model);
    // NOTE: Check that the result is not unnecessary strict.
    // Ideally the result should be "(a or b) and (x1 <= 0)"
    std::cout << logic.printTerm(result) << std::endl;
    ASSERT_TRUE(logic.isAnd(result));
    PTRef expectedConjunct = logic.mkLeq(x1, zero);
    bool found = false;
    for (int i = 0; i < logic.getPterm(result).size(); ++i) {
        found = found or logic.getPterm(result)[i] == expectedConjunct;
    }
    ASSERT_TRUE(found);
}

TEST_F(MBP_RealTest, test_TwoInequalities_BothStrict) {
    PTRef lower = logic.mkLt(y, x);
    PTRef upper = logic.mkLt(x, zero);
    auto model = getModel({{x,logic.mkRealConst(FastRational(-1))}, {y, logic.mkRealConst(FastRational(-3,2))}});
    auto res = mbp.project(logic.mkAnd(lower, upper), {x}, *model);
    ASSERT_EQ(logic.mkLt(y, zero), res);
}

TEST_F(MBP_RealTest, test_TwoInequalities_StrictNonstrict) {
    PTRef lower = logic.mkLt(y, x);
    PTRef upper = logic.mkLeq(x, zero);
    auto model = getModel({{x,zero}, {y,logic.mkRealConst(FastRational(-3,2))}});
    auto res = mbp.project(logic.mkAnd(lower, upper), {x}, *model);
    ASSERT_EQ(logic.mkLt(y, zero), res);
}

TEST_F(MBP_RealTest, test_TwoInequalities_NonstrictStrict) {
    PTRef lower = logic.mkLeq(y, x);
    PTRef upper = logic.mkLt(x, zero);
    PTRef val = logic.mkRealConst(FastRational(-3,2));
    auto model = getModel({{x,val}, {y,val}});
    auto res = mbp.project(logic.mkAnd(lower, upper), {x}, *model);
    ASSERT_EQ(logic.mkLt(y, zero), res);
}

TEST_F(MBP_RealTest, test_TwoInequalities_NonstrictNonstrict) {
    PTRef lower = logic.mkLeq(y, x);
    PTRef upper = logic.mkLeq(x, zero);
    auto model = getModel({{x,zero}, {y,logic.mkRealConst(FastRational(-3,2))}});
    auto res = mbp.project(logic.mkAnd(lower, upper), {x}, *model);
    ASSERT_EQ(logic.mkLeq(y, zero), res);
}

TEST_F(MBP_RealTest, test_Disequality) {
    PTRef diseq = logic.mkNot(logic.mkEq(y, logic.mkPlus(y, one)));
    auto model = getModel({{y,zero}});
    auto res = mbp.project(diseq, {y}, *model);
    ASSERT_EQ(logic.getTerm_true(), res);
}

TEST_F(MBP_RealTest, test_strictInequalitiesProblem) {
    PTRef lit1 = logic.mkLeq(x, logic.mkMinus(y, one));
    PTRef lit2 = logic.mkGeq(x, logic.mkMinus(y, one));
    PTRef lit3 = logic.mkNot(logic.mkEq(y, one));
    PTRef fla = logic.mkAnd({lit1, lit2, lit3});
    auto model = getModel({{x,one}, {y,logic.mkRealConst(FastRational(2))}});
    PTRef res = mbp.project(fla, {y}, *model);
    std::cout << logic.printTerm(res) << std::endl;
    EXPECT_EQ(res, logic.mkLt(zero, x));
}

TEST_F(MBP_RealTest, test_strictNonStrictEqualitiesSameBound_1) {
    PTRef lit1 = logic.mkLeq(zero, x);
    PTRef lit2 = logic.mkLt(zero, x);
    PTRef lit3 = logic.mkLt(x,y);
    // 0 <= x and 0 < x and x < y
    PTRef fla = logic.mkAnd({lit1, lit2, lit3});
    auto model = getModel({{x,one}, {y,logic.mkRealConst(FastRational(2))}});
    PTRef res = mbp.project(fla, {x}, *model);
    std::cout << logic.printTerm(res) << std::endl;
    EXPECT_EQ(res, logic.mkLt(zero, y));
}

TEST_F(MBP_RealTest, test_strictNonStrictEqualitiesSameBound_2) {
    PTRef lit1 = logic.mkLeq(zero, x);
    PTRef lit2 = logic.mkLt(zero, x);
    PTRef lit3 = logic.mkLeq(x,y);
    // 0 <= x and 0 < x and x <= y
    PTRef fla = logic.mkAnd({lit1, lit2, lit3});
    auto model = getModel({{x,one}, {y,logic.mkRealConst(FastRational(2))}});
    PTRef res = mbp.project(fla, {x}, *model);
    std::cout << logic.printTerm(res) << std::endl;
//    EXPECT_EQ(res, logic.mkLt(zero, y));
    // Currently contains redundant conjuncts
    PTRef expected = logic.mkLt(zero, y);
    auto containsConjunct = [&](PTRef ref) {
        if (not logic.isAnd(ref)) { return false; }
        Pterm const& term = logic.getPterm(ref);
        for (int i = 0; i < term.size(); ++i) {
            if (term[i] == expected) { return true; }
        }
        return false;
    };
    EXPECT_TRUE(res == expected or containsConjunct(res));
}

TEST_F(MBP_RealTest, test_RegressionTest) {
    PTRef x = this->x;
    PTRef y = this->y;
    PTRef xp = logic.mkRealVar("xp");
    PTRef yp = logic.mkRealVar("yp");
    // y >= 256 and x <= 64
    PTRef part1 = logic.mkAnd(
        logic.mkLeq(x, logic.mkRealConst(FastRational(64))),
        logic.mkLeq(y, logic.mkRealConst(FastRational(256)))
    );
    // yp - y >= 0 and y - yp >= 0 and xp <= x + 256 and yp > x + 254
    PTRef diff = logic.mkMinus(y, yp);
    PTRef part2 = logic.mkAnd({
       logic.mkLeq(diff, zero),
       logic.mkLeq(zero, diff),
       logic.mkLeq(xp, logic.mkPlus(x, logic.mkRealConst(FastRational(256)))),
       logic.mkGt(yp, logic.mkPlus(x, logic.mkRealConst(FastRational(254))))
    });
    // yp != xp and yp <= xp
    PTRef part3 = logic.mkAnd(
        logic.mkLt(yp, xp),
//        logic.getTerm_true()
        logic.mkLeq(yp, xp)
    );
    PTRef fla = logic.mkAnd({part1, part2, part3});
    auto model = getModel({{x, logic.mkRealConst(FastRational(3, 2))},
                           {y, logic.mkRealConst(FastRational(256))},
                           {xp, logic.mkRealConst(FastRational(513, 2))},
                           {yp, logic.mkRealConst(FastRational(256))}
                          });
    ASSERT_EQ(model->evaluate(fla), logic.getTerm_true());
    PTRef midpoint = mbp.project(fla, {xp,yp}, *model);
    std::cout << logic.printTerm(midpoint) << std::endl;
    auto checker = getModel({{x,zero}, {y, logic.mkRealConst(FastRational(256))}});
    ASSERT_NE(checker->evaluate(midpoint), logic.getTerm_true());
}

TEST_F(MBP_RealTest, test_strictNonStrict_1) {
    // x >= 0 and x > y and x <= 2 and x <= z; M: y -> 0, x -> 1, z -> 1
    // y should be picked for substitution
    // result is 0 <= y < 2 and y < z
    PTRef two = logic.mkRealConst(FastRational(2));
    PTRef lit1 = logic.mkLeq(zero, x);
    PTRef lit2 = logic.mkLt(y, x);
    PTRef lit3 = logic.mkLeq(x, two);
    PTRef lit4 = logic.mkLeq(x, z);
    PTRef fla = logic.mkAnd({lit1, lit2, lit3, lit4});
    auto model = getModel({{x, one}, {y, zero}, {z, one}});
    ASSERT_EQ(model->evaluate(fla), logic.getTerm_true());
    PTRef res = mbp.project(fla, {x}, *model);
    std::cout << logic.printTerm(res) << std::endl;
    EXPECT_EQ(res, logic.mkAnd({logic.mkLeq(zero, y), logic.mkLt(y, two), logic.mkLt(y, z)}));
}

TEST_F(MBP_RealTest, test_strictNonStrict_2) {
    // x >= 0 and x > y and x <= 2 and x <=z; M: y -> 1/2, x -> 1, z -> 1
    // y should be picked for substitution
    // result is 0 <= y < 2 and y < z
    PTRef two = logic.mkRealConst(FastRational(2));
    PTRef half = logic.mkRealConst(FastRational(1,2));
    PTRef lit1 = logic.mkLeq(zero, x);
    PTRef lit2 = logic.mkLt(y, x);
    PTRef lit3 = logic.mkLeq(x, two);
    PTRef lit4 = logic.mkLeq(x, z);
    PTRef fla = logic.mkAnd({lit1, lit2, lit3, lit4});
    auto model = getModel({{x, one}, {y, half}, {z, one}});
    ASSERT_EQ(model->evaluate(fla), logic.getTerm_true());
    PTRef res = mbp.project(fla, {x}, *model);
    std::cout << logic.printTerm(res) << std::endl;
    EXPECT_EQ(res, logic.mkAnd({logic.mkLeq(zero, y), logic.mkLt(y, two), logic.mkLt(y, z)}));
}

TEST_F(MBP_RealTest, test_strictNonStrict_3) {
    // x > 0 and x >= y and x <= 2 and x <= z; M: y -> 1/2, x -> 1, z -> 1
    // y should be picked for substitution
    // result is 0 < y <= 2 and y <= z
    PTRef two = logic.mkRealConst(FastRational(2));
    PTRef half = logic.mkRealConst(FastRational(1,2));
    PTRef lit1 = logic.mkLt(zero, x);
    PTRef lit2 = logic.mkLeq(y, x);
    PTRef lit3 = logic.mkLeq(x, two);
    PTRef lit4 = logic.mkLeq(x, z);
    PTRef fla = logic.mkAnd({lit1, lit2, lit3, lit4});
    auto model = getModel({{x, one}, {y, half}, {z, one}});
    ASSERT_EQ(model->evaluate(fla), logic.getTerm_true());
    PTRef res = mbp.project(fla, {x}, *model);
    std::cout << logic.printTerm(res) << std::endl;
    EXPECT_EQ(res, logic.mkAnd({logic.mkLt(zero, y), logic.mkLeq(y, two), logic.mkLeq(y,z)}));
}

TEST_F(MBP_RealTest, test_strictNonStrict_4) {
    // x > 0 and x > y and x <= 2 and x <= z; M: y -> 1/2, x -> 1, z -> 1
    // y should be picked for substitution
    // result is 0 <= y < 2 and y < z
    PTRef two = logic.mkRealConst(FastRational(2));
    PTRef half = logic.mkRealConst(FastRational(1,2));
    PTRef lit1 = logic.mkLt(zero, x);
    PTRef lit2 = logic.mkLt(y, x);
    PTRef lit3 = logic.mkLeq(x, two);
    PTRef lit4 = logic.mkLeq(x, z);
    PTRef fla = logic.mkAnd({lit1, lit2, lit3, lit4});
    auto model = getModel({{x, one}, {y, half}, {z, one}});
    ASSERT_EQ(model->evaluate(fla), logic.getTerm_true());
    PTRef res = mbp.project(fla, {x}, *model);
    std::cout << logic.printTerm(res) << std::endl;
    EXPECT_EQ(res, logic.mkAnd({logic.mkLeq(zero, y), logic.mkLt(y, two), logic.mkLt(y,z)}));
}

TEST_F(MBP_RealTest, test_avoidRedundantBounds) {
    // x <= y and y <= 0 and y <= 1 (last one is redundant)
    PTRef lit1 = logic.mkLeq(x,y);
    PTRef lit2 = logic.mkLeq(y, zero);
    PTRef lit3 = logic.mkLeq(y, one);
    PTRef fla = logic.mkAnd({lit1, lit2, lit3});
    auto model = getModel({{x, logic.getTerm_RealMinusOne()}, {y, zero}});
    PTRef res = mbp.project(fla, {y}, *model);
    std::cout << logic.printTerm(res) << std::endl;
    EXPECT_EQ(res, logic.mkLeq(x, zero)); // The redundant bound x <= 1 should not appear in the projection
}

TEST_F(MBP_RealTest, test_EqualityNotNormalized) {
    // x + y = x + 1
    PTRef lhs = logic.mkPlus(x,y);
    PTRef rhs = logic.mkPlus(x, one);
    PTRef lit = logic.mkEq(lhs, rhs);
    auto model = getModel({{x,one}, {y,one}});
    PTRef res = mbp.project(lit, {x}, *model);
    std::cout << logic.printTerm(res) << std::endl;
    // EXPECT_EQ(res, logic.mkEq(y,one));
     EXPECT_EQ(res, logic.mkEq(logic.mkPlus(y, logic.getTerm_RealMinusOne()), zero));
}

TEST_F(MBP_RealTest, test_singleUpperBound) {
    // y <= x and z <= x and 0 <= x and x <= 1
    // Using the single upper bound for elimination is strictly more general than using any of the lower bounds
    PTRef lit1 = logic.mkLeq(y,x);
    PTRef lit2 = logic.mkLeq(z, x);
    PTRef lit3 = logic.mkLeq(zero, x);
    PTRef lit4 = logic.mkLeq(x, one);
    PTRef fla = logic.mkAnd({lit1, lit2, lit3, lit4});
    auto model = getModel({{x,zero}, {y,zero}, {z,zero}});
    PTRef res = mbp.project(fla, {x}, *model);
    std::cout << logic.printTerm(res) << std::endl;
    EXPECT_EQ(res, logic.mkAnd(logic.mkLeq(y, one), logic.mkLeq(z, one)));
}

TEST_F(MBP_RealTest, test_avoidRedundantBounds_2) {
    // y + z <= x and x <= 0 and y + z <= 1 and z = 0
    PTRef yz = logic.mkPlus(y,z);
    PTRef lit1 = logic.mkLeq(yz,x);
    PTRef lit2 = logic.mkLeq(x, zero);
    PTRef lit3 = logic.mkLeq(yz, one);
    PTRef lit4 = logic.mkEq(z, zero);
    PTRef fla = logic.mkAnd({lit1, lit2, lit3, lit4});
    auto model = getModel({{x,zero}, {y,zero}, {z,zero}});
    PTRef res = mbp.project(fla, {x,z}, *model);
    std::cout << logic.printTerm(res) << std::endl;
    EXPECT_EQ(res, logic.mkAnd({logic.mkLeq(y, zero)}));
}

TEST_F(MBP_RealTest, test_avoidRedundantBounds_3) {
    // y  <= x and x <= 0 and y <= 1
    PTRef lit1 = logic.mkLeq(y,x);
    PTRef lit2 = logic.mkLeq(x, zero);
    PTRef lit3 = logic.mkLeq(y, one);
    PTRef fla = logic.mkAnd({lit1, lit2, lit3});
    auto model = getModel({{x,zero}, {y,zero}});
    PTRef res = mbp.project(fla, {x}, *model);
    std::cout << logic.printTerm(res) << std::endl;
    EXPECT_EQ(res, logic.mkAnd({logic.mkLeq(y, zero)}));
}

TEST_F(MBP_RealTest, test_hiddenEquality) {
    // z <= x and y  <= x and x <= y and  x <= 1
    PTRef lit3 = logic.mkLeq(z, x);
    PTRef lit1 = logic.mkLeq(y, x);
    PTRef lit2 = logic.mkLeq(x, y);
    PTRef lit4 = logic.mkLeq(x, one);
    PTRef fla = logic.mkAnd({lit1, lit2, lit3, lit4});
    auto model = getModel({{x,zero}, {y,zero}, {z,zero}});
    PTRef res = mbp.project(fla, {x}, *model);
    std::cout << logic.printTerm(res) << std::endl;
    EXPECT_EQ(res, logic.mkAnd({logic.mkLeq(z, y), logic.mkLeq(y, one)}));
}


class MBP_IntTest : public ::testing::Test {
protected:
    ArithLogic logic {opensmt::Logic_t::QF_LIA};
    PTRef x;
    PTRef y;
    PTRef z;
    PTRef a;
    PTRef b;
    PTRef c;
    PTRef zero;
    PTRef one;
    PTRef minusOne;
    ModelBasedProjection mbp;
    MBP_IntTest() : mbp(logic) {
        x = logic.mkIntVar("x");
        y = logic.mkIntVar("y");
        z = logic.mkIntVar("z");
        a = logic.mkBoolVar("a");
        b = logic.mkBoolVar("b");
        c = logic.mkBoolVar("c");
        zero = logic.getTerm_IntZero();
        one = logic.getTerm_IntOne();
        minusOne = logic.getTerm_IntMinusOne();
    }

    using Assignment = std::vector<std::pair<PTRef, PTRef>>;
    auto getModel(Assignment const & values) {
        ModelBuilder builder(logic);
        for (auto const & entry : values) {
            builder.addVarValue(entry.first, entry.second);
        }
        return builder.build();
    }
};

TEST_F(MBP_IntTest, test_oneLower_oneUpper) {
    PTRef lit1 = logic.mkLeq(x,y);
    PTRef lit2 = logic.mkLeq(y,zero);
    PTRef fla = logic.mkAnd(lit1, lit2);
    auto model = getModel({{x, minusOne}, {y, zero}});
    PTRef res = mbp.project(fla, {y}, *model);
    EXPECT_EQ(res, logic.mkLeq(x, zero));
}

TEST_F(MBP_IntTest, test_oneLower_oneUpper_withCoefficients_1) {
    PTRef two = logic.mkIntConst(FastRational(2));
    PTRef y2 = logic.mkTimes(two, y);
    PTRef lit1 = logic.mkLeq(x,y2);
    PTRef lit2 = logic.mkLt(y2,zero);
    PTRef fla = logic.mkAnd(lit1, lit2);
    auto model = getModel({{x, logic.mkIntConst(FastRational(-2))}, {y, minusOne}});
    PTRef res = mbp.project(fla, {y}, *model);
    std::cout << logic.pp(res) << std::endl;
    EXPECT_EQ(res, logic.mkLeq(x, logic.mkIntConst(FastRational(-2))));
}

TEST_F(MBP_IntTest, test_oneLower_oneUpper_withCoefficients_2) {
    PTRef two = logic.mkIntConst(FastRational(2));
    PTRef three = logic.mkIntConst(FastRational(3));
    PTRef y2 = logic.mkTimes(two, y);
    PTRef y3 = logic.mkTimes(three, y);
    PTRef lit1 = logic.mkLeq(zero,y3);
    PTRef lit2 = logic.mkLeq(y2,zero);
    PTRef fla = logic.mkAnd(lit1, lit2);
    auto model = getModel({{y, zero}});
    PTRef res = mbp.project(fla, {y}, *model);
    std::cout << logic.pp(res) << std::endl;
    EXPECT_EQ(res, logic.getTerm_true());
}

TEST_F(MBP_IntTest, test_oneLower_oneUpper_withCoefficients_3) {
    PTRef two = logic.mkIntConst(FastRational(2));
    PTRef three = logic.mkIntConst(FastRational(3));
    PTRef y2 = logic.mkTimes(two, y);
    PTRef y3 = logic.mkTimes(three, y);
    PTRef lit1 = logic.mkLeq(x,y3);
    PTRef lit2 = logic.mkLeq(y2,z);
    PTRef fla = logic.mkAnd(lit1, lit2);
    auto model = getModel({{x, three}, {y, one}, {z, two}});
    PTRef res = mbp.project(fla, {y}, *model);
    std::cout << logic.pp(res) << std::endl;
    // MB: not 100% sure, but this should be the correct result
    EXPECT_EQ(res, logic.mkAnd(
        logic.mkLeq(logic.mkTimes(two,x), logic.mkTimes(three,z)),
        logic.mkEq(logic.mkMod(z, two), zero)
    ));
}

TEST_F(MBP_IntTest, test_ElimTwoVariables_withDivConstraints) {
    PTRef two = logic.mkIntConst(FastRational(2));
    PTRef three = logic.mkIntConst(FastRational(3));
    PTRef y2 = logic.mkTimes(two, y);
    PTRef y3 = logic.mkTimes(three, y);
    PTRef lit1 = logic.mkLeq(x,y3);
    PTRef lit2 = logic.mkLeq(y2,z);
    PTRef fla = logic.mkAnd(lit1, lit2);
    auto model = getModel({{x, three}, {y, one}, {z, two}});
    PTRef res = mbp.project(fla, {y,z}, *model);
    std::cout << logic.pp(res) << std::endl;
    EXPECT_EQ(res, logic.getTerm_true());
}

TEST_F(MBP_IntTest, test_Equality) {
    PTRef two = logic.mkIntConst(FastRational(2));
    PTRef lit1 = logic.mkLeq(x,y);
    PTRef lit2 = logic.mkLeq(y,z);
    PTRef lit3 = logic.mkEq(y, two);
    PTRef fla = logic.mkAnd({lit1, lit2, lit3});
    auto model = getModel({{x, logic.mkIntConst(FastRational(-2))}, {y, two}, {z, two}});
    PTRef res = mbp.project(fla, {y}, *model);
    std::cout << logic.pp(res) << std::endl;
    EXPECT_EQ(res, logic.mkAnd(logic.mkLeq(x, two), logic.mkLeq(two, z)));
}

TEST_F(MBP_IntTest, test_EqualityWithCoefficients) {
    PTRef two = logic.mkIntConst(FastRational(2));
    PTRef three = logic.mkIntConst(FastRational(3));
    PTRef x2 = logic.mkTimes(x, two);
    PTRef x3 = logic.mkTimes(x, three);
    PTRef lit1 = logic.mkEq(x2,y);
    PTRef lit2 = logic.mkLeq(z,x3);
    PTRef fla = logic.mkAnd({lit1, lit2});
    auto model = getModel({{x, zero}, {y, zero}, {z, minusOne}});
    PTRef res = mbp.project(fla, {x}, *model);
    std::cout << logic.pp(res) << std::endl;
    EXPECT_EQ(res,logic.mkAnd(
        logic.mkLeq(logic.mkTimes(z, two), logic.mkTimes(three, y)),
        logic.mkEq(zero, logic.mkMod(y, two))
    ));
}

TEST_F(MBP_IntTest, test_EqualityAsConjunctionOfInequalities) {
    PTRef two = logic.mkIntConst(FastRational(2));
    PTRef three = logic.mkIntConst(FastRational(3));
    PTRef x2 = logic.mkTimes(x, two);
    PTRef x3 = logic.mkTimes(x, three);
    PTRef lit1 = logic.mkLeq(x2,y);
    PTRef lit2 = logic.mkLeq(y,x2);
    PTRef lit3 = logic.mkLeq(z,x3);
    PTRef fla = logic.mkAnd({lit1, lit2, lit3});
    auto model = getModel({{x, zero}, {y, zero}, {z, minusOne}});
    PTRef res = mbp.project(fla, {x}, *model);
    std::cout << logic.pp(res) << std::endl;
    EXPECT_EQ(res,logic.mkAnd(
        logic.mkLeq(logic.mkTimes(z, two), logic.mkTimes(three, y)),
        logic.mkEq(zero, logic.mkMod(y, two))
    ));
}

TEST_F(MBP_IntTest, test_AuxiliaryVarAndDisequality) {
    // Auxiliary variable is used because of divisibility constraint and its value is needed
    // in the model in order to, e.g., decide disequality.
    // Our current model silently returns a default value (0) if the variable is not known
    PTRef two = logic.mkIntConst(FastRational(2));
    PTRef three = logic.mkIntConst(FastRational(3));
    PTRef y2 = logic.mkTimes(two, y);
    // x - 1 mod 2 = 0
    PTRef lit1 = logic.mkEq(logic.mkMod(logic.mkMinus(x, one), two), zero);
    // x - 2y != 0
    PTRef lit2 = logic.mkNot(logic.mkEq(logic.mkMinus(x,y2), zero));
    // x <= 3
    PTRef lit3 = logic.mkLeq(x, three);
    // x >= 3
    PTRef lit4 = logic.mkLeq(three, x);
    PTRef fla = logic.mkAnd({lit1, lit2, lit3, lit4});
    auto model = getModel({{x, logic.mkIntConst(FastRational(3))}, {y, one}});
    PTRef res = mbp.project(fla, {x}, *model);
    std::cout << logic.pp(res) << std::endl;
    EXPECT_EQ(res, logic.getTerm_true());
}

TEST_F(MBP_IntTest, test_ResolvesToTrue) {
    PTRef five = logic.mkIntConst(FastRational(5));
    PTRef three = logic.mkIntConst(FastRational(3));
    PTRef y5 = logic.mkTimes(y, five);
    // x - 3 <= 5y <= x
    PTRef lit1 = logic.mkLeq(y5, x);
    PTRef lit2 = logic.mkLeq(logic.mkMinus(x, three), y5);
    PTRef fla = logic.mkAnd({lit1, lit2});
    auto model = getModel({{x, logic.mkIntConst(FastRational(6))}, {y, one}});
    PTRef res = mbp.project(fla, {y}, *model);
    std::cout << logic.pp(res) << std::endl;
    // Because of the model x -> 6, we get that 5 divides (x - 1)
    EXPECT_EQ(res, logic.mkEq(zero, logic.mkMod(logic.mkMinus(x, one), five)));
}

