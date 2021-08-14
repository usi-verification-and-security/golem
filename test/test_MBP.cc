//
// Created by Martin Blicha on 09.06.21.
//

#include <gtest/gtest.h>
#include "ModelBasedProjection.h"

class MBP_RealTest : public ::testing::Test {
protected:
    LRALogic logic;
    PTRef x;
    PTRef y;
    PTRef z;
    PTRef a;
    PTRef b;
    PTRef c;
    PTRef zero;
    PTRef one;
    ModelBasedProjection mbp;
    MBP_RealTest() : mbp(logic) {
        x = logic.mkNumVar("x");
        y = logic.mkNumVar("y");
        z = logic.mkNumVar("z");
        a = logic.mkBoolVar("a");
        b = logic.mkBoolVar("b");
        c = logic.mkBoolVar("c");
        zero = logic.getTerm_NumZero();
        one = logic.getTerm_NumOne();
    }
};

TEST_F(MBP_RealTest, test_AllEqualBounds) {
    PTRef x0 = logic.mkNumVar("x0");
    PTRef x1 = logic.mkNumVar("x1");
    // x0 = 0 and x1 = x0 + 1
    // (and (<= x0 0) (<= 0 x0) (<= (- x1 x0) 1) (<= 1 (- x1 x0)))
    PTRef lit1 = logic.mkNumLeq(x0, logic.getTerm_NumZero());
    PTRef lit2 = logic.mkNumGeq(x0, logic.getTerm_NumZero());
    PTRef lit3 = logic.mkNumLeq(logic.mkNumMinus(x1, x0), logic.getTerm_NumOne());
    PTRef lit4 = logic.mkNumGeq(logic.mkNumMinus(x1, x0), logic.getTerm_NumOne());
    ModelBuilder builder(logic);
    builder.addVarValue(x0, logic.getTerm_NumZero());
    builder.addVarValue(x1, logic.getTerm_NumOne());
    auto model = builder.build();
    PTRef result = mbp.project(logic.mkAnd({lit1, lit2, lit3, lit4}), {x0}, *model);
    // result should be equivalent to "x1 = 1"
    std::cout << logic.printTerm(result) << std::endl;
    ASSERT_EQ(result, logic.mkAnd(logic.mkNumLeq(one, x1), logic.mkNumLeq(x1, one)));
}

TEST_F(MBP_RealTest, test_AllEqualBoundsTwoVars) {
    // x = y and y = z
    PTRef eq1 = logic.mkEq(x, y);
    PTRef eq2 = logic.mkEq(y, z);
    ModelBuilder builder(logic);
    builder.addVarValue(x, zero);
    builder.addVarValue(y, zero);
    builder.addVarValue(z, zero);
    auto model = builder.build();
    PTRef result = mbp.project(logic.mkAnd(eq1, eq2), {x,y}, *model);
    // result should be equivalent to true
    std::cout << logic.printTerm(result) << std::endl;
    ASSERT_EQ(result, logic.getTerm_true());
}

TEST_F(MBP_RealTest, test_SimpleDisjunction) {
    PTRef x0 = logic.mkNumVar("x0");
    PTRef x1 = logic.mkNumVar("x1");
    // (a or b) and (x0 <= 0) and (x0 >= x1))
    PTRef part1 = logic.mkOr(a,b);
    PTRef part2 = logic.mkNumLeq(x0, zero);
    PTRef part3 = logic.mkNumLeq(x1, x0);
    ModelBuilder builder(logic);
    builder.addVarValue(x0, zero);
    builder.addVarValue(x1, zero);
    builder.addVarValue(a, logic.getTerm_true());
    builder.addVarValue(b, logic.getTerm_true());
    auto model = builder.build();
    PTRef result = mbp.project(logic.mkAnd({part1, part2, part3}), {x0}, *model);
    // NOTE: Check that the result is not unnecessary strict.
    // Ideally the result should be "(a or b) and (x1 <= 0)"
    std::cout << logic.printTerm(result) << std::endl;
    ASSERT_TRUE(logic.isAnd(result));
    PTRef expectedConjunct = logic.mkNumLeq(x1, zero);
    bool found = false;
    for (int i = 0; i < logic.getPterm(result).size(); ++i) {
        found = found or logic.getPterm(result)[i] == expectedConjunct;
    }
    ASSERT_TRUE(found);
}

TEST_F(MBP_RealTest, test_TwoInequalities_BothStrict) {
    PTRef lower = logic.mkNumLt(y, x);
    PTRef upper = logic.mkNumLt(x, zero);
    ModelBuilder builder(logic);
    builder.addVarValue(x, logic.mkConst(FastRational(-1)));
    builder.addVarValue(y, logic.mkConst(FastRational(-3,2)));
    auto model = builder.build();
    auto res = mbp.project(logic.mkAnd(lower, upper), {x}, *model);
    ASSERT_EQ(logic.mkNumLt(y, zero), res);
}

TEST_F(MBP_RealTest, test_TwoInequalities_StrictNonstrict) {
    PTRef lower = logic.mkNumLt(y, x);
    PTRef upper = logic.mkNumLeq(x, zero);
    ModelBuilder builder(logic);
    builder.addVarValue(x, zero);
    builder.addVarValue(y, logic.mkConst(FastRational(-3,2)));
    auto model = builder.build();
    auto res = mbp.project(logic.mkAnd(lower, upper), {x}, *model);
    ASSERT_EQ(logic.mkNumLt(y, zero), res);
}

TEST_F(MBP_RealTest, test_TwoInequalities_NonstrictStrict) {
    PTRef lower = logic.mkNumLeq(y, x);
    PTRef upper = logic.mkNumLt(x, zero);
    ModelBuilder builder(logic);
    builder.addVarValue(x, logic.mkConst(FastRational(-3,2)));
    builder.addVarValue(y, logic.mkConst(FastRational(-3,2)));
    auto model = builder.build();
    auto res = mbp.project(logic.mkAnd(lower, upper), {x}, *model);
    ASSERT_EQ(logic.mkNumLt(y, zero), res);
}

TEST_F(MBP_RealTest, test_TwoInequalities_NonstrictNonstrict) {
    PTRef lower = logic.mkNumLeq(y, x);
    PTRef upper = logic.mkNumLeq(x, zero);
    ModelBuilder builder(logic);
    builder.addVarValue(x, zero);
    builder.addVarValue(y, logic.mkConst(FastRational(-3,2)));
    auto model = builder.build();
    auto res = mbp.project(logic.mkAnd(lower, upper), {x}, *model);
    ASSERT_EQ(logic.mkNumLeq(y, zero), res);
}

TEST_F(MBP_RealTest, test_Disequality) {
    PTRef diseq = logic.mkNot(logic.mkEq(y, logic.mkNumPlus(y, one)));
    ModelBuilder builder(logic);
    builder.addVarValue(y, zero);
    auto model = builder.build();
    auto res = mbp.project(diseq, {y}, *model);
    ASSERT_EQ(logic.getTerm_true(), res);
}

TEST_F(MBP_RealTest, test_strictInequalitiesProblem) {
    PTRef lit1 = logic.mkNumLeq(x, logic.mkNumMinus(y, one));
    PTRef lit2 = logic.mkNumGeq(x, logic.mkNumMinus(y, one));
    PTRef lit3 = logic.mkNot(logic.mkEq(y, one));
    PTRef fla = logic.mkAnd({lit1, lit2, lit3});
    ModelBuilder builder(logic);
    builder.addVarValue(x, logic.mkConst(FastRational(1)));
    builder.addVarValue(y, logic.mkConst(FastRational(2)));
    auto model = builder.build();
    PTRef res = mbp.project(fla, {y}, *model);
    std::cout << logic.printTerm(res) << std::endl;
    EXPECT_EQ(res, logic.mkNumLt(zero, x));
}

TEST_F(MBP_RealTest, test_strictNonStrictEqualitiesSameBound_1) {
    PTRef lit1 = logic.mkNumLeq(zero, x);
    PTRef lit2 = logic.mkNumLt(zero, x);
    PTRef lit3 = logic.mkNumLt(x,y);
    // 0 <= x and 0 < x and x < y
    PTRef fla = logic.mkAnd({lit1, lit2, lit3});
    ModelBuilder builder(logic);
    builder.addVarValue(x, logic.mkConst(FastRational(1)));
    builder.addVarValue(y, logic.mkConst(FastRational(2)));
    auto model = builder.build();
    PTRef res = mbp.project(fla, {x}, *model);
    std::cout << logic.printTerm(res) << std::endl;
    EXPECT_EQ(res, logic.mkNumLt(zero, y));
}

TEST_F(MBP_RealTest, test_strictNonStrictEqualitiesSameBound_2) {
    PTRef lit1 = logic.mkNumLeq(zero, x);
    PTRef lit2 = logic.mkNumLt(zero, x);
    PTRef lit3 = logic.mkNumLeq(x,y);
    // 0 <= x and 0 < x and x <= y
    PTRef fla = logic.mkAnd({lit1, lit2, lit3});
    ModelBuilder builder(logic);
    builder.addVarValue(x, logic.mkConst(FastRational(1)));
    builder.addVarValue(y, logic.mkConst(FastRational(2)));
    auto model = builder.build();
    PTRef res = mbp.project(fla, {x}, *model);
    std::cout << logic.printTerm(res) << std::endl;
//    EXPECT_EQ(res, logic.mkNumLt(zero, y));
    // Currently contains redundant conjuncts
    PTRef expected = logic.mkNumLt(zero, y);
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
    PTRef xp = logic.mkNumVar("xp");
    PTRef yp = logic.mkNumVar("yp");
    // y >= 256 and x <= 64
    PTRef part1 = logic.mkAnd(
        logic.mkNumLeq(x, logic.mkConst(FastRational(64))),
        logic.mkNumLeq(y, logic.mkConst(FastRational(256)))
    );
    // yp - y >= 0 and y - yp >= 0 and xp <= x + 256 and yp > x + 254
    PTRef diff = logic.mkNumMinus(y, yp);
    PTRef part2 = logic.mkAnd({
       logic.mkNumLeq(diff, zero),
       logic.mkNumLeq(zero, diff),
       logic.mkNumLeq(xp, logic.mkNumPlus(x, logic.mkConst(FastRational(256)))),
       logic.mkNumGt(yp, logic.mkNumPlus(x, logic.mkConst(FastRational(254))))
    });
    // yp != xp and yp <= xp
    PTRef part3 = logic.mkAnd(
        logic.mkNumLt(yp, xp),
//        logic.getTerm_true()
        logic.mkNumLeq(yp, xp)
    );
    PTRef fla = logic.mkAnd({part1, part2, part3});
    ModelBuilder builder(logic);
    builder.addVarValue(x, logic.mkConst(FastRational(3,2)));
    builder.addVarValue(y, logic.mkConst(FastRational(256)));
    builder.addVarValue(xp, logic.mkConst(FastRational(513,2)));
    builder.addVarValue(yp, logic.mkConst(FastRational(256)));
    auto model = builder.build();
    ASSERT_EQ(model->evaluate(fla), logic.getTerm_true());
    PTRef midpoint = mbp.project(fla, {xp,yp}, *model);
    std::cout << logic.printTerm(midpoint) << std::endl;
    ModelBuilder checkerBuilder(logic);
    checkerBuilder.addVarValue(x, zero);
    checkerBuilder.addVarValue(y, logic.mkConst(FastRational(256)));
    auto checker = checkerBuilder.build();
    ASSERT_NE(checker->evaluate(midpoint), logic.getTerm_true());
}

TEST_F(MBP_RealTest, test_strictNonStrict_1) {
    // x >= 0 and x > y and x <= 2 and x <= z; M: y -> 0, x -> 1, z -> 1
    // y should be picked for substitution
    // result is 0 <= y < 2 and y < z
    PTRef two = logic.mkConst(FastRational(2));
    PTRef lit1 = logic.mkNumLeq(zero, x);
    PTRef lit2 = logic.mkNumLt(y, x);
    PTRef lit3 = logic.mkNumLeq(x, two);
    PTRef lit4 = logic.mkNumLeq(x, z);
    PTRef fla = logic.mkAnd({lit1, lit2, lit3, lit4});
    ModelBuilder builder(logic);
    builder.addVarValue(x, one);
    builder.addVarValue(y, zero);
    builder.addVarValue(z, one);
    auto model = builder.build();
    ASSERT_EQ(model->evaluate(fla), logic.getTerm_true());
    PTRef res = mbp.project(fla, {x}, *model);
    std::cout << logic.printTerm(res) << std::endl;
    EXPECT_EQ(res, logic.mkAnd({logic.mkNumLeq(zero, y), logic.mkNumLt(y, two), logic.mkNumLt(y, z)}));
}

TEST_F(MBP_RealTest, test_strictNonStrict_2) {
    // x >= 0 and x > y and x <= 2 and x <=z; M: y -> 1/2, x -> 1, z -> 1
    // y should be picked for substitution
    // result is 0 <= y < 2 and y < z
    PTRef two = logic.mkConst(FastRational(2));
    PTRef half = logic.mkConst(FastRational(1,2));
    PTRef lit1 = logic.mkNumLeq(zero, x);
    PTRef lit2 = logic.mkNumLt(y, x);
    PTRef lit3 = logic.mkNumLeq(x, two);
    PTRef lit4 = logic.mkNumLeq(x, z);
    PTRef fla = logic.mkAnd({lit1, lit2, lit3, lit4});
    ModelBuilder builder(logic);
    builder.addVarValue(x, one);
    builder.addVarValue(y, half);
    builder.addVarValue(z, one);
    auto model = builder.build();
    ASSERT_EQ(model->evaluate(fla), logic.getTerm_true());
    PTRef res = mbp.project(fla, {x}, *model);
    std::cout << logic.printTerm(res) << std::endl;
    EXPECT_EQ(res, logic.mkAnd({logic.mkNumLeq(zero, y), logic.mkNumLt(y, two), logic.mkNumLt(y, z)}));
}

TEST_F(MBP_RealTest, test_strictNonStrict_3) {
    // x > 0 and x >= y and x <= 2 and x <= z; M: y -> 1/2, x -> 1, z -> 1
    // y should be picked for substitution
    // result is 0 < y <= 2 and y <= z
    PTRef two = logic.mkConst(FastRational(2));
    PTRef half = logic.mkConst(FastRational(1,2));
    PTRef lit1 = logic.mkNumLt(zero, x);
    PTRef lit2 = logic.mkNumLeq(y, x);
    PTRef lit3 = logic.mkNumLeq(x, two);
    PTRef lit4 = logic.mkNumLeq(x, z);
    PTRef fla = logic.mkAnd({lit1, lit2, lit3, lit4});
    ModelBuilder builder(logic);
    builder.addVarValue(x, one);
    builder.addVarValue(y, half);
    builder.addVarValue(z, one);
    auto model = builder.build();
    ASSERT_EQ(model->evaluate(fla), logic.getTerm_true());
    PTRef res = mbp.project(fla, {x}, *model);
    std::cout << logic.printTerm(res) << std::endl;
    EXPECT_EQ(res, logic.mkAnd({logic.mkNumLt(zero, y), logic.mkNumLeq(y, two), logic.mkNumLeq(y,z)}));
}

TEST_F(MBP_RealTest, test_strictNonStrict_4) {
    // x > 0 and x > y and x <= 2 and x <= z; M: y -> 1/2, x -> 1, z -> 1
    // y should be picked for substitution
    // result is 0 <= y < 2 and y < z
    PTRef two = logic.mkConst(FastRational(2));
    PTRef half = logic.mkConst(FastRational(1,2));
    PTRef lit1 = logic.mkNumLt(zero, x);
    PTRef lit2 = logic.mkNumLt(y, x);
    PTRef lit3 = logic.mkNumLeq(x, two);
    PTRef lit4 = logic.mkNumLeq(x, z);
    PTRef fla = logic.mkAnd({lit1, lit2, lit3, lit4});
    ModelBuilder builder(logic);
    builder.addVarValue(x, one);
    builder.addVarValue(y, half);
    builder.addVarValue(z, one);
    auto model = builder.build();
    ASSERT_EQ(model->evaluate(fla), logic.getTerm_true());
    PTRef res = mbp.project(fla, {x}, *model);
    std::cout << logic.printTerm(res) << std::endl;
    EXPECT_EQ(res, logic.mkAnd({logic.mkNumLeq(zero, y), logic.mkNumLt(y, two), logic.mkNumLt(y,z)}));
}

TEST_F(MBP_RealTest, test_avoidRedundantBounds) {
    // x <= y and y <= 0 and y <= 1 (last one is redundant)
    PTRef lit1 = logic.mkNumLeq(x,y);
    PTRef lit2 = logic.mkNumLeq(y, zero);
    PTRef lit3 = logic.mkNumLeq(y, one);
    PTRef fla = logic.mkAnd({lit1, lit2, lit3});
    ModelBuilder builder(logic);
    builder.addVarValue(x, logic.mkConst(FastRational(-1)));
    builder.addVarValue(y, zero);
    auto model = builder.build();
    PTRef res = mbp.project(fla, {y}, *model);
    std::cout << logic.printTerm(res) << std::endl;
    EXPECT_EQ(res, logic.mkNumLeq(x, zero)); // The redundant bound x <= 1 should not appear in the projection
}

TEST_F(MBP_RealTest, test_EqualityNotNormalized) {
    // x + y = x + 1
    PTRef lit = logic.mkEq(logic.mkNumPlus(x,y), logic.mkNumPlus(x, one));
    ModelBuilder builder(logic);
    builder.addVarValue(x, one);
    builder.addVarValue(y, one);
    auto model = builder.build();
    PTRef res = mbp.project(lit, {x}, *model);
    std::cout << logic.printTerm(res) << std::endl;
    // EXPECT_EQ(res, logic.mkEq(y,one));
     EXPECT_EQ(res, logic.mkEq(logic.mkNumPlus(y, logic.getTerm_NumMinusOne()), zero));
}

TEST_F(MBP_RealTest, test_singleUpperBound) {
    // y <= x and z <= x and 0 <= x and x <= 1
    // Using the single upper bound for elimination is strictly more general than using any of the lower bounds
    PTRef lit1 = logic.mkNumLeq(y,x);
    PTRef lit2 = logic.mkNumLeq(z, x);
    PTRef lit3 = logic.mkNumLeq(zero, x);
    PTRef lit4 = logic.mkNumLeq(x, one);
    PTRef fla = logic.mkAnd({lit1, lit2, lit3, lit4});
    ModelBuilder builder(logic);
    builder.addVarValue(x, zero);
    builder.addVarValue(y, zero);
    builder.addVarValue(z, zero);
    auto model = builder.build();
    PTRef res = mbp.project(fla, {x}, *model);
    std::cout << logic.printTerm(res) << std::endl;
    EXPECT_EQ(res, logic.mkAnd(logic.mkNumLeq(y, one), logic.mkNumLeq(z, one)));
}

TEST_F(MBP_RealTest, test_avoidRedundantBounds_2) {
    // y + z <= x and x <= 0 and y + z <= 1 and z = 0
    PTRef yz = logic.mkNumPlus(y,z);
    PTRef lit1 = logic.mkNumLeq(yz,x);
    PTRef lit2 = logic.mkNumLeq(x, zero);
    PTRef lit3 = logic.mkNumLeq(yz, one);
    PTRef lit4 = logic.mkEq(z, zero);
    PTRef fla = logic.mkAnd({lit1, lit2, lit3, lit4});
    ModelBuilder builder(logic);
    builder.addVarValue(x, zero);
    builder.addVarValue(y, zero);
    builder.addVarValue(z, zero);
    auto model = builder.build();
    PTRef res = mbp.project(fla, {x,z}, *model);
    std::cout << logic.printTerm(res) << std::endl;
    EXPECT_EQ(res, logic.mkAnd({logic.mkNumLeq(y, zero)}));
}

TEST_F(MBP_RealTest, test_avoidRedundantBounds_3) {
    // y  <= x and x <= 0 and y <= 1
    PTRef lit1 = logic.mkNumLeq(y,x);
    PTRef lit2 = logic.mkNumLeq(x, zero);
    PTRef lit3 = logic.mkNumLeq(y, one);
    PTRef fla = logic.mkAnd({lit1, lit2, lit3});
    ModelBuilder builder(logic);
    builder.addVarValue(x, zero);
    builder.addVarValue(y, zero);
    auto model = builder.build();
    PTRef res = mbp.project(fla, {x}, *model);
    std::cout << logic.printTerm(res) << std::endl;
    EXPECT_EQ(res, logic.mkAnd({logic.mkNumLeq(y, zero)}));
}

TEST_F(MBP_RealTest, test_hiddenEquality) {
    // z <= x and y  <= x and x <= y and  x <= 1
    PTRef lit3 = logic.mkNumLeq(z, x);
    PTRef lit1 = logic.mkNumLeq(y, x);
    PTRef lit2 = logic.mkNumLeq(x, y);
    PTRef lit4 = logic.mkNumLeq(x, one);
    PTRef fla = logic.mkAnd({lit1, lit2, lit3, lit4});
    ModelBuilder builder(logic);
    builder.addVarValue(x, zero);
    builder.addVarValue(y, zero);
    builder.addVarValue(z, zero);
    auto model = builder.build();
    PTRef res = mbp.project(fla, {x}, *model);
    std::cout << logic.printTerm(res) << std::endl;
    EXPECT_EQ(res, logic.mkAnd({logic.mkNumLeq(z, y), logic.mkNumLeq(y, one)}));
}


class MBP_IntTest : public ::testing::Test {
protected:
    LIALogic logic;
    PTRef x;
    PTRef y;
    PTRef z;
    PTRef a;
    PTRef b;
    PTRef c;
    PTRef zero;
    PTRef one;
    ModelBasedProjection mbp;
    MBP_IntTest() : mbp(logic) {
        x = logic.mkNumVar("x");
        y = logic.mkNumVar("y");
        z = logic.mkNumVar("z");
        a = logic.mkBoolVar("a");
        b = logic.mkBoolVar("b");
        c = logic.mkBoolVar("c");
        zero = logic.getTerm_NumZero();
        one = logic.getTerm_NumOne();
    }
};

TEST_F(MBP_IntTest, test_oneLower_oneUpper) {
    PTRef lit1 = logic.mkNumLeq(x,y);
    PTRef lit2 = logic.mkNumLeq(y,zero);
    PTRef fla = logic.mkAnd(lit1, lit2);
    ModelBuilder builder(logic);
    builder.addVarValue(x, logic.mkConst(FastRational(-1)));
    builder.addVarValue(y, zero);
    auto model = builder.build();
    PTRef res = mbp.project(fla, {y}, *model);
    EXPECT_EQ(res, logic.mkNumLeq(x, zero));
}

TEST_F(MBP_IntTest, test_oneLower_oneUpper_withCoefficients_1) {
    PTRef two = logic.mkConst(FastRational(2));
    PTRef y2 = logic.mkNumTimes(two, y);
    PTRef lit1 = logic.mkNumLeq(x,y2);
    PTRef lit2 = logic.mkNumLt(y2,zero);
    PTRef fla = logic.mkAnd(lit1, lit2);
    ModelBuilder builder(logic);
    builder.addVarValue(x, logic.mkConst(FastRational(-2)));
    builder.addVarValue(y, logic.getTerm_NumMinusOne());
    auto model = builder.build();
    PTRef res = mbp.project(fla, {y}, *model);
    std::cout << logic.pp(res) << std::endl;
    EXPECT_EQ(res, logic.mkNumLeq(x, logic.mkConst(FastRational(-2))));
}

TEST_F(MBP_IntTest, test_oneLower_oneUpper_withCoefficients_2) {
    PTRef two = logic.mkConst(FastRational(2));
    PTRef three = logic.mkConst(FastRational(3));
    PTRef y2 = logic.mkNumTimes(two, y);
    PTRef y3 = logic.mkNumTimes(three, y);
    PTRef lit1 = logic.mkNumLeq(zero,y3);
    PTRef lit2 = logic.mkNumLeq(y2,zero);
    PTRef fla = logic.mkAnd(lit1, lit2);
    ModelBuilder builder(logic);
    builder.addVarValue(y, zero);
    auto model = builder.build();
    PTRef res = mbp.project(fla, {y}, *model);
    std::cout << logic.pp(res) << std::endl;
    EXPECT_EQ(res, logic.getTerm_true());
}

TEST_F(MBP_IntTest, test_oneLower_oneUpper_withCoefficients_3) {
    PTRef two = logic.mkConst(FastRational(2));
    PTRef three = logic.mkConst(FastRational(3));
    PTRef y2 = logic.mkNumTimes(two, y);
    PTRef y3 = logic.mkNumTimes(three, y);
    PTRef lit1 = logic.mkNumLeq(x,y3);
    PTRef lit2 = logic.mkNumLeq(y2,z);
    PTRef fla = logic.mkAnd(lit1, lit2);
    ModelBuilder builder(logic);
    builder.addVarValue(x, three);
    builder.addVarValue(y, logic.getTerm_NumOne());
    builder.addVarValue(z, two);
    auto model = builder.build();
    PTRef res = mbp.project(fla, {y}, *model);
    std::cout << logic.pp(res) << std::endl;
    // MB: not 100% sure, but this should be the correct result
    EXPECT_EQ(res, logic.mkAnd(
        logic.mkNumLeq(logic.mkNumTimes(two,x), logic.mkNumTimes(three,z)),
        logic.mkEq(logic.mkIntMod(z, two), zero)
    ));
}

TEST_F(MBP_IntTest, test_ElimTwoVariables_withDivConstraints) {
    PTRef two = logic.mkConst(FastRational(2));
    PTRef three = logic.mkConst(FastRational(3));
    PTRef y2 = logic.mkNumTimes(two, y);
    PTRef y3 = logic.mkNumTimes(three, y);
    PTRef lit1 = logic.mkNumLeq(x,y3);
    PTRef lit2 = logic.mkNumLeq(y2,z);
    PTRef fla = logic.mkAnd(lit1, lit2);
    ModelBuilder builder(logic);
    builder.addVarValue(x, three);
    builder.addVarValue(y, logic.getTerm_NumOne());
    builder.addVarValue(z, two);
    auto model = builder.build();
    PTRef res = mbp.project(fla, {y,z}, *model);
    std::cout << logic.pp(res) << std::endl;
    EXPECT_EQ(res, logic.getTerm_true());
}

TEST_F(MBP_IntTest, test_Equality) {
    PTRef two = logic.mkConst(FastRational(2));
    PTRef lit1 = logic.mkNumLeq(x,y);
    PTRef lit2 = logic.mkNumLeq(y,z);
    PTRef lit3 = logic.mkEq(y, two);
    PTRef fla = logic.mkAnd({lit1, lit2, lit3});
    ModelBuilder builder(logic);
    builder.addVarValue(x, logic.mkConst(FastRational(-2)));
    builder.addVarValue(y, two);
    builder.addVarValue(z, two);
    auto model = builder.build();
    PTRef res = mbp.project(fla, {y}, *model);
    std::cout << logic.pp(res) << std::endl;
    EXPECT_EQ(res, logic.mkAnd(logic.mkNumLeq(x, two), logic.mkNumLeq(two, z)));
}

TEST_F(MBP_IntTest, test_EqualityWithCoefficients) {
    PTRef two = logic.mkConst(FastRational(2));
    PTRef three = logic.mkConst(FastRational(3));
    PTRef x2 = logic.mkNumTimes(x, two);
    PTRef x3 = logic.mkNumTimes(x, three);
    PTRef lit1 = logic.mkEq(x2,y);
    PTRef lit2 = logic.mkNumLeq(z,x3);
    PTRef fla = logic.mkAnd({lit1, lit2});
    ModelBuilder builder(logic);
    builder.addVarValue(x, zero);
    builder.addVarValue(y, zero);
    builder.addVarValue(z, logic.getTerm_NumMinusOne());
    auto model = builder.build();
    PTRef res = mbp.project(fla, {x}, *model);
    std::cout << logic.pp(res) << std::endl;
    EXPECT_EQ(res,logic.mkAnd(
        logic.mkNumLeq(logic.mkNumTimes(z, two), logic.mkNumTimes(three, y)),
        logic.mkEq(zero, logic.mkIntMod(y, two))
    ));
}

TEST_F(MBP_IntTest, test_EqualityAsConjunctionOfInequalities) {
    PTRef two = logic.mkConst(FastRational(2));
    PTRef three = logic.mkConst(FastRational(3));
    PTRef x2 = logic.mkNumTimes(x, two);
    PTRef x3 = logic.mkNumTimes(x, three);
    PTRef lit1 = logic.mkNumLeq(x2,y);
    PTRef lit2 = logic.mkNumLeq(y,x2);
    PTRef lit3 = logic.mkNumLeq(z,x3);
    PTRef fla = logic.mkAnd({lit1, lit2, lit3});
    ModelBuilder builder(logic);
    builder.addVarValue(x, zero);
    builder.addVarValue(y, zero);
    builder.addVarValue(z, logic.getTerm_NumMinusOne());
    auto model = builder.build();
    PTRef res = mbp.project(fla, {x}, *model);
    std::cout << logic.pp(res) << std::endl;
    EXPECT_EQ(res,logic.mkAnd(
        logic.mkNumLeq(logic.mkNumTimes(z, two), logic.mkNumTimes(three, y)),
        logic.mkEq(zero, logic.mkIntMod(y, two))
    ));
}

TEST_F(MBP_IntTest, test_AuxiliaryVarAndDisequality) {
    // Auxiliary variable is used because of divisibility constraint and its value is needed
    // in the model in order to, e.g., decide disequality.
    // Our current model silently returns a default value (0) if the variable is not known
    PTRef two = logic.mkConst(FastRational(2));
    PTRef three = logic.mkConst(FastRational(3));
    PTRef y2 = logic.mkNumTimes(two, y);
    PTRef lit1 = logic.mkEq(logic.mkIntMod(logic.mkNumMinus(x, one), two), zero);
    PTRef lit2 = logic.mkNot(logic.mkEq(logic.mkNumMinus(x,y2), zero));
    PTRef lit3 = logic.mkNumLeq(x, three);
    PTRef lit4 = logic.mkNumLeq(three, x);
    PTRef fla = logic.mkAnd({lit1, lit2, lit3, lit4});
    ModelBuilder builder(logic);
    builder.addVarValue(x, logic.mkConst(FastRational(3)));
    builder.addVarValue(y, one);
    auto model = builder.build();
    PTRef res = mbp.project(fla, {x}, *model);
    std::cout << logic.pp(res) << std::endl;
    // FIXME: Update LIA-MBP to the result here is "y <= 1"
    EXPECT_EQ(res, logic.mkAnd(logic.mkNumLeq(y, one), logic.mkNumLeq(one, y)));
}

TEST_F(MBP_IntTest, test_ResolvesToTrue) {
    PTRef five = logic.mkConst(FastRational(5));
    PTRef three = logic.mkConst(FastRational(3));
    PTRef y5 = logic.mkNumTimes(y, five);
    // x - 3 <= 5y <= x
    PTRef lit1 = logic.mkNumLeq(y5, x);
    PTRef lit2 = logic.mkNumLeq(logic.mkNumMinus(x, three), y5);
    PTRef fla = logic.mkAnd({lit1, lit2});
    ModelBuilder builder(logic);
    builder.addVarValue(x, logic.mkConst(FastRational(6)));
    builder.addVarValue(y, one);
    auto model = builder.build();
    PTRef res = mbp.project(fla, {y}, *model);
    std::cout << logic.pp(res) << std::endl;
    // Because of the model x -> 6, we get that 5 divides (x - 1)
    EXPECT_EQ(res, logic.mkEq(zero, logic.mkIntMod(logic.mkNumMinus(x, one), five)));
}

