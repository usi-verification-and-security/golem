//
// Created by Martin Blicha on 12.06.21.
//

#include <gtest/gtest.h>
#include "QuantifierElimination.h"

class QE_RealTest : public ::testing::Test {
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
    QE_RealTest() {
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

TEST_F(QE_RealTest, test_singleVar_Equality) {
    PTRef fla = logic.mkEq(y, x);
    QuantifierElimination qe(logic);
    PTRef res = qe.eliminate(fla, x);
    EXPECT_EQ(res, logic.getTerm_true());
    fla = logic.mkAnd(fla, logic.mkEq(x, zero));
    res = qe.eliminate(fla, x);
    std::cout << logic.printTerm(res) << std::endl;
    EXPECT_TRUE(res == logic.mkEq(y, zero) or res == logic.mkAnd(logic.mkNumLeq(y, zero), logic.mkNumGeq(y, zero)));
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
    PTRef lit1 = logic.mkNumLeq(zero, x);
    PTRef lit2 = logic.mkNumLeq(x, logic.mkNumMinus(y, one));
    PTRef lit3 = logic.mkNumGeq(x, logic.mkNumMinus(y, one));
    PTRef lit4 = logic.mkNot(logic.mkEq(y, one));
    PTRef fla = logic.mkAnd({lit1, lit2, lit3, lit4});
    PTRef res = QuantifierElimination(logic).eliminate(fla, y);
    std::cout << logic.printTerm(res) << std::endl;
//    EXPECT_EQ(res, logic.mkNumLt(zero, x));
    // The result is equivalent to x > 0, but we are missing arithmetic simplifications to get it to that form
    // Current result is x >= 0 and x > 0 which is equivalent to x > 0;
    EXPECT_EQ(res, logic.mkAnd(logic.mkNumLt(zero, x), logic.mkNumLeq(zero, x)));
}
