/*
 * Copyright (c) 2021-2025, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include <TermUtils.h>
#include <gtest/gtest.h>
#include <ostream>
#include "QuantifierElimination.h"
#include "pterms/PTRef.h"
#include "utils/SmtSolver.h"

using namespace golem;

namespace {

bool implies(PTRef antecedent, PTRef consequent, Logic & logic) {
    SMTSolver solver(logic);
    solver.assertProp(antecedent);
    solver.assertProp(logic.mkNot(consequent));
    return solver.check() == SMTSolver::Answer::UNSAT;
}

bool isEquivalent(PTRef a, PTRef b, Logic & logic) {
    return implies(a, b, logic) and implies(b, a, logic);
}

} // namespace

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

// Eliminating x from 0 ≤ x ∧ x ≤ y should give y ≥ 0
TEST_F(QE_RealTest, test_LRA_eliminateSingleVar_SimpleBound) {
    PTRef fla = logic.mkAnd(logic.mkLeq(zero, x), logic.mkLeq(x, y));
    PTRef res = QuantifierElimination(logic).eliminate(fla, x);
    std::cout << logic.printTerm(res) << std::endl;
    EXPECT_EQ(res, logic.mkLeq(zero, y));
}

// Eliminating x from a SAT formula where no free vars remain
TEST_F(QE_RealTest, test_LRA_eliminateSingleVar_AllEliminated_SAT) {
    PTRef fla = logic.mkLeq(zero, x);
    PTRef res = QuantifierElimination(logic).eliminate(fla, x);
    EXPECT_EQ(res, logic.getTerm_true());

    PTRef res2 = QuantifierElimination(logic).keepOnly(fla, vec<PTRef>{});
    EXPECT_EQ(res2, res);
}

// Eliminating x from an UNSAT formula where no free vars remain
TEST_F(QE_RealTest, test_LRA_eliminateSingleVar_AllEliminated_UNSAT) {
    PTRef fla = logic.mkAnd(logic.mkLt(x, zero), logic.mkLeq(zero, x)); // UNSAT: x < 0 ∧ x ≥ 0
    PTRef res = QuantifierElimination(logic).eliminate(fla, x);
    EXPECT_EQ(res, logic.getTerm_false());

    PTRef res2 = QuantifierElimination(logic).keepOnly(fla, vec<PTRef>{});
    EXPECT_EQ(res2, res);
}

// Eliminating {x, y} from 0 ≤ x ∧ x ≤ y ∧ y ≤ z should give z ≥ 0 (vec overload)
TEST_F(QE_RealTest, test_LRA_eliminateMultipleVars) {
    PTRef fla = logic.mkAnd({logic.mkLeq(zero, x), logic.mkLeq(x, y), logic.mkLeq(y, z)});
    PTRef res = QuantifierElimination(logic).eliminate(fla, vec<PTRef>{x, y});
    std::cout << logic.printTerm(res) << std::endl;
    EXPECT_EQ(res, logic.mkLeq(zero, z));

    PTRef res2 = QuantifierElimination(logic).keepOnly(fla, vec<PTRef>{z});
    std::cout << logic.printTerm(res2) << std::endl;
    EXPECT_EQ(res2, res);
}

TEST_F(QE_RealTest, test_LRA_BoolAndReal_eliminateReal) {
    PTRef fla = logic.mkAnd(logic.mkOr(a, logic.mkGt(x, zero)), logic.mkLeq(x, zero));
    PTRef res = QuantifierElimination(logic).eliminate(fla, x);
    std::cout << logic.printTerm(res) << std::endl;
    EXPECT_TRUE(isEquivalent(res, a, logic));
}

TEST_F(QE_RealTest, test_LRA_keepOnly_BoolsWithRealWitness) {
    PTRef fla = logic.mkAnd(
        logic.mkOr(a, logic.mkGt(x, zero)),
        logic.mkOr(b, logic.mkLeq(x, zero)));
    PTRef res = QuantifierElimination(logic).keepOnly(fla, vec<PTRef>{a, b});
    std::cout << logic.printTerm(res) << std::endl;
    EXPECT_TRUE(isEquivalent(res, logic.mkOr(a, b), logic));
}

TEST_F(QE_RealTest, test_LRA_QEResult_defaultOptions_precise) {
    PTRef fla = logic.mkAnd(logic.mkLeq(zero, x), logic.mkLeq(x, y));
    PTRef precise = QuantifierElimination(logic).eliminate(fla, x);
    QEOptions options;
    options.compute_overapproximation = true;
    options.max_disjunctions_in_over = false;
    options.max_mbp_per_poly = false;
    QEResult result = QuantifierElimination(logic).eliminate(fla, vec<PTRef>{x}, options);
    EXPECT_TRUE(result.precise_under);
    EXPECT_TRUE(result.precise_over);
    EXPECT_TRUE(isEquivalent(result.under, precise, logic));
    EXPECT_TRUE(isEquivalent(result.over, precise, logic));
}

TEST_F(QE_RealTest, test_LRA_QEResult_underImpliesPrecise_maxDisjunctions) {
    PTRef case1 = logic.mkAnd({a, logic.mkLeq(zero, x), logic.mkLeq(x, y)});
    PTRef case2 = logic.mkAnd({logic.mkNot(a), logic.mkLeq(zero, x), logic.mkLeq(x, z)});
    PTRef fla = logic.mkOr(case1, case2);
    PTRef precise = QuantifierElimination(logic).eliminate(fla, x);
    QEOptions options;
    options.compute_overapproximation = true;
    options.max_disjunctions_in_over = 1;
    options.max_mbp_per_poly = false;
    QEResult result = QuantifierElimination(logic).eliminate(fla, vec<PTRef>{x}, options);
    std::cout << logic.pp(precise) << std::endl;
    std::cout << logic.pp(result.over) << std::endl;
    std::cout << logic.pp(result.under) << std::endl;
    // EXPECT_EQ(result.under, precise);
    EXPECT_TRUE(isEquivalent(result.under, precise, logic));
    EXPECT_TRUE(result.precise_under);
    EXPECT_TRUE(logic.isAnd(result.over) or result.over == logic.getTerm_true());
}

TEST_F(QE_RealTest, test_LRA_QEResult_preciseImpliesOver_maxDisjunctions) {
    PTRef case1 = logic.mkAnd({a, logic.mkLeq(zero, x), logic.mkLeq(x, y)});
    PTRef case2 = logic.mkAnd({logic.mkNot(a), logic.mkLeq(zero, x), logic.mkLeq(x, z)});
    PTRef fla = logic.mkOr(case1, case2);
    PTRef precise = QuantifierElimination(logic).eliminate(fla, x);
    QEOptions options;
    options.compute_overapproximation = true;
    options.max_disjunctions_in_over = 1;
    options.max_mbp_per_poly = false;
    QEResult result = QuantifierElimination(logic).eliminate(fla, vec<PTRef>{x}, options);
    std::cout << logic.pp(precise) << std::endl;
    std::cout << logic.pp(result.over) << std::endl;
    std::cout << logic.pp(result.under) << std::endl;
    EXPECT_TRUE(isEquivalent(result.under, precise, logic));
    EXPECT_TRUE(implies(precise, result.over, logic));
    // Check that result.over is a conjunction (i.e., at most 1 disjunction)
    EXPECT_TRUE(logic.isAnd(result.over) or result.over == logic.getTerm_true());
}

TEST_F(QE_RealTest, test_LRA_keepOnly_QEResult_defaultOptions) {
    PTRef fla = logic.mkAnd({logic.mkLeq(zero, x), logic.mkLeq(x, y), logic.mkLeq(y, z)});
    PTRef precise = QuantifierElimination(logic).keepOnly(fla, vec<PTRef>{z});
    QEOptions options;
    options.compute_overapproximation = true;
    QEResult result = QuantifierElimination(logic).keepOnly(fla, vec<PTRef>{z}, options);
    EXPECT_TRUE(result.precise_under);
    EXPECT_TRUE(result.precise_over);
    EXPECT_TRUE(isEquivalent(result.under, precise, logic));
    EXPECT_TRUE(isEquivalent(result.over, precise, logic));
}

TEST_F(QE_RealTest, test_LRA_disjunctive) {
    PTRef lbA1 = logic.mkGeq(y, logic.mkRealConst(-2));
    PTRef lbA2 = logic.mkGeq(y, logic.mkMinus(x, logic.mkRealConst(3)));
    PTRef lbA3 = logic.mkGeq(y, logic.mkMinus(logic.mkRealConst(-3), x));
    PTRef ubA1 = logic.mkLeq(y, logic.mkRealConst(2));
    PTRef ubA2 = logic.mkLeq(y, logic.mkPlus(x, logic.mkRealConst(3)));
    PTRef ubA3 = logic.mkLeq(y, logic.mkMinus(logic.mkRealConst(3), x));
    PTRef blockA = logic.mkAnd({lbA1, lbA2, lbA3, ubA1, ubA2, ubA3});
    PTRef lbB1 = logic.mkGeq(y, logic.mkMinus(x, logic.mkRealConst(6)));
    PTRef ubB1 = logic.mkLeq(y, logic.mkMinus(logic.mkRealConst(6), x));
    PTRef backB = logic.mkGeq(x, logic.mkRealConst(5));
    PTRef blockB = logic.mkAnd({lbB1, ubB1, backB});
    PTRef fla = logic.mkOr(blockA, blockB);

    PTRef precise = QuantifierElimination(logic).eliminate(fla, y);
    std::cout << "Precise result: " << logic.printTerm(precise) << std::endl;

    QEResult result;
    QEOptions option;

    option.compute_overapproximation = false;
    option.max_disjunctions_in_over = 0;
    option.max_mbp_per_poly = 0;
    result = QuantifierElimination(logic).eliminate(fla, y, option);
    std::cout << "With option: "
              << option.compute_overapproximation << " "
              << option.max_mbp_per_poly << " "
              << option.max_disjunctions_in_over << std::endl;
    std::cout << "Obtianed under: " << logic.printTerm(result.under) << std::endl;
    std::cout << "Obtianed over: " << logic.printTerm(result.over) << std::endl;
    EXPECT_EQ(result.under, precise);
    EXPECT_EQ(result.over, logic.getTerm_true());

    option.compute_overapproximation = true;
    option.max_disjunctions_in_over = 0;
    option.max_mbp_per_poly = 0;
    result = QuantifierElimination(logic).eliminate(fla, y, option);
    std::cout << "With option: "
              << option.compute_overapproximation << " "
              << option.max_mbp_per_poly << " "
              << option.max_disjunctions_in_over << std::endl;
    std::cout << "Obtianed under: " << logic.printTerm(result.under) << std::endl;
    std::cout << "Obtianed over: " << logic.printTerm(result.over) << std::endl;
    EXPECT_TRUE(isEquivalent(result.over, result.under, logic));
    EXPECT_TRUE(isEquivalent(result.over, precise, logic));
    EXPECT_TRUE(result.precise_over);
    EXPECT_TRUE(result.precise_under);

    option.compute_overapproximation = true;
    option.max_disjunctions_in_over = 1;
    option.max_mbp_per_poly = 0;
    result = QuantifierElimination(logic).eliminate(fla, y, option);
    std::cout << "With option: "
              << option.compute_overapproximation << " "
              << option.max_mbp_per_poly << " "
              << option.max_disjunctions_in_over << std::endl;
    std::cout << "Obtianed under: " << logic.printTerm(result.under) << std::endl;
    std::cout << "Obtianed over: " << logic.printTerm(result.over) << std::endl;
    EXPECT_TRUE(isEquivalent(result.under, precise, logic));
    EXPECT_TRUE(result.precise_under);
    EXPECT_FALSE(isEquivalent(result.over, precise, logic));
    EXPECT_FALSE(result.precise_over);
    EXPECT_TRUE(implies(result.under, result.over, logic));

    option.compute_overapproximation = true;
    option.max_disjunctions_in_over = 1;
    option.max_mbp_per_poly = 1;
    result = QuantifierElimination(logic).eliminate(fla, y, option);
    std::cout << "With option: "
              << option.compute_overapproximation << " "
              << option.max_mbp_per_poly << " "
              << option.max_disjunctions_in_over << std::endl;
    std::cout << "Obtianed under: " << logic.printTerm(result.under) << std::endl;
    std::cout << "Obtianed over: " << logic.printTerm(result.over) << std::endl;
    EXPECT_FALSE(isEquivalent(result.under, precise, logic));
    EXPECT_FALSE(result.precise_over);
    EXPECT_FALSE(isEquivalent(result.over, precise, logic));
    EXPECT_FALSE(result.precise_over);
    EXPECT_TRUE(implies(result.under, precise, logic));
    EXPECT_TRUE(implies(precise, result.over, logic));
}

class QE_IntTest : public ::testing::Test {
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
    PTRef two;
    PTRef three;
    QE_IntTest() {
        x = logic.mkIntVar("x");
        y = logic.mkIntVar("y");
        z = logic.mkIntVar("z");
        a = logic.mkBoolVar("a");
        b = logic.mkBoolVar("b");
        c = logic.mkBoolVar("c");
        zero = logic.getTerm_IntZero();
        one = logic.getTerm_IntOne();
        minusOne = logic.getTerm_IntMinusOne();
        two = logic.mkIntConst(2);
        three = logic.mkIntConst(3);
    }
};

// Eliminating y from 0 < y ∧ y <= z should give 1 <= z (integer Fourier-Motzkin)
TEST_F(QE_IntTest, test_LIA_eliminateSingleVar) {
    PTRef fla = logic.mkAnd(logic.mkLeq(one, y), logic.mkLeq(y, z));
    PTRef res = QuantifierElimination(logic).eliminate(fla, y);
    std::cout << logic.pp(res) << std::endl;
    EXPECT_EQ(res, logic.mkLeq(one, z));
}

// Eliminating all vars from a SAT formula
TEST_F(QE_IntTest, test_LIA_eliminateMultipleVars_AllEliminated_SAT) {
    PTRef fla = logic.mkAnd(logic.mkEq(x, one), logic.mkLeq(y, x));
    PTRef res = QuantifierElimination(logic).eliminate(fla, vec<PTRef>{x, y});
    EXPECT_EQ(res, logic.getTerm_true());

    PTRef res2 = QuantifierElimination(logic).keepOnly(fla, vec<PTRef>{});
    EXPECT_EQ(res2, logic.getTerm_true());
}

// Eliminating x from UNSAT formula (2 x >= 3 ∧ x < 2)
TEST_F(QE_IntTest, test_LIA_eliminateSingleVar_UNSAT) {
    PTRef fla = logic.mkAnd(logic.mkGeq(logic.mkTimes(two, x), three), logic.mkLt(x, two));
    PTRef res = QuantifierElimination(logic).eliminate(fla, x);
    EXPECT_EQ(res, logic.getTerm_false());

    PTRef res2 = QuantifierElimination(logic).keepOnly(fla, vec<PTRef>{});
    EXPECT_EQ(res2, logic.getTerm_false());
}

// keepOnly {a, b} from (a or x >= 0) and (b or x <= 0) --> a or b (integer version)
TEST_F(QE_IntTest, test_LIA_keepOnly_BoolsWithIntWitness) {
    PTRef fla = logic.mkAnd(
        logic.mkOr(a, logic.mkGt(x, zero)),
        logic.mkOr(b, logic.mkLeq(x, zero)));
    PTRef res = QuantifierElimination(logic).keepOnly(fla, vec<PTRef>{a, b});
    std::cout << logic.pp(res) << std::endl;
    EXPECT_EQ(res, logic.mkOr(a, b));

    QEResult result = QuantifierElimination(logic).keepOnly(fla, vec<PTRef>{a, b},
                                                            QEOptions(0, 0, true));
    std::cout << logic.pp(result.under) << std::endl;
    std::cout << logic.pp(result.over) << std::endl;
    EXPECT_TRUE(result.precise_under);
    EXPECT_TRUE(result.precise_over);
    EXPECT_EQ(result.under, res);
    EXPECT_EQ(result.over, res);

    result = QuantifierElimination(logic).keepOnly(fla, vec<PTRef>{a, b},
                                                   QEOptions(1, 0, true));
    std::cout << logic.pp(result.under) << std::endl;
    std::cout << logic.pp(result.over) << std::endl;
    EXPECT_TRUE(result.precise_under);
    EXPECT_TRUE(not result.precise_over);
    // EXPECT_EQ(result.under, res);
    EXPECT_TRUE(isEquivalent(result.under, res, logic));
    EXPECT_EQ(result.over, logic.getTerm_true());


}

// QEResult with max_disjunctions=1 (integer): under must imply precise
TEST_F(QE_IntTest, test_LIA_QEResult_underImpliesPrecise_maxDisjunctions) {
    PTRef case1 = logic.mkAnd({a, logic.mkLeq(zero, x), logic.mkLeq(x, y)});
    PTRef case2 = logic.mkAnd({logic.mkNot(a), logic.mkLeq(zero, x), logic.mkLeq(x, z)});
    PTRef fla = logic.mkOr(case1, case2);
    PTRef precise = QuantifierElimination(logic).eliminate(fla, x);
    QEResult result = QuantifierElimination(logic).eliminate(fla, vec<PTRef>{x}, QEOptions(1, 0, true));
    EXPECT_EQ(result.under, precise);
    EXPECT_TRUE(result.precise_under);
    EXPECT_FALSE(result.precise_over);
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
