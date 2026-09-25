/*
 * Copyright (c) 2026, Anna Becchi <anna.becchi@usi.ch>
 *
 * SPDX-License-Identifier: MIT
 */

#include "utils/ConvexClosure.h"

#include "utils/SmtSolver.h"

#include <gtest/gtest.h>

#include <cstddef>
#include <vector>

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

/*
 * Fixture for convex closure tests.
 *
 * Every test describes a handful of polyhedra whose convex hull is known by hand and checks that
 * the computed closure is that hull. The closure is an over-approximation by construction, so the
 * two directions are checked separately: `expectClosure` first verifies that each input polyhedron
 * is covered (soundness, which must hold unconditionally) and then that the closure is not weaker
 * than the expected hull (precision, which holds for these particular examples).
 */
class ConvexClosureTest : public ::testing::Test {
protected:
    ArithLogic logic;
    SRef sort;
    PTRef x, y, z;
    PTRef b, c;

    ConvexClosureTest(opensmt::Logic_t logicType, SRef (ArithLogic::*sortGetter)() const)
        : logic(logicType), sort((logic.*sortGetter)()) {
        x = logic.mkVar(sort, "x");
        y = logic.mkVar(sort, "y");
        z = logic.mkVar(sort, "z");
        b = logic.mkBoolVar("b");
        c = logic.mkBoolVar("c");
    }

    PTRef num(int value) { return logic.mkConst(sort, FastRational(value)); }
    PTRef leq(PTRef lhs, PTRef rhs) { return logic.mkLeq(lhs, rhs); }
    PTRef lt(PTRef lhs, PTRef rhs) { return logic.mkLt(lhs, rhs); }
    PTRef eq(PTRef lhs, PTRef rhs) { return logic.mkEq(lhs, rhs); }
    PTRef sum(std::vector<PTRef> const & args) { return logic.mkPlus(vec<PTRef>(args)); }
    PTRef scale(int factor, PTRef term) { return logic.mkTimes(num(factor), term); }
    PTRef all(std::vector<PTRef> const & args) { return logic.mkAnd(vec<PTRef>(args)); }
    PTRef any(std::vector<PTRef> const & args) { return logic.mkOr(vec<PTRef>(args)); }
    PTRef neg(PTRef arg) { return logic.mkNot(arg); }

    // The point (a, b) in the x/y plane, as a polyhedron.
    PTRef point(int a, int b) { return all({eq(x, num(a)), eq(y, num(b))}); }
    // The point (a, b, c) in x/y/z space, as a polyhedron.
    PTRef point(int a, int b, int c) { return all({eq(x, num(a)), eq(y, num(b)), eq(z, num(c))}); }
    // The box [xLo, xHi] x [yLo, yHi].
    PTRef box(int xLo, int xHi, int yLo, int yHi) {
        return all({leq(num(xLo), x), leq(x, num(xHi)), leq(num(yLo), y), leq(y, num(yHi))});
    }

    // Soundness: the closure must cover every input polyhedron. This has to hold whatever options
    // the closure was given.
    void expectCovers(PTRef closure, std::vector<PTRef> const & polyhedra) {
        for (PTRef polyhedron : polyhedra) {
            EXPECT_TRUE(implies(polyhedron, closure, logic))
                << "polyhedron " << logic.pp(polyhedron) << "\nis not covered by the closure "
                << logic.pp(closure);
        }
    }

    // `maxCubesPerFormula` is the budget for expanding a formula that mixes Boolean and arithmetic
    // content into cubes; 0 drops such a conjunct instead. The tests state the budget explicitly,
    // so that they keep describing one behaviour each if the library default moves.
    void expectClosure(std::vector<PTRef> const & polyhedra, PTRef expectedHull,
                       std::size_t maxCubesPerFormula = 0) {
        PTRef closure = ConvexClosure(logic, ConvexClosure::defaultOptions(), maxCubesPerFormula)
                            .getConvexClosure(vec<PTRef>(polyhedra));
        expectCovers(closure, polyhedra);
        EXPECT_TRUE(isEquivalent(closure, expectedHull, logic))
            << "expected " << logic.pp(expectedHull) << "\nbut got  " << logic.pp(closure);
    }
};

class ConvexClosure_RealTest : public ConvexClosureTest {
protected:
    ConvexClosure_RealTest() : ConvexClosureTest(opensmt::Logic_t::QF_LRA, &ArithLogic::getSort_real) {}
};

class ConvexClosure_IntTest : public ConvexClosureTest {
protected:
    ConvexClosure_IntTest() : ConvexClosureTest(opensmt::Logic_t::QF_LIA, &ArithLogic::getSort_int) {}
};

/* ------------------------------------------------------------------ reals */

// Nested half-planes: the widest one already contains the others.
TEST_F(ConvexClosure_RealTest, test_ThreeNestedHalfPlanes) {
    expectClosure({leq(x, num(1)), leq(x, num(3)), leq(x, num(5))}, leq(x, num(5)));
}

// Three disjoint unit boxes along the x axis; the hull fills the gaps between them.
TEST_F(ConvexClosure_RealTest, test_ThreeBoxesInAStrip) {
    expectClosure({box(0, 1, 0, 1), box(2, 3, 0, 1), box(4, 5, 0, 1)}, box(0, 5, 0, 1));
}

// Three points spanning a triangle.
TEST_F(ConvexClosure_RealTest, test_ThreePointsSpanATriangle) {
    expectClosure({point(0, 0), point(4, 0), point(0, 4)},
                  all({leq(num(0), x), leq(num(0), y), leq(sum({x, y}), num(4))}));
}

// Four points spanning a square.
TEST_F(ConvexClosure_RealTest, test_FourPointsSpanASquare) {
    expectClosure({point(0, 0), point(4, 0), point(0, 4), point(4, 4)}, box(0, 4, 0, 4));
}

// Three downward-closed cones. The hull is unbounded from below and has two slanted facets, so
// this is the first example whose hull is not just a bounding box of the inputs.
TEST_F(ConvexClosure_RealTest, test_ThreeDownwardCones) {
    expectClosure({all({leq(x, num(0)), leq(y, num(6))}),
                   all({leq(x, num(6)), leq(y, num(0))}),
                   all({leq(x, num(5)), leq(y, num(5))})},
                  all({leq(x, num(6)), leq(y, num(6)), leq(sum({x, scale(5, y)}), num(30)),
                       leq(sum({scale(5, x), y}), num(30))}));
}

// Five collinear points. The hull is the segment between the extreme ones, so the closure has to
// keep the equality relating x and y exactly.
TEST_F(ConvexClosure_RealTest, test_FiveCollinearPoints) {
    std::vector<PTRef> polyhedra;
    for (int k = 0; k <= 4; ++k) { polyhedra.push_back(point(k, 2 * k)); }
    expectClosure(polyhedra, all({eq(y, scale(2, x)), leq(num(0), x), leq(x, num(4))}));
}

// Five horizontal segments, each shifted one step right of the previous one: the hull is the
// parallelogram they sweep.
TEST_F(ConvexClosure_RealTest, test_FiveShiftedSegments) {
    std::vector<PTRef> polyhedra;
    for (int k = 0; k <= 4; ++k) {
        polyhedra.push_back(all({eq(y, num(k)), leq(num(k), x), leq(x, num(k + 2))}));
    }
    expectClosure(polyhedra, all({leq(num(0), y), leq(y, num(4)), leq(y, x), leq(x, sum({y, num(2)}))}));
}

// Four points in three dimensions spanning a tetrahedron.
TEST_F(ConvexClosure_RealTest, test_FourPointsSpanATetrahedron) {
    expectClosure({point(0, 0, 0), point(4, 0, 0), point(0, 4, 0), point(0, 0, 4)},
                  all({leq(num(0), x), leq(num(0), y), leq(num(0), z), leq(sum({x, y, z}), num(4))}));
}

// The shape that stalled Spacer on tte_synchro: the negation of a lemma `x = 0 \/ y = 1` whose
// equalities are written as two inequalities. Both conjuncts are disequalities, nothing convex is
// left of that input, and the closure is unconstrained.
TEST_F(ConvexClosure_RealTest, test_NegatedLemmaOfEqualitiesIsUnconstrained) {
    PTRef lemma = any({all({leq(num(0), x), leq(num(0), scale(-1, x))}),
                       all({leq(num(1), y), leq(num(-1), scale(-1, y))})});
    expectClosure({neg(lemma), point(3, 3)}, logic.getTerm_true(), /* maxCubesPerFormula */ 8);
}

/* --------------------------------------------------------------- integers */

// Three disjoint intervals.
TEST_F(ConvexClosure_IntTest, test_ThreeIntervals) {
    expectClosure({all({leq(num(0), x), leq(x, num(1))}),
                   all({leq(num(4), x), leq(x, num(5))}),
                   all({leq(num(8), x), leq(x, num(9))})},
                  all({leq(num(0), x), leq(x, num(9))}));
}

// Example 1 of "Global Guidance for Local Generalization in Model Checking" (CAV'20), whose
// convex closure in LIA without divisibility constraints is 2 <= x <= 8 and y <= x + 1.
TEST_F(ConvexClosure_IntTest, test_PaperExample) {
    expectClosure({all({eq(x, num(2)), leq(y, num(3))}),
                   all({eq(x, num(4)), leq(y, num(5))}),
                   all({eq(x, num(8)), leq(y, num(9))})},
                  all({leq(num(2), x), leq(x, num(8)), leq(y, sum({x, num(1)}))}));
}

// Three points spanning a triangle.
TEST_F(ConvexClosure_IntTest, test_ThreePointsSpanATriangle) {
    expectClosure({point(0, 0), point(4, 0), point(0, 4)},
                  all({leq(num(0), x), leq(num(0), y), leq(sum({x, y}), num(4))}));
}

// Three collinear points on a line of slope 1/2. The hull needs the equality x = 2y; a naive
// translation back to integers would produce the fractional y = x/2 instead.
TEST_F(ConvexClosure_IntTest, test_ThreeCollinearPointsOnAFractionalSlope) {
    expectClosure({point(0, 0), point(2, 1), point(4, 2)},
                  all({eq(x, scale(2, y)), leq(num(0), x), leq(x, num(4))}));
}

// Five collinear points on a line of slope 1/3.
TEST_F(ConvexClosure_IntTest, test_FiveCollinearPoints) {
    std::vector<PTRef> polyhedra;
    for (int k = 0; k <= 4; ++k) { polyhedra.push_back(point(3 * k, k)); }
    expectClosure(polyhedra, all({eq(x, scale(3, y)), leq(num(0), y), leq(y, num(4))}));
}

// Four boxes spread along a strip.
TEST_F(ConvexClosure_IntTest, test_FourBoxesInAStrip) {
    std::vector<PTRef> polyhedra;
    for (int k : {0, 3, 6, 9}) { polyhedra.push_back(box(k, k + 1, 0, 2)); }
    expectClosure(polyhedra, box(0, 10, 0, 2));
}

// Three shifted quadrants; the hull gains the slanted facet x + y <= 0.
TEST_F(ConvexClosure_IntTest, test_ThreeShiftedQuadrants) {
    expectClosure({all({leq(x, num(0)), leq(y, num(0))}),
                   all({leq(x, num(2)), leq(y, num(-2))}),
                   all({leq(x, num(-2)), leq(y, num(2))})},
                  all({leq(x, num(2)), leq(y, num(2)), leq(sum({x, y}), num(0))}));
}

// The same quadrants restricted by a congruence, as integer MBP produces. A relation over (mod t k)
// is not a linear constraint: it is dropped from its cube, which only enlarges the cube, so the
// closure is the hull of the plain quadrants instead of an exception.
TEST_F(ConvexClosure_IntTest, test_ModuloConjunctIsDropped) {
    PTRef divisible = eq(logic.mkMod(logic.mkMinus(x, y), num(4)), num(0));
    expectClosure({all({leq(x, num(0)), leq(y, num(0)), divisible}),
                   all({leq(x, num(2)), leq(y, num(-2)), divisible}),
                   all({leq(x, num(-2)), leq(y, num(2)), divisible})},
                  all({leq(x, num(2)), leq(y, num(2)), leq(sum({x, y}), num(0))}));
}

// Over the integers a strict bound is tightened rather than relaxed: x < 10 is x <= 9, and
// not (-4 <= x) is x <= -5. Relaxing the strict bounds instead would yield x <= 10.
TEST_F(ConvexClosure_IntTest, test_StrictInequalitiesAreTightened) {
    expectClosure({lt(x, num(4)), lt(x, num(10)), logic.mkNot(leq(num(-4), x))}, leq(x, num(9)));
}

// 2x = 3 has no integer solution, so that polyhedron contributes nothing to the hull. Were it
// kept, its recession cone would widen the closure.
TEST_F(ConvexClosure_IntTest, test_EmptyPolyhedronIsIgnored) {
    expectClosure({point(0, 0), all({eq(scale(2, x), num(3)), eq(y, num(100))}), point(4, 0)},
                  all({eq(y, num(0)), leq(num(0), x), leq(x, num(4))}));
}

// Four points in three dimensions spanning a tetrahedron.
TEST_F(ConvexClosure_IntTest, test_FourPointsSpanATetrahedron) {
    expectClosure({point(0, 0, 0), point(4, 0, 0), point(0, 4, 0), point(0, 0, 4)},
                  all({leq(num(0), x), leq(num(0), y), leq(num(0), z), leq(sum({x, y, z}), num(4))}));
}

// If every polyhedron is empty, so is their union.
TEST_F(ConvexClosure_IntTest, test_AllPolyhedraEmpty) {
    vec<PTRef> polyhedra;
    polyhedra.push(all({leq(num(1), x), leq(x, num(0))}));
    polyhedra.push(eq(scale(2, x), num(3)));
    EXPECT_EQ(ConvexClosure(logic).getConvexClosure(polyhedra), logic.getTerm_false());
}

// A polyhedron with no arithmetic constraint at all covers the whole space, and with it the hull.
TEST_F(ConvexClosure_IntTest, test_UnconstrainedPolyhedron) {
    vec<PTRef> polyhedra;
    polyhedra.push(point(0, 0));
    polyhedra.push(logic.mkBoolVar("b"));
    EXPECT_EQ(ConvexClosure(logic).getConvexClosure(polyhedra), logic.getTerm_true());
}


/* --------------------------------------------------------------- booleans */

// A literal every input agrees on is not part of the polyhedra, but it holds in their union, so it
// comes back conjoined to the hull.
TEST_F(ConvexClosure_IntTest, test_SharedBooleanLiteralIsKept) {
    expectClosure({all({b, eq(x, num(0))}), all({b, eq(x, num(4))})},
                  all({b, leq(num(0), x), leq(x, num(4))}));
}

// Polarity is part of the match: `~b` is shared here, `b` is not.
TEST_F(ConvexClosure_IntTest, test_SharedNegatedBooleanLiteralIsKept) {
    expectClosure({all({neg(b), eq(x, num(0))}), all({neg(b), eq(x, num(4))})},
                  all({neg(b), leq(num(0), x), leq(x, num(4))}));
}

// `c` is split between the inputs, so nothing can be said about it; `b` still survives.
TEST_F(ConvexClosure_IntTest, test_SplitBooleanLiteralIsDropped) {
    expectClosure({all({b, c, eq(x, num(0))}), all({b, neg(c), eq(x, num(4))})},
                  all({b, leq(num(0), x), leq(x, num(4))}));
}

// A Boolean equality is not a literal: NNF turns `(= b c)` into `(or ~b c) /\ (or ~c b)`. Both
// clauses constrain no arithmetic variable, so both are shared and the equality comes back whole.
TEST_F(ConvexClosure_IntTest, test_SharedBooleanEqualityIsKept) {
    PTRef equivalence = logic.mkEq(b, c);
    expectClosure({all({equivalence, eq(x, num(0))}), all({equivalence, eq(x, num(4))})},
                  all({equivalence, leq(num(0), x), leq(x, num(4))}));
}

// With no arithmetic literal anywhere the hull is the whole space, but the shared Boolean part is
// still a constraint worth reporting.
TEST_F(ConvexClosure_IntTest, test_PurelyBooleanInputsKeepTheSharedPart) {
    expectClosure({all({b, c}), all({b, neg(c)})}, b);
}

// An input that constrains no arithmetic variable makes the arithmetic part of the closure
// unconstrained, and only the Boolean part is left.
TEST_F(ConvexClosure_IntTest, test_UnconstrainedInputKeepsTheSharedPart) {
    expectClosure({all({b, eq(x, num(0))}), b}, b);
}

// `(b \/ c) /\ ~b /\ ~c` is unsatisfiable, so that input describes no state at all: it must
// neither widen the hull to x = 100 nor empty the shared Boolean part.
TEST_F(ConvexClosure_IntTest, test_BooleanContradictionDropsTheInput) {
    expectClosure({all({b, eq(x, num(0))}), all({b, eq(x, num(4))}),
                   all({any({b, c}), neg(b), neg(c), eq(x, num(100))})},
                  all({b, leq(num(0), x), leq(x, num(4))}));
}

// Without a budget a conjunct mixing the two theories is dropped: the guard is lost, and so is the
// `y` it guards.
TEST_F(ConvexClosure_IntTest, test_MixedConjunctIsDroppedWithoutABudget) {
    PTRef guarded = any({neg(b), eq(y, num(2))});
    expectClosure({all({guarded, eq(x, num(0))}), all({guarded, eq(x, num(4))})},
                  all({leq(num(0), x), leq(x, num(4))}));
}

// A disjunctive input has a single mixed top-level conjunct, so without a budget it is dropped
// whole and leaves the closure unconstrained.
TEST_F(ConvexClosure_IntTest, test_DisjunctiveInputIsUnconstrainedWithoutABudget) {
    PTRef branches = any({point(0, 0), point(1, 1)});
    expectClosure({branches, point(4, 4)}, logic.getTerm_true());
}

// With a budget for two cubes the branches become inputs of their own and the hull is exact.
TEST_F(ConvexClosure_IntTest, test_DisjunctiveInputIsExpandedWithABudget) {
    PTRef branches = any({point(0, 0), point(1, 1)});
    expectClosure({branches, point(4, 4)}, all({eq(x, y), leq(num(0), x), leq(x, num(4))}),
                  /* maxCubesPerFormula */ 2);
}

// The budget is checked before the conversion runs, and a formula over it is processed as it would
// be at 0.
TEST_F(ConvexClosure_IntTest, test_BudgetTooSmallFallsBackToDropping) {
    PTRef branches = any({point(0, 0), point(1, 1)});
    expectClosure({branches, point(4, 4)}, logic.getTerm_true(), /* maxCubesPerFormula */ 1);
}

// The default budget expands, so a caller that asks for nothing in particular gets the case split.
TEST_F(ConvexClosure_IntTest, test_DefaultBudgetExpands) {
    std::vector<PTRef> polyhedra = {any({point(0, 0), point(1, 1)}), point(4, 4)};
    PTRef closure = ConvexClosure(logic).getConvexClosure(vec<PTRef>(polyhedra));
    expectCovers(closure, polyhedra);
    EXPECT_TRUE(isEquivalent(closure, all({eq(x, y), leq(num(0), x), leq(x, num(4))}), logic))
        << "got " << logic.pp(closure);
}

// `z != 0` in the shape interpolants give it: the negation of `0 <= z /\ 0 <= -z`, which NNF turns
// into a two-literal clause. It is dropped like a disequality instead of counting as a mixed
// conjunct, so the branches still fit a budget of two cubes and the hull stays exact.
TEST_F(ConvexClosure_IntTest, test_DisequalityClauseDoesNotCountAgainstTheBudget) {
    PTRef zNotZero = neg(all({leq(num(0), z), leq(num(0), scale(-1, z))}));
    PTRef branches = any({point(0, 0), point(1, 1)});
    expectClosure({all({branches, zNotZero}), point(4, 4)},
                  all({eq(x, y), leq(num(0), x), leq(x, num(4))}), /* maxCubesPerFormula */ 2);
}

// Two inequalities that are not complementary, `z < 0 \/ z > 1`, are not a disequality: the clause
// stays a mixed conjunct, the formula needs four cubes, over the budget, and falls back to dropping.
TEST_F(ConvexClosure_IntTest, test_NonComplementaryClauseStillCountsAgainstTheBudget) {
    PTRef gap = any({lt(z, num(0)), lt(num(1), z)});
    PTRef branches = any({point(0, 0), point(1, 1)});
    expectClosure({all({branches, gap}), point(4, 4)}, logic.getTerm_true(), /* maxCubesPerFormula */ 2);
}

/* ---------------------------------------------------------------- options */

// The closure is a convex over-approximation by definition, so the two options that say so are
// not up for negotiation.
TEST_F(ConvexClosure_IntTest, test_RejectsOptionsWithoutOverapproximation) {
    QEOptions options = ConvexClosure::defaultOptions();
    options.compute_overapproximation = false;
    EXPECT_THROW(ConvexClosure(logic, options), std::invalid_argument);
}

TEST_F(ConvexClosure_IntTest, test_RejectsOptionsWithMultipleDisjunctions) {
    QEOptions options = ConvexClosure::defaultOptions();
    options.max_disjunctions_in_over = 2;
    EXPECT_THROW(ConvexClosure(logic, options), std::invalid_argument);
    options.max_disjunctions_in_over = 0; // 0 means "no limit", which is not a single polyhedron
    EXPECT_THROW(ConvexClosure(logic, options), std::invalid_argument);
}

// The projection budget is the one option a caller may pick. A tight budget may cost precision but
// must never cost soundness.
TEST_F(ConvexClosure_IntTest, test_AcceptsCustomProjectionBudget) {
    std::vector<PTRef> polyhedra = {point(0, 0), point(4, 0), point(0, 4)};
    QEOptions options = ConvexClosure::defaultOptions();
    options.max_mbp_per_poly = 1;
    PTRef closure = ConvexClosure(logic, options).getConvexClosure(vec<PTRef>(polyhedra));
    expectCovers(closure, polyhedra);
}

// The default budget is unlimited, which is what lets the examples above reach the exact hull.
TEST_F(ConvexClosure_IntTest, test_DefaultOptions) {
    QEOptions options = ConvexClosure::defaultOptions();
    EXPECT_TRUE(options.compute_overapproximation);
    EXPECT_EQ(options.max_disjunctions_in_over, 1);
    EXPECT_EQ(options.max_mbp_per_poly, 0);
}
