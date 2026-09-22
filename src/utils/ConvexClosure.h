#ifndef GOLEM_CONVEXCLOSURE_H
#define GOLEM_CONVEXCLOSURE_H

#include "QuantifierElimination.h"
#include "osmt_terms.h"

#include <cstddef>

namespace golem {

/**
 * Utility for computing a convex closure of a disjunction of formulas.
 *
 * Given formulas F_1(x), ..., F_n(x), the method over-approximates each F_i by
 * the polyhedron obtained from its arithmetic literals (in NNF) and returns the
 * existential quantifier elimination of the standard syntactic convex closure
 * encoding.
 *
 * Boolean content is factorized out rather than dropped: a top-level conjunct of F_i
 * that mentions no arithmetic variable (a literal `b` / `~b`, but also a clause such as
 * `(or ~b1 b2)`, which is what NNF turns `(= b1 b2)` into) is collected separately, and
 * the conjuncts shared by *every* satisfiable F_i are conjoined to the arithmetic closure
 * at the end. This is sound because a shared conjunct holds in each F_i, hence in their
 * union. Conjuncts that are shared by only some F_i are dropped, and so are conjuncts that
 * mix Boolean and arithmetic content (see `maxCubesPerFormula`).
 *
 * Both rational and integer variables are supported. The multipliers of the
 * encoding are always rational, so for integer variables the encoding is built
 * over a private LRA logic on shadow variables and the result is translated back
 * into integer atoms. Integer literals are tightened before the closure (strict
 * inequalities are decremented and every atom is divided by the gcd of its
 * coefficients), and the atoms of the result are tightened the same way.
 */
class ConvexClosure {
public:
    /**
     * Options for the quantifier elimination that closes the encoding.
     *
     * Two of the three fields are fixed by what a convex closure is: `compute_overapproximation`
     * must be set, and `max_disjunctions_in_over` must be 1 so that the result is a single convex
     * polyhedron rather than a disjunction. Passing anything else is rejected. `max_mbp_per_poly`
     * is free; 0 (the default) means no limit.
     *
     * The encoding handed to quantifier elimination is a cube, which is its own only implicant, so
     * a disjunction budget of 1 never restricts the search. With `max_mbp_per_poly` left at 0 the
     * elimination is therefore exact and `QEResult::precise_over` holds.
     */
    static QEOptions defaultOptions() {
        return QEOptions(/* max_disjunctions_in_over */ 1, /* max_mbp_per_poly */ 0,
                         /* compute_overapproximation */ true);
    }

    /**
     * `maxCubesPerFormula` controls what happens to a conjunct that mixes Boolean and arithmetic
     * content, such as `(or ~g (= y 2))`. A formula containing one is first converted to DNF and
     * each of its cubes becomes an input polyhedron of its own, provided the cube count stays
     * within the budget; past the budget, and at 0, such a conjunct is simply dropped instead,
     * which is sound but loses the case split. The cube count is bounded *before* the conversion
     * runs, so the budget caps the work, not just the result.
     */
    explicit ConvexClosure(Logic & logic, QEOptions options = defaultOptions(),
                           std::size_t maxCubesPerFormula = 8);

    PTRef getConvexClosure(vec<PTRef> const & formulas);

private:
    Logic & logic;
    QEOptions options;
    std::size_t maxCubesPerFormula;
};

} // namespace golem

#endif // GOLEM_CONVEXCLOSURE_H
