#ifndef GOLEM_CONVEXCLOSURE_H
#define GOLEM_CONVEXCLOSURE_H

#include "QuantifierElimination.h"
#include "osmt_terms.h"

namespace golem {

/**
 * Utility for computing a convex closure of a disjunction of formulas.
 *
 * Given formulas F_1(x), ..., F_n(x), the method over-approximates each F_i by
 * the polyhedron obtained from its arithmetic literals (in NNF) and returns the
 * existential quantifier elimination of the standard syntactic convex closure
 * encoding.
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

    explicit ConvexClosure(Logic & logic, QEOptions options = defaultOptions());

    PTRef getConvexClosure(vec<PTRef> const & formulas);

private:
    Logic & logic;
    QEOptions options;
};

} // namespace golem

#endif // GOLEM_CONVEXCLOSURE_H
