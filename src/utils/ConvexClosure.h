#ifndef GOLEM_CONVEXCLOSURE_H
#define GOLEM_CONVEXCLOSURE_H

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
    explicit ConvexClosure(Logic & logic) : logic(logic) {}

    PTRef getConvexClosure(vec<PTRef> const & formulas);

private:
    Logic & logic;
};

} // namespace golem

#endif // GOLEM_CONVEXCLOSURE_H
