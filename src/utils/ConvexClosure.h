#ifndef GOLEM_CONVEXCLOSURE_H
#define GOLEM_CONVEXCLOSURE_H

#include "osmt_terms.h"

namespace golem {

/**
 * Utility for computing a convex closure of a disjunction of formulas.
 *
 * Given formulas F_1(x), ..., F_n(x), the method over-approximates each F_i by
 * the polyhedron obtained from its arithmetic literals (in NNF, with strict
 * inequalities relaxed to non-strict ones) and returns the existential
 * quantifier elimination of the standard syntactic convex closure encoding.
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
