/*
 * Copyright (c) 2021-2025, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef OPENSMT_QUANTIFIERELIMINATION_H
#define OPENSMT_QUANTIFIERELIMINATION_H

#include "osmt_terms.h"

namespace golem {


/*
Options for quantifier elimination technique.
- `compute_overapproximation` : if false, the original mbp algorithm is performed.
- `max_disjunctions_in_over`: limits the number of disjunctions in the overapproximation.
  It applies only when `compute_overapproximation` is true.
  If 0, no limit is applied. In particular, if 1, then the
  over-approximation will be a convex polyhedron.
- `max_mbp_per_poly`: limits the number of mbps per convex implicant.
  It applies only when `compute_overapproximation` is true.
  If 0, no limit is applied. When exceeded, the returned result is an underapproximaton,
  overapproximation is not precise.
 */
struct QEOptions {
    QEOptions() : max_disjunctions_in_over(0), max_mbp_per_poly(0), compute_overapproximation(false) {}
    QEOptions(short max_disjunctions_in_over, short max_mbp_per_poly, bool compute_overapproximation)
        : max_disjunctions_in_over(max_disjunctions_in_over), max_mbp_per_poly(max_mbp_per_poly), compute_overapproximation(compute_overapproximation) {}
    short max_disjunctions_in_over;
    short max_mbp_per_poly;
    bool compute_overapproximation;
};

/*
  Wrapper for the results produced by a Quantifier Elimination procedure.
  It is a pair of formulae `over` and `under`, each equipped with a
  Boolean flag `precise_over` and `precise_under`.
 */
struct QEResult {
    QEResult() : under(PTRef_Undef), over(PTRef_Undef), precise_under(false), precise_over(false) {}
    QEResult(PTRef under, PTRef over, bool precise_under, bool precise_over)
        : under(under), over(over), precise_under(precise_under), precise_over(precise_over) {}
    QEResult(const QEResult& other) = default;
    QEResult(QEResult&& other) = default;
    QEResult& operator=(const QEResult& other) = default;
    QEResult& operator=(QEResult&& other) = default;
    ~QEResult() = default;
    PTRef under;
    PTRef over;
    bool precise_under;
    bool precise_over;

};

/*
 * A utility for precise elimination of (existential) quantifiers from a formula.
 *
 * Given a formula F(x,y) we want to compute a formula G(x) such that G(x) \equiv \exist y F(x,y)
 */
class QuantifierElimination {
public:
    explicit QuantifierElimination(Logic & logic) : logic(logic) {}

    // Elimination of a single variable. Returns the precise QE result.
    PTRef eliminate(PTRef fla, PTRef var) {
        QEResult result = eliminate(fla, vec<PTRef>{var}, QEOptions());
        return result.under;
    }
    // Elimination of multiple variables. Returns the precise QE result.
    PTRef eliminate(PTRef fla, vec<PTRef> const & vars) {
        QEResult result = eliminate(fla, vars, QEOptions());
        return result.under;
    }
    // Keeps only the specified variables. Returns the precise QE result.
    PTRef keepOnly(PTRef fla, vec<PTRef> const & vars) {
        QEResult result = keepOnly(fla, vars, QEOptions());
        return result.under;
    }

    // Elimination of a single variable. Returns both under and over approximations in `result`.
    // Precision of under and over is set in `limits`.
    QEResult eliminate(PTRef fla, PTRef var, QEOptions limits) {
        return eliminate(fla, vec<PTRef>{var}, limits);
    }

    // Elimination of multiple variables. Returns both under and over approximations in `result`.
    // Precision of under and over is set in `limits`.
    QEResult eliminate(PTRef fla, vec<PTRef> const & vars, QEOptions limits);

    // Keeps only the specified variables. Returns both under and over approximations in `result`.
    // Precision of under and over is set in `limits`.
    QEResult keepOnly(PTRef fla, vec<PTRef> const & vars, QEOptions limits);

private:
    Logic & logic;
};
} // namespace golem

#endif // OPENSMT_QUANTIFIERELIMINATION_H
