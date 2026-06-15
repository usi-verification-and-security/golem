/*
 * Copyright (c) 2021-2025, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "QuantifierElimination.h"

#include "ModelBasedProjection.h"
#include "TermUtils.h"
#include "pterms/PTRef.h"
#include "utils/SmtSolver.h"

#define DEBUG_CHECK_BMBP 0

namespace {
using namespace golem;
QEResult eliminate_aux(Logic & logic, PTRef fla, vec<PTRef> const & vars, QEOptions limits) {
    vec<PTRef> under_projections;
    vec<PTRef> over_projections;

    fla = TermUtils(logic).toNNF(fla);

    SMTSolver outer_solver(logic, SMTSolver::WitnessProduction::ONLY_MODEL);
    SMTSolver inner_solver(logic, SMTSolver::WitnessProduction::ONLY_MODEL);

    PTRef unexplored = fla;

    QEResult result;
    result.precise_under = true;
    result.precise_over = limits.compute_overapproximation;

    // for logging purposes only
    // auto max_inner_iter = 0;

    outer_solver.assertProp(fla);
    auto outer_iter = 0;
    while (true) {
        auto outer_res = outer_solver.check();
        if (outer_res == SMTSolver::Answer::UNSAT) { break; }
        if (outer_res != SMTSolver::Answer::SAT) {
            throw std::logic_error("Error in solver during quantifier elimination");
        }
        ++outer_iter;
        auto model = outer_solver.getModel();
        ModelBasedProjection mbp(logic);

        PTRef implicant;
        if (not limits.compute_overapproximation) {
            // This is the original algorithm collecting mbps
            PTRef under_projection = mbp.project(fla, vars, *model);
            under_projections.push(under_projection);
            outer_solver.assertProp(logic.mkNot(under_projection));
            continue;
        }

        // Here, we are computing both under and over approximations.

        if (limits.max_disjunctions_in_over > 0 and limits.max_disjunctions_in_over <= outer_iter) {
            // let's wrap everything that remains in a single convex-overapproximation
            result.precise_over = false;
            implicant = unexplored;
            // std::cerr << "OUT: exceeded limit " << outer_iter << "..." << std::endl;
            // std::cerr << "   remaining part: " << logic.printTerm(implicant) << std::endl;
        } else {
            implicant = mbp.getModelBasedImplicant(fla, vars, *model);
            // std::cerr << "OUT: Getting implicant " << outer_iter << "..." << std::endl;
            // std::cerr << "   implicant: " << logic.printTerm(implicant) << std::endl;
        }

        // Here, perform QE only on the implicant
        auto inner_iter = 0;
        inner_solver.push();
        inner_solver.assertProp(implicant);
        vec<PTRef> implicant_over_conjuncts;
        vec<PTRef> implicant_under_disjuncts;
        while (true) {
            auto inner_res = inner_solver.check();
            if (inner_res == SMTSolver::Answer::UNSAT) { break; }
            if (inner_res != SMTSolver::Answer::SAT) {
                throw std::logic_error("Error in solver during quantifier elimination");
            }
            ++inner_iter;
            auto inner_model = inner_solver.getModel();
            PTRef over_projection = PTRef_Undef;
            PTRef under_projection = mbp.project(implicant, vars, *inner_model, over_projection);

            // std::cerr << "   IN: projected" << inner_iter + 1 << "..." << std::endl;
            // std::cerr << "     under projection: " << logic.printTerm(under_projection) << std::endl;
            // std::cerr << "     over projection: " << logic.printTerm(over_projection) << std::endl;

            implicant_over_conjuncts.push(over_projection);
            implicant_under_disjuncts.push(under_projection);

            // A mbp of the implicant is also a mbp of the fla
            under_projections.push(under_projection);

            // Block the found mbp
            inner_solver.assertProp(logic.mkNot(under_projection));

            if (limits.max_mbp_per_poly > 0 and inner_iter >= limits.max_mbp_per_poly) {
                result.precise_under = false;
                break;
            }
            // max_inner_iter = std::max(max_inner_iter, inner_iter);
        }
        // Here QE of implicant is done
        inner_solver.pop();

        PTRef implicant_projection_with_over = logic.mkAnd(implicant_over_conjuncts);
        over_projections.push(implicant_projection_with_over);
        outer_solver.assertProp(logic.mkNot(implicant_projection_with_over));
        unexplored = logic.mkAnd(unexplored, logic.mkNot(implicant_projection_with_over));
    }

    result.under = logic.mkOr(under_projections);
    result.over = limits.compute_overapproximation ?
        logic.mkOr(over_projections) : logic.getTerm_true();

    if (logic.isBooleanOperator(result.under) and not logic.isNot(result.under)) {
        result.under = ::rewriteMaxArityAggresive(logic, result.under);
        if (logic.isAnd(result.under) or logic.isOr(result.under)) {
            result.under = ::simplifyUnderAssignment_Aggressive(result.under, logic);
        }
    }
    if (result.over != PTRef_Undef and logic.isBooleanOperator(result.over) and not logic.isNot(result.over)) {
        result.over = ::rewriteMaxArityAggresive(logic, result.over);
        if (logic.isAnd(result.over) or logic.isOr(result.over)) {
            result.over = ::simplifyUnderAssignment_Aggressive(result.over, logic);
        }
    }

#if DEBUG_CHECK_BMBP
    // Check that under => over
    SMTSolver check_over_solver(logic, SMTSolver::WitnessProduction::ONLY_MODEL);
    check_over_solver.assertProp(result.under);
    check_over_solver.assertProp(logic.mkNot(result.over));
    auto check_over_res = check_over_solver.check();
    if (check_over_res == SMTSolver::Answer::SAT) {
        throw std::logic_error("Under does not imply over projection!?");
    }
    if (result.precise_over) {
        // Check that over => under
        SMTSolver check_under_solver(logic, SMTSolver::WitnessProduction::ONLY_MODEL);
        check_under_solver.assertProp(result.over);
        check_under_solver.assertProp(logic.mkNot(result.under));
        auto check_under_res = check_under_solver.check();
        if (check_under_res == SMTSolver::Answer::SAT) {
            throw std::logic_error("Over does not imply under projection!?");
        }
    }
#endif

    // if (max_inner_iter > 1) {
    //     std::cerr << "QE done: " << outer_iter << " blocks, " << max_inner_iter
    //             << " max mbps per block" << std::endl;
    // }

    return result;
}
} // namespace

namespace golem {

QEResult QuantifierElimination::eliminate(PTRef fla, vec<PTRef> const & vars, QEOptions limits) {
    if (not std::all_of(vars.begin(), vars.end(), [this](PTRef var) { return logic.isVar(var); }) or
        not logic.hasSortBool(fla)) {
        throw std::invalid_argument("Invalid arguments to quantifier elimination");
    }

    return ::eliminate_aux(logic, fla, vars, limits);
}

QEResult QuantifierElimination::keepOnly(PTRef fla, vec<PTRef> const & vars, QEOptions limits) {
    auto allVars = TermUtils(logic).getVars(fla);
    vec<PTRef> toEliminate;
    for (PTRef var : allVars) {
        if (std::find(vars.begin(), vars.end(), var) == vars.end()) { toEliminate.push(var); }
    }
    return eliminate(fla, toEliminate, limits);
}

} // namespace golem
