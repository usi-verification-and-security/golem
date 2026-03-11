/*
 * Copyright (c) 2021-2025, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "QuantifierElimination.h"

#include "ModelBasedProjection.h"
#include "TermUtils.h"
#include "utils/SmtSolver.h"

namespace {
using namespace golem;
PTRef eliminate(Logic & logic, PTRef fla, vec<PTRef> const & vars, PTRef* overapprox) {
    vec<PTRef> projections;

    bool overapprox_requested = (overapprox != nullptr);
    vec<PTRef> over_conjuncts;

    fla = TermUtils(logic).toNNF(fla);

    SMTSolver solver(logic, SMTSolver::WitnessProduction::ONLY_MODEL);
    solver.assertProp(fla);
    while (true) {
        auto res = solver.check();
        if (res == SMTSolver::Answer::UNSAT) { break; }
        if (res == SMTSolver::Answer::SAT) {
            auto model = solver.getModel();
            ModelBasedProjection mbp(logic);
            PTRef over_projection = PTRef_Undef;
            PTRef projection = mbp.project(fla, vars, *model, (overapprox_requested ? &over_projection : nullptr));
            projections.push(projection);
            if (overapprox_requested && over_projection != logic.getTerm_true()) {
                over_conjuncts.push(over_projection);
            }
            solver.push(); // to avoid processing the same formula over and over again
            solver.assertProp(logic.mkNot(projection));
        } else {
            throw std::logic_error("Error in solver during quantifier elimination");
        }
    }
    PTRef result = logic.mkOr(projections);
    if (logic.isBooleanOperator(result) and not logic.isNot(result)) {
        result = ::rewriteMaxArityAggresive(logic, result);
        if (logic.isAnd(result) or logic.isOr(result)) {
            result = ::simplifyUnderAssignment_Aggressive(result, logic);
        }
        // TODO: more simplifications?
    }

    if (!overapprox_requested) {
        return result;
    }

    *overapprox = logic.getTerm_true();
    if (projections.size() == 0) {
        *overapprox = logic.getTerm_false();
    }
    if (over_conjuncts.size() > 0) {
        *overapprox = logic.mkAnd(over_conjuncts);
        if (logic.isBooleanOperator(*overapprox) and not logic.isNot(*overapprox)) {
            *overapprox = ::rewriteMaxArityAggresive(logic, *overapprox);
            if (logic.isAnd(*overapprox) or logic.isOr(*overapprox)) {
                *overapprox = ::simplifyUnderAssignment_Aggressive(*overapprox, logic);
            }
        }
    }

#define CHECK_VALIDITY_OF_OVERAPPROXIMATION 1
#if CHECK_VALIDITY_OF_OVERAPPROXIMATION
    // CHECK VALIDITY OF OVERAPPROXIMATION
    // FreeVars(*overapprox) should be subset of FreeVars(fla) and should not contain any of vars
    auto overVars = TermUtils(logic).getVars(*overapprox);
    auto flaVars = TermUtils(logic).getVars(fla);
    for (PTRef var : overVars) {
        if (std::find(flaVars.begin(), flaVars.end(), var) == flaVars.end()) {
            throw std::logic_error("Overapproximation contains variable not present in original formula");
        }
        if (std::find(vars.begin(), vars.end(), var) != vars.end()) {
            throw std::logic_error("Overapproximation contains variable that should be eliminated");
        }
    }
    // Overapproximation should be entailed by original formula
    SMTSolver overapproxSolver(logic);
    overapproxSolver.assertProp(fla);
    overapproxSolver.assertProp(logic.mkNot(*overapprox));
    auto overapproxRes = overapproxSolver.check();
    if (overapproxRes != SMTSolver::Answer::UNSAT) {
        throw std::logic_error("Overapproximation is not an overapproximation of the result!");
    }
#endif

    return result;
}
} // namespace

namespace golem {
PTRef QuantifierElimination::keepOnly(PTRef fla, const vec<PTRef> & varsToKeep, PTRef* overapprox) {
    auto allVars = TermUtils(logic).getVars(fla);
    vec<PTRef> toEliminate;
    for (PTRef var : allVars) {
        if (std::find(varsToKeep.begin(), varsToKeep.end(), var) == varsToKeep.end()) { toEliminate.push(var); }
    }
    return eliminate(fla, toEliminate, overapprox);
}

PTRef QuantifierElimination::eliminate(PTRef fla, PTRef var, PTRef* overapprox) {
    return eliminate(fla, vec<PTRef>{var}, overapprox);
}

PTRef QuantifierElimination::eliminate(PTRef fla, vec<PTRef> const & vars, PTRef* overapprox) {
    if (not std::all_of(vars.begin(), vars.end(), [this](PTRef var) { return logic.isVar(var); }) or
        not logic.hasSortBool(fla)) {
        throw std::invalid_argument("Invalid arguments to quantifier elimination");
    }

    fla = TermUtils(logic).toNNF(fla);
    return ::eliminate(logic, fla, vars, overapprox);
}
} // namespace golem
