//
// Created by Martin Blicha on 12.06.21.
//

#include "QuantifierElimination.h"

#include "ModelBasedProjection.h"
#include "TermUtils.h"


PTRef QuantifierElimination::keepOnly(PTRef fla, const vec<PTRef> & varsToKeep) {
    auto allVars = TermUtils(logic).getVars(fla);
    vec<PTRef> toEliminate;
    for (PTRef var : allVars) {
        if (std::find(varsToKeep.begin(), varsToKeep.end(), var) == varsToKeep.end()) {
            toEliminate.push(var);
        }
    }
    return eliminate(fla, toEliminate);
}

PTRef QuantifierElimination::eliminate(PTRef fla, PTRef var) {
    return eliminate(fla, vec<PTRef>{var});
}

PTRef QuantifierElimination::eliminate(PTRef fla, vec<PTRef> const & vars) {
    if (not std::all_of(vars.begin(), vars.end(), [this](PTRef var){ return logic.isVar(var); }) or not logic.hasSortBool(fla)) {
        throw std::invalid_argument("Invalid arguments to quantifier elimination");
    }

    fla = TermUtils(logic).toNNF(fla);
    vec<PTRef> projections;

    SMTConfig config;
    const char* msg = "ok";
    config.setOption(SMTConfig::o_produce_models, SMTOption(true), msg);
    MainSolver solver(logic, config, "QE solver");
    solver.insertFormula(fla);
    while(true) {
        auto res = solver.check();
        if (res == s_False) {
            break;
        } else if (res == s_True) {
            auto model = solver.getModel();
            ModelBasedProjection mbp(logic);
            PTRef projection = mbp.project(fla, vars, *model);
//            std::cout << "Projection: " << logic.printTerm(projection) << std::endl;
            projections.push(projection);
            solver.push(); // to avoid processing the same formula over and over again
            solver.insertFormula(logic.mkNot(projection));
        } else {
            throw std::logic_error("Error in solver during quantifier elimination");
        }
    }
    PTRef result = logic.mkOr(projections);
    if (logic.isBooleanOperator(result) and not logic.isNot(result)) {
        result = ::rewriteMaxArityAggresive(logic, result);
        result = ::simplifyUnderAssignment_Aggressive(result, logic);
        // TODO: more simplifications?
    }
    return result;
}
