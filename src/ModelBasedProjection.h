/*
 * Copyright (c) 2021-2025, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef GOLEM_MODELBASEDPROJECTION_H
#define GOLEM_MODELBASEDPROJECTION_H

#include "osmt_solver.h"
#include "osmt_terms.h"

#include <iosfwd>
#include <unordered_set>

namespace golem {

struct MBPOptions {
    MBPOptions() :
        fm_bound_threshold(1),
        pick_best_side(false),
        use_unsat_core(false) {}
    MBPOptions(short fm_bound, bool best_side, bool unsat_core) :
        fm_bound_threshold(fm_bound),
        pick_best_side(best_side),
        use_unsat_core(unsat_core) {}
    short fm_bound_threshold;
    bool pick_best_side;
    bool use_unsat_core;
};

class ModelBasedProjection {
private:
    Logic & logic;

public:
    using VarsInfo = Map<PTRef, bool, PTRefHash>;

    MBPOptions options;

    explicit ModelBasedProjection(Logic & logic) : logic(logic) {}
    explicit ModelBasedProjection(Logic & logic, MBPOptions mbp_options)
        : logic(logic), options(mbp_options) {}

    PTRef getModelBasedImplicant(PTRef fla, vec<PTRef> const & varsToEliminate, Model & model);

    PTRef project(PTRef fla, vec<PTRef> const & varsToEliminate, Model & model, PTRef & overapprox) {
        return project_aux(fla, varsToEliminate, model, &overapprox);
    }
    PTRef project(PTRef fla, vec<PTRef> const &varsToEliminate, Model &model) {
        return project_aux(fla, varsToEliminate, model, nullptr);
    }

    PTRef keepOnly(PTRef fla, vec<PTRef> const &varsToKeep, Model & model, PTRef & overapprox) {
        return keepOnly_aux(fla, varsToKeep, model, &overapprox);
    }
    PTRef keepOnly(PTRef fla, vec<PTRef> const &varsToKeep, Model & model) {
        return keepOnly_aux(fla, varsToKeep, model, nullptr);
    }

    using implicant_t = std::vector<PtAsgn>;

private:
    implicant_t projectSingleVar(PTRef var, implicant_t implicant, Model & model);

    implicant_t getImplicant(PTRef var, Model & model, VarsInfo const &);

    void dumpImplicant(std::ostream & out, implicant_t const & implicant);

    void postprocess(implicant_t & literals, ArithLogic & logic);

    PTRef get_mbp(implicant_t implicant, implicant_t const & background, PTRef original_fla, PTRef* overapprox);

    PTRef project_aux(PTRef fla, vec<PTRef> const & varsToEliminate, Model & model, PTRef* overapprox);
    PTRef keepOnly_aux(PTRef fla, vec<PTRef> const & varsToKeep, Model & model, PTRef* overapprox);
 
    // LIA version

    struct DivisibilityConstraint {
        PTRef constant;
        PTRef term;
    };

    using div_constraints_t = std::vector<DivisibilityConstraint>;

    implicant_t projectIntegerVars(PTRef * beg, PTRef * end, implicant_t implicant, Model & model);

    void processDivConstraints(PTRef var, div_constraints_t & divConstraints, implicant_t & implicant, Model & model);

    void processClassicLiterals(PTRef var, div_constraints_t & divConstraints, implicant_t & implicant, Model & model);

    struct LIABound {
        PTRef term;
        PTRef coeff;
        bool isLower;
    };

    struct ResolveResult {
        std::vector<PTRef> bounds;
        DivisibilityConstraint constraint; // TODO: optional
        bool hasDivConstraint;
    };

    ResolveResult resolve(LIABound const & lower, LIABound const & upper, Model & model,
                          ArithLogic & lialogic);
};
} // namespace golem
#endif // GOLEM_MODELBASEDPROJECTION_H
