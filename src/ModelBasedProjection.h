//
// Created by Martin Blicha on 06.03.21.
//

#ifndef OPENSMT_MODELBASEDPROJECTION_H
#define OPENSMT_MODELBASEDPROJECTION_H

#endif //OPENSMT_MODELBASEDPROJECTION_H

#include "osmt_solver.h"
#include "osmt_terms.h"

#include <unordered_set>
#include <iosfwd>
class Logic;
class ArithLogic;

class ModelBasedProjection {
private:
    Logic & logic;

public:
    using VarsInfo = Map<PTRef, bool, PTRefHash>;

    explicit ModelBasedProjection(Logic & logic) : logic(logic) {}

    PTRef project(PTRef fla, vec<PTRef> const & varsToEliminate, Model & model);

    PTRef keepOnly(PTRef fla, vec<PTRef> const & varsToKeep, Model & model);

    using implicant_t = std::vector<PtAsgn>;
private:
    implicant_t projectSingleVar(PTRef var, implicant_t implicant, Model & model);

    implicant_t getImplicant(PTRef var, Model & model, VarsInfo const&);

    void dumpImplicant(std::ostream& out, implicant_t const & implicant);

    void postprocess(implicant_t & literals, ArithLogic & logic);

    // LIA version

    struct DivisibilityConstraint {
        PTRef constant;
        PTRef term;
    };

    using div_constraints_t = std::vector<DivisibilityConstraint>;

    implicant_t projectIntegerVars(PTRef* beg, PTRef* end, implicant_t implicant, Model & model);

    void processDivConstraints(PTRef var, div_constraints_t & divConstraints, implicant_t & implicant, Model & model);

    void processClassicLiterals(PTRef var, div_constraints_t & divConstraints, implicant_t & implicant, Model & model);

    struct LIABound {
        PTRef term;
        PTRef coeff;
    };

    struct LIABoundLower {
        PTRef term;
        PTRef coeff;
    };
    struct LIABoundUpper {
        PTRef term;
        PTRef coeff;
    };

    struct ResolveResult {
        std::vector<PTRef> bounds;
        DivisibilityConstraint constraint; // TODO: optional
        bool hasDivConstraint;
    };

    ResolveResult resolve(LIABoundLower const& lower, LIABoundUpper const& upper, Model & model, ArithLogic & lialogic);
};