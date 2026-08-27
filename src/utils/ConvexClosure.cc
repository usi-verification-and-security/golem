#include "ConvexClosure.h"

#include "QuantifierElimination.h"
#include "TermUtils.h"

#include <optional>
#include <utility>
#include <vector>

namespace golem {

namespace {

struct NormalizedAtom {
    PTRef linearTerm;
    PTRef constant;
    bool equality;
};

// Normalize `term <= 0` into (sum of linear factors, constant) such that
// `term <= 0` is equivalent to `linearTerm <= -constant`.
// The returned linearTerm contains no constant and constant is a numeric constant.
std::pair<PTRef, PTRef> normalizeLinearInequality(ArithLogic & logic, PTRef term) {
    if (not logic.isLinearTerm(term) and not logic.isNumConst(term)) {
        throw std::logic_error("Non-linear term encountered in ConvexClosure normalization");
    }

    auto extractConstantAndFactors = [&](PTRef t) -> std::pair<PTRef, vec<PTRef>> {
        if (logic.isNumConst(t)) { return std::make_pair(t, vec<PTRef>()); }
        if (logic.isNumVarLike(t)) {
            vec<PTRef> factors;
            factors.push(t);
            return std::make_pair(logic.getZeroForSort(logic.getSortRef(t)), std::move(factors));
        }
        if (logic.isTimes(t)) {
            assert(logic.isLinearFactor(t));
            vec<PTRef> factors;
            factors.push(t);
            return std::make_pair(logic.getZeroForSort(logic.getSortRef(t)), std::move(factors));
        }
        if (logic.isPlus(t)) {
            assert(logic.isLinearTerm(t));
            auto [constantValue, varFactors] = logic.getConstantAndFactors(t);
            PTRef constantTerm = logic.mkConst(logic.getSortRef(t), constantValue);
            return std::make_pair(constantTerm, std::move(varFactors));
        }
        throw std::logic_error("Unexpected arithmetic term in ConvexClosure normalization");
    };

    auto [constantTerm, varFactors] = extractConstantAndFactors(term);

    PTRef linearTerm;
    if (varFactors.size() == 0) {
        linearTerm = logic.getZeroForSort(logic.getSortRef(term));
    } else if (varFactors.size() == 1) {
        linearTerm = varFactors[0];
    } else {
        linearTerm = logic.mkPlus(varFactors);
    }

    return {linearTerm, constantTerm};
}

// Normalize a (possibly negated) arithmetic atom into the form
//   linearTerm <= constant   or   linearTerm = constant
// where `constant` is a numeric constant and `linearTerm` contains no constants.
// Returns std::nullopt if the atom cannot be represented as a convex polyhedron literal.
std::optional<NormalizedAtom> normalizeArithmeticLiteral(ArithLogic & logic, PTRef lit, bool negated) {
    if (logic.isNumEq(lit)) {
        // Disequalities cannot be represented in a convex polyhedron.
        if (negated) { return std::nullopt; }
        PTRef lhs = logic.getPterm(lit)[0];
        PTRef rhs = logic.getPterm(lit)[1];
        PTRef diff = logic.mkMinus(lhs, rhs);
        auto [linearTerm, constant] = normalizeLinearInequality(logic, diff);
        return NormalizedAtom{linearTerm, logic.mkNeg(constant), true};
    }

    auto handleInequality = [&](PTRef lhs, PTRef rhs, bool flip) -> std::optional<NormalizedAtom> {
        PTRef diff = flip ? logic.mkMinus(rhs, lhs) : logic.mkMinus(lhs, rhs);
        auto [linearTerm, constant] = normalizeLinearInequality(logic, diff);
        return NormalizedAtom{linearTerm, logic.mkNeg(constant), false};
    };

    if (logic.isLeq(lit)) {
        PTRef lhs = logic.getPterm(lit)[0];
        PTRef rhs = logic.getPterm(lit)[1];
        // <=  : lhs - rhs <= 0 ; not <=  : rhs - lhs <= 0
        return handleInequality(lhs, rhs, negated);
    }
    if (logic.isLt(lit)) {
        PTRef lhs = logic.getPterm(lit)[0];
        PTRef rhs = logic.getPterm(lit)[1];
        // <  : relax to lhs - rhs <= 0 ; not <  : relax to rhs - lhs <= 0
        return handleInequality(lhs, rhs, negated);
    }
    if (logic.isGeq(lit)) {
        PTRef lhs = logic.getPterm(lit)[0];
        PTRef rhs = logic.getPterm(lit)[1];
        // >=  : rhs - lhs <= 0 ; not >=  : lhs - rhs <= 0
        return handleInequality(lhs, rhs, not negated);
    }
    if (logic.isGt(lit)) {
        PTRef lhs = logic.getPterm(lit)[0];
        PTRef rhs = logic.getPterm(lit)[1];
        // >  : relax to rhs - lhs <= 0 ; not >  : relax to lhs - rhs <= 0
        return handleInequality(lhs, rhs, not negated);
    }
    // Non-arithmetic literal: drop.
    return std::nullopt;
}

PTRef rebuildAtom(ArithLogic & logic, NormalizedAtom const & atom, PTRef sigma) {
    PTRef scaledConstant = logic.mkTimes(atom.constant, sigma);
    if (atom.equality) {
        return logic.mkEq(atom.linearTerm, scaledConstant);
    }
    return logic.mkLeq(atom.linearTerm, scaledConstant);
}

} // namespace

PTRef ConvexClosure::getConvexClosure(vec<PTRef> const & formulas) {
    auto * arithLogic = dynamic_cast<ArithLogic *>(&logic);
    if (not arithLogic) { throw std::logic_error("ConvexClosure currently supports only arithmetic logics"); }

    // Collect all polyhedra (sets of normalized arithmetic atoms) over-approximating each input formula.
    std::vector<std::vector<NormalizedAtom>> polyhedra;
    std::unordered_set<PTRef, PTRefHash> allVariables;

    for (PTRef formula : formulas) {
        PTRef nnf = TermUtils(logic).toNNF(formula);
        vec<PTRef> conjuncts = TermUtils(logic).getTopLevelConjuncts(nnf);
        std::vector<NormalizedAtom> atoms;
        bool droppedAllLiterals = true;
        for (PTRef conj : conjuncts) {
            PTRef lit = conj;
            bool negated = false;
            if (logic.isNot(conj)) {
                lit = logic.getPterm(conj)[0];
                negated = true;
            }
            auto normalized = normalizeArithmeticLiteral(*arithLogic, lit, negated);
            if (normalized) {
                atoms.push_back(std::move(*normalized));
                droppedAllLiterals = false;
            }
        }

        if (droppedAllLiterals) {
            // A single unconstrained polyhedron makes the whole convex closure unconstrained.
            return logic.getTerm_true();
        }
        polyhedra.push_back(std::move(atoms));
    }

    if (polyhedra.empty()) { return logic.getTerm_true(); }

    // Collect all variables appearing in any polyhedron.
    for (auto const & poly : polyhedra) {
        for (auto const & atom : poly) {
            auto vars = TermUtils(logic).getVars(atom.linearTerm);
            for (PTRef var : vars) { allVariables.insert(var); }
        }
    }

    if (allVariables.empty()) { return logic.getTerm_true(); }

    // Verify all collected variables are arithmetic and share the same sort.
    SRef sort = SRef_Undef;
    for (PTRef var : allVariables) {
        if (not arithLogic->isNumVar(var)) {
            throw std::logic_error("ConvexClosure currently supports only linear arithmetic formulas");
        }
        SRef varSort = logic.getSortRef(var);
        if (sort == SRef_Undef) {
            sort = varSort;
        } else if (sort != varSort) {
            throw std::logic_error("ConvexClosure currently requires all variables to have the same sort");
        }
    }

    // Build the convex closure formula.
    // Variables:
    //   x      : original variables from allVariables
    //   z_i    : fresh variables for each polyhedron i
    //   sigma_i: fresh scalar variables for each polyhedron i
    std::vector<std::unordered_map<PTRef, PTRef, PTRefHash>> perPolyFreshVariables;
    vec<PTRef> sigmaVars;

    for (std::size_t i = 0; i < polyhedra.size(); ++i) {
        std::unordered_map<PTRef, PTRef, PTRefHash> freshForPoly;
        for (PTRef var : allVariables) {
            std::string name = "cc_z_" + std::to_string(i) + "_" + logic.getSymName(var);
            freshForPoly[var] = logic.mkVar(logic.getSortRef(var), name.c_str());
        }
        perPolyFreshVariables.push_back(std::move(freshForPoly));

        std::string sigmaName = "cc_sigma_" + std::to_string(i);
        sigmaVars.push(logic.mkVar(sort, sigmaName.c_str()));
    }

    auto substituteVariables = [&](PTRef term, std::unordered_map<PTRef, PTRef, PTRefHash> const & substMap) -> PTRef {
        TermUtils::substitutions_map subst;
        for (auto const & entry : substMap) { subst.insert({entry.first, entry.second}); }
        return TermUtils(logic).varSubstitute(term, subst);
    };

    vec<PTRef> closureConjuncts;

    // x = sum_i z_i
    for (PTRef x : allVariables) {
        vec<PTRef> sumArgs;
        for (auto const & freshMap : perPolyFreshVariables) { sumArgs.push(freshMap.at(x)); }
        PTRef sum = sumArgs.size() == 1 ? sumArgs[0] : arithLogic->mkPlus(sumArgs);
        closureConjuncts.push(arithLogic->mkEq(x, sum));
    }

    // 1 = sum_i sigma_i
    {
        vec<PTRef> sumArgs;
        for (PTRef sigma : sigmaVars) { sumArgs.push(sigma); }
        PTRef sum = sumArgs.size() == 1 ? sumArgs[0] : arithLogic->mkPlus(sumArgs);
        closureConjuncts.push(arithLogic->mkEq(arithLogic->mkConst(sort, "1"), sum));
    }

    // For each polyhedron: A_i z_i <= sigma_i a_i  and  sigma_i >= 0
    for (std::size_t i = 0; i < polyhedra.size(); ++i) {
        PTRef sigma = sigmaVars[i];
        for (auto const & atom : polyhedra[i]) {
            PTRef substitutedLinearTerm = substituteVariables(atom.linearTerm, perPolyFreshVariables[i]);
            NormalizedAtom substitutedAtom{substitutedLinearTerm, atom.constant, atom.equality};
            closureConjuncts.push(rebuildAtom(*arithLogic, substitutedAtom, sigma));
        }
        // sigma_i >= 0  <=>  0 <= sigma_i
        PTRef zero = arithLogic->getZeroForSort(sort);
        closureConjuncts.push(arithLogic->mkLeq(zero, sigma));
    }

    PTRef closureFormula = logic.mkAnd(closureConjuncts);

    // Eliminate the fresh variables and sigma variables.
    vec<PTRef> varsToEliminate;
    for (PTRef sigma : sigmaVars) { varsToEliminate.push(sigma); }
    for (auto const & freshMap : perPolyFreshVariables) {
        for (PTRef originalVar : allVariables) {
            (void)originalVar;
            varsToEliminate.push(freshMap.at(originalVar));
        }
    }

    QuantifierElimination qe(logic);
    QEOptions options;
    options.compute_overapproximation = true;
    options.max_mbp_per_poly = 10;
    options.max_disjunctions_in_over = 1;
    QEResult result = qe.eliminate(closureFormula, varsToEliminate, options);
    return result.over;
}

} // namespace golem
