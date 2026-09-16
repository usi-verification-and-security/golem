#include "ConvexClosure.h"

#include "QuantifierElimination.h"
#include "SmtSolver.h"
#include "TermUtils.h"

#include <algorithm>
#include <optional>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

namespace golem {

namespace {

using Coefficients = std::vector<std::pair<PTRef, FastRational>>;

// A linear atom in explicit coefficient form:
//    sum_j coefficient_j * variable_j   (<= | =)   constant
struct LinearAtom {
    Coefficients coefficients;
    FastRational constant;
    bool equality;
};

FastRational absoluteValue(FastRational const & value) {
    return value.sign() < 0 ? -value : value;
}

// GCD of the absolute values of all coefficients; zero if there are no coefficients.
FastRational coefficientGcd(Coefficients const & coefficients) {
    FastRational result(0);
    for (auto const & [var, coeff] : coefficients) {
        (void)var;
        result = gcd(result, absoluteValue(coeff));
    }
    return result;
}

// LCM of the denominators of all coefficients and of `constant`.
FastRational commonDenominator(Coefficients const & coefficients, FastRational const & constant) {
    FastRational result = constant.get_den();
    for (auto const & [var, coeff] : coefficients) {
        (void)var;
        result = lcm(result, coeff.get_den());
    }
    return result;
}

void addCoefficient(Coefficients & coefficients, PTRef var, FastRational const & value) {
    auto it = std::find_if(coefficients.begin(), coefficients.end(),
                           [var](auto const & entry) { return entry.first == var; });
    if (it == coefficients.end()) {
        coefficients.emplace_back(var, value);
    } else {
        it->second = it->second + value;
    }
}

// Decompose a linear term into its coefficients over variables plus a constant offset.
std::pair<Coefficients, FastRational> decomposeLinearTerm(ArithLogic & logic, PTRef term) {
    Coefficients coefficients;
    FastRational constant(0);

    auto handleFactor = [&](PTRef factor) {
        auto [var, coeff] = logic.splitTermToVarAndConst(factor);
        if (var == PTRef_Undef) {
            constant = constant + logic.getNumConst(coeff);
        } else {
            addCoefficient(coefficients, var, logic.getNumConst(coeff));
        }
    };

    if (logic.isNumConst(term)) {
        constant = logic.getNumConst(term);
    } else if (logic.isPlus(term)) {
        if (not logic.isLinearTerm(term)) {
            throw std::logic_error("Non-linear term encountered in ConvexClosure normalization");
        }
        auto [constantValue, factors] = logic.getConstantAndFactors(term);
        constant = constantValue;
        for (PTRef factor : factors) { handleFactor(factor); }
    } else if (logic.isNumVarLike(term) or logic.isTimes(term)) {
        if (logic.isTimes(term) and not logic.isLinearFactor(term)) {
            throw std::logic_error("Non-linear term encountered in ConvexClosure normalization");
        }
        handleFactor(term);
    } else {
        throw std::logic_error("Unexpected arithmetic term in ConvexClosure normalization");
    }

    coefficients.erase(std::remove_if(coefficients.begin(), coefficients.end(),
                                      [](auto const & entry) { return entry.second.sign() == 0; }),
                       coefficients.end());
    return {std::move(coefficients), std::move(constant)};
}

// Tighten `sum c_j x_j (<=|=) k` to the smallest integer-equivalent atom.
// With g = gcd(c_j) every integer point satisfies `sum (c_j/g) x_j (<=|=) k/g`, so the
// inequality can be rounded down and the equality can only be divided when g divides k.
// This is an equivalence over the integers, hence it is sound in any polarity.
void tightenToIntegers(LinearAtom & atom) {
    for (auto const & [var, coeff] : atom.coefficients) {
        (void)var;
        if (not coeff.isInteger()) { return; }
    }
    if (not atom.constant.isInteger()) { return; }
    FastRational divisor = coefficientGcd(atom.coefficients);
    if (divisor.sign() == 0 or divisor.isOne()) { return; }
    FastRational scaledConstant = atom.constant / divisor;
    if (atom.equality) {
        if (not scaledConstant.isInteger()) { return; }
    } else {
        scaledConstant = scaledConstant.floor();
    }
    for (auto & [var, coeff] : atom.coefficients) {
        (void)var;
        coeff = coeff / divisor;
    }
    atom.constant = scaledConstant;
}

// Normalize a (possibly negated) arithmetic literal into `sum c_j x_j (<= | =) k`.
// Over the integers strict inequalities are tightened (`t < k` becomes `t <= k-1`) and the
// atom is divided by the gcd of its coefficients; over the rationals strict inequalities are
// relaxed into non-strict ones, which over-approximates the literal.
// Returns nullopt for literals that cannot be part of a convex polyhedron.
std::optional<LinearAtom> normalizeArithmeticLiteral(ArithLogic & logic, PTRef lit, bool negated) {
    bool const isEquality = logic.isNumEq(lit);
    bool const isGreater = logic.isGeq(lit) or logic.isGt(lit);
    bool const isStrictRelation = logic.isLt(lit) or logic.isGt(lit);
    if (not isEquality and not isGreater and not logic.isLeq(lit) and not logic.isLt(lit)) {
        // Non-arithmetic literal: drop.
        return std::nullopt;
    }
    // Disequalities cannot be represented in a convex polyhedron.
    if (isEquality and negated) { return std::nullopt; }

    PTRef lhs = logic.getPterm(lit)[0];
    PTRef rhs = logic.getPterm(lit)[1];
    // Orient everything into `diff (<=|=) 0`. Negating a literal both swaps the sides and
    // toggles strictness.
    bool const flip = not isEquality and (isGreater != negated);
    bool const strict = not isEquality and (isStrictRelation != negated);
    PTRef diff = flip ? logic.mkMinus(rhs, lhs) : logic.mkMinus(lhs, rhs);
    bool const integers = logic.getSortRef(diff) == logic.getSort_int();

    auto [coefficients, offset] = decomposeLinearTerm(logic, diff);
    LinearAtom atom{std::move(coefficients), -offset, isEquality};
    if (strict and integers) { atom.constant = atom.constant - FastRational(1); }
    if (integers) { tightenToIntegers(atom); }
    return atom;
}

// Rebuild `sum c_j x_j (<=|=) k` as a term of `logic`, over the variables the atom refers to.
PTRef atomToTerm(ArithLogic & logic, LinearAtom const & atom) {
    assert(not atom.coefficients.empty());
    SRef sort = logic.getSortRef(atom.coefficients.front().first);
    vec<PTRef> summands;
    for (auto const & [var, coeff] : atom.coefficients) {
        summands.push(logic.mkTimes(logic.mkConst(sort, coeff), var));
    }
    PTRef lhs = summands.size() == 1 ? summands[0] : logic.mkPlus(summands);
    PTRef rhs = logic.mkConst(sort, atom.constant);
    return atom.equality ? logic.mkEq(lhs, rhs) : logic.mkLeq(lhs, rhs);
}

PTRef polyhedronToTerm(ArithLogic & logic, std::vector<LinearAtom> const & atoms) {
    vec<PTRef> conjuncts;
    for (auto const & atom : atoms) { conjuncts.push(atomToTerm(logic, atom)); }
    return logic.mkAnd(conjuncts);
}

/*
 * Translates a formula of the rational encoding logic back into the source logic.
 *
 * When the source variables are integers, every atom is first scaled to integer coefficients
 * (multiplying by the lcm of the denominators) and then tightened with `tightenToIntegers`.
 * Both steps are equivalences over the integer points, so they hold under any polarity and the
 * translated formula has exactly the same integer models as the original one.
 */
class BackTranslator {
public:
    BackTranslator(ArithLogic & from, ArithLogic & to, std::unordered_map<PTRef, PTRef, PTRefHash> varMap,
                   bool integers)
        : from(from), to(to), varMap(std::move(varMap)), integers(integers) {}

    PTRef translate(PTRef term) {
        if (from.isTrue(term)) { return to.getTerm_true(); }
        if (from.isFalse(term)) { return to.getTerm_false(); }
        if (from.isAnd(term) or from.isOr(term)) {
            vec<PTRef> args;
            for (int i = 0; i < from.getPterm(term).size(); ++i) {
                args.push(translate(from.getPterm(term)[i]));
            }
            return from.isAnd(term) ? to.mkAnd(args) : to.mkOr(args);
        }
        if (from.isNot(term)) { return to.mkNot(translate(from.getPterm(term)[0])); }
        return translateAtom(term);
    }

private:
    PTRef translateAtom(PTRef term) {
        bool const isEquality = from.isNumEq(term);
        bool const isGreater = from.isGeq(term) or from.isGt(term);
        bool strict = from.isLt(term) or from.isGt(term);
        if (not isEquality and not isGreater and not from.isLeq(term) and not from.isLt(term)) {
            throw std::logic_error("Unexpected atom in the result of ConvexClosure elimination");
        }
        PTRef lhs = from.getPterm(term)[0];
        PTRef rhs = from.getPterm(term)[1];
        PTRef diff = (not isEquality and isGreater) ? from.mkMinus(rhs, lhs) : from.mkMinus(lhs, rhs);
        auto [encodedCoefficients, offset] = decomposeLinearTerm(from, diff);

        Coefficients coefficients;
        for (auto const & [var, coeff] : encodedCoefficients) {
            addCoefficient(coefficients, varMap.at(var), coeff);
        }
        LinearAtom atom{std::move(coefficients), -offset, isEquality};

        if (atom.coefficients.empty()) {
            bool const holds = isEquality           ? atom.constant.sign() == 0
                               : strict             ? atom.constant.sign() > 0
                                                    : atom.constant.sign() >= 0;
            return holds ? to.getTerm_true() : to.getTerm_false();
        }

        if (integers) {
            FastRational scale = commonDenominator(atom.coefficients, atom.constant);
            if (not scale.isOne()) {
                for (auto & [var, coeff] : atom.coefficients) {
                    (void)var;
                    coeff = coeff * scale;
                }
                atom.constant = atom.constant * scale;
            }
            if (strict) {
                atom.constant = atom.constant - FastRational(1);
                strict = false;
            }
            tightenToIntegers(atom);
            if (atom.equality) {
                // `tightenToIntegers` refuses to divide when the gcd does not divide the constant,
                // which means the equality has no integer solution.
                FastRational divisor = coefficientGcd(atom.coefficients);
                if (divisor.sign() != 0 and not(atom.constant / divisor).isInteger()) {
                    return to.getTerm_false();
                }
            }
        }

        SRef sort = to.getSortRef(atom.coefficients.front().first);
        vec<PTRef> summands;
        for (auto const & [var, coeff] : atom.coefficients) {
            summands.push(to.mkTimes(to.mkConst(sort, coeff), var));
        }
        PTRef left = summands.size() == 1 ? summands[0] : to.mkPlus(summands);
        PTRef right = to.mkConst(sort, atom.constant);
        if (isEquality) { return to.mkEq(left, right); }
        return strict ? to.mkLt(left, right) : to.mkLeq(left, right);
    }

    ArithLogic & from;
    ArithLogic & to;
    std::unordered_map<PTRef, PTRef, PTRefHash> varMap;
    bool integers;
};

} // namespace

PTRef ConvexClosure::getConvexClosure(vec<PTRef> const & formulas) {
    auto * arithLogic = dynamic_cast<ArithLogic *>(&logic);
    if (not arithLogic) { throw std::logic_error("ConvexClosure currently supports only arithmetic logics"); }
    if (formulas.size() == 0) { return logic.getTerm_true(); }

    // Collect all polyhedra (sets of normalized arithmetic atoms) over-approximating each input formula.
    std::vector<std::vector<LinearAtom>> polyhedra;

    for (PTRef formula : formulas) {
        PTRef nnf = TermUtils(logic).toNNF(formula);
        vec<PTRef> conjuncts = TermUtils(logic).getTopLevelConjuncts(nnf);
        std::vector<LinearAtom> atoms;
        bool infeasible = false;
        for (PTRef conj : conjuncts) {
            if (logic.isTrue(conj)) { continue; }
            if (logic.isFalse(conj)) {
                infeasible = true;
                continue;
            }
            PTRef lit = conj;
            bool negated = false;
            if (logic.isNot(conj)) {
                lit = logic.getPterm(conj)[0];
                negated = true;
            }
            auto normalized = normalizeArithmeticLiteral(*arithLogic, lit, negated);
            if (not normalized) { continue; }
            if (normalized->coefficients.empty()) {
                // A variable-free atom is either trivially true (drop it) or makes the polyhedron empty.
                bool const holds = normalized->equality ? normalized->constant.sign() == 0
                                                        : normalized->constant.sign() >= 0;
                if (not holds) { infeasible = true; }
                continue;
            }
            atoms.push_back(std::move(*normalized));
        }

        if (infeasible) { continue; }
        if (atoms.empty()) {
            // A single unconstrained polyhedron makes the whole convex closure unconstrained.
            return logic.getTerm_true();
        }
        // The syntactic convex closure is exact only for non-empty polyhedra: for an empty one the
        // sigma_i = 0 case still admits its recession cone and would add spurious directions.
        SMTSolver solver(logic, SMTSolver::WitnessProduction::NONE);
        solver.assertProp(polyhedronToTerm(*arithLogic, atoms));
        if (solver.check() == SMTSolver::Answer::UNSAT) { continue; }
        polyhedra.push_back(std::move(atoms));
    }

    // Every input formula is unsatisfiable, so is their disjunction.
    if (polyhedra.empty()) { return logic.getTerm_false(); }

    // Collect all variables appearing in any polyhedron, in a deterministic order.
    std::vector<PTRef> variables;
    std::unordered_set<PTRef, PTRefHash> seenVariables;
    for (auto const & poly : polyhedra) {
        for (auto const & atom : poly) {
            for (auto const & [var, coeff] : atom.coefficients) {
                (void)coeff;
                if (seenVariables.insert(var).second) { variables.push_back(var); }
            }
        }
    }
    if (variables.empty()) { return logic.getTerm_true(); }

    // Verify all collected variables are arithmetic and share the same sort.
    SRef sort = logic.getSortRef(variables.front());
    for (PTRef var : variables) {
        if (not arithLogic->isNumVar(var)) {
            throw std::logic_error("ConvexClosure currently supports only linear arithmetic formulas");
        }
        if (logic.getSortRef(var) != sort) {
            throw std::logic_error("ConvexClosure currently requires all variables to have the same sort");
        }
    }
    bool const integers = sort == arithLogic->getSort_int();

    // The syntactic convex closure needs rational multipliers, so the encoding is always built in a
    // private LRA logic over shadow copies of the original variables. Over the integers this is the
    // rational relaxation of the convex closure, which still over-approximates the union; the result
    // is mapped back to integer atoms (and tightened) by `BackTranslator`.
    ArithLogic encodingLogic(Logic_t::QF_LRA);
    SRef encodingSort = encodingLogic.getSort_real();
    auto encodingConst = [&](FastRational const & value) { return encodingLogic.mkConst(encodingSort, value); };

    std::unordered_map<PTRef, std::size_t, PTRefHash> variableIndex;
    std::vector<PTRef> shadowVariables;
    std::unordered_map<PTRef, PTRef, PTRefHash> shadowToOriginal;
    for (std::size_t j = 0; j < variables.size(); ++j) {
        std::string name = "cc_x_" + std::to_string(j);
        PTRef shadow = encodingLogic.mkRealVar(name.c_str());
        variableIndex[variables[j]] = j;
        shadowVariables.push_back(shadow);
        shadowToOriginal[shadow] = variables[j];
    }

    // Variables of the encoding:
    //   x      : shadow copies of the original variables
    //   z_i    : fresh variables for each polyhedron i
    //   sigma_i: fresh scalar variables for each polyhedron i
    std::vector<std::vector<PTRef>> zVariables(polyhedra.size());
    std::vector<PTRef> sigmaVariables;
    for (std::size_t i = 0; i < polyhedra.size(); ++i) {
        for (std::size_t j = 0; j < variables.size(); ++j) {
            std::string name = "cc_z_" + std::to_string(i) + "_" + std::to_string(j);
            zVariables[i].push_back(encodingLogic.mkRealVar(name.c_str()));
        }
        std::string sigmaName = "cc_sigma_" + std::to_string(i);
        sigmaVariables.push_back(encodingLogic.mkRealVar(sigmaName.c_str()));
    }

    vec<PTRef> closureConjuncts;

    // x = sum_i z_i
    for (std::size_t j = 0; j < variables.size(); ++j) {
        vec<PTRef> sumArgs;
        for (std::size_t i = 0; i < polyhedra.size(); ++i) { sumArgs.push(zVariables[i][j]); }
        PTRef sum = sumArgs.size() == 1 ? sumArgs[0] : encodingLogic.mkPlus(sumArgs);
        closureConjuncts.push(encodingLogic.mkEq(shadowVariables[j], sum));
    }

    // 1 = sum_i sigma_i
    {
        vec<PTRef> sumArgs;
        for (PTRef sigma : sigmaVariables) { sumArgs.push(sigma); }
        PTRef sum = sumArgs.size() == 1 ? sumArgs[0] : encodingLogic.mkPlus(sumArgs);
        closureConjuncts.push(encodingLogic.mkEq(encodingConst(FastRational(1)), sum));
    }

    // For each polyhedron: A_i z_i <= sigma_i a_i  and  sigma_i >= 0
    for (std::size_t i = 0; i < polyhedra.size(); ++i) {
        PTRef sigma = sigmaVariables[i];
        for (auto const & atom : polyhedra[i]) {
            vec<PTRef> summands;
            for (auto const & [var, coeff] : atom.coefficients) {
                summands.push(encodingLogic.mkTimes(encodingConst(coeff), zVariables[i][variableIndex.at(var)]));
            }
            PTRef lhs = summands.size() == 1 ? summands[0] : encodingLogic.mkPlus(summands);
            PTRef rhs = encodingLogic.mkTimes(encodingConst(atom.constant), sigma);
            closureConjuncts.push(atom.equality ? encodingLogic.mkEq(lhs, rhs) : encodingLogic.mkLeq(lhs, rhs));
        }
        closureConjuncts.push(encodingLogic.mkLeq(encodingLogic.getTerm_RealZero(), sigma));
    }

    PTRef closureFormula = encodingLogic.mkAnd(closureConjuncts);

    // Eliminate the fresh variables and sigma variables.
    vec<PTRef> varsToEliminate;
    for (PTRef sigma : sigmaVariables) { varsToEliminate.push(sigma); }
    for (auto const & zVars : zVariables) {
        for (PTRef z : zVars) { varsToEliminate.push(z); }
    }

    QuantifierElimination qe(encodingLogic);
    QEOptions options;
    options.compute_overapproximation = true;
    options.max_mbp_per_poly = 10;
    options.max_disjunctions_in_over = 1;
    QEResult result = qe.eliminate(closureFormula, varsToEliminate, options);
    if (result.over == PTRef_Undef) { return logic.getTerm_true(); }

    // Anything the elimination failed to remove cannot be expressed in the source logic; giving up
    // and returning the trivial over-approximation is always sound.
    for (PTRef var : TermUtils(encodingLogic).getVars(result.over)) {
        if (shadowToOriginal.find(var) == shadowToOriginal.end()) { return logic.getTerm_true(); }
    }

    BackTranslator translator(encodingLogic, *arithLogic, std::move(shadowToOriginal), integers);
    return translator.translate(result.over);
}

} // namespace golem
