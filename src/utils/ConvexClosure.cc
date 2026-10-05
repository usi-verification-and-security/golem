#include "ConvexClosure.h"

#include "QuantifierElimination.h"
#include "SmtSolver.h"
#include "TermUtils.h"

#include <algorithm>
#include <cassert>
#include <cstddef>
#include <map>
#include <optional>
#include <stdexcept>
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

bool isArithmeticRelation(ArithLogic & logic, PTRef term) {
    return logic.isNumEq(term) or logic.isLeq(term) or logic.isLt(term) or logic.isGeq(term) or
           logic.isGt(term);
}

// A conjunct is factorizable when it constrains no arithmetic variable. That covers a Boolean
// literal, but also a clause such as `(or ~b1 b2)`, which is what NNF makes of `(= b1 b2)`.
// Only precision depends on this test: conjoining a conjunct of every input to the result is
// sound whatever the conjunct says.
bool isPureBoolean(Logic & logic, PTRef conj) {
    for (PTRef var : TermUtils(logic).getVars(conj)) {
        if (not logic.hasSortBool(var)) { return false; }
    }
    return true;
}

// Upper bound on the number of cubes `toDNF` would produce, saturating at `cap + 1`. Computing it
// first is what makes the cube budget a bound on the work and not only on the result.
std::size_t countCubes(Logic & logic, PTRef fla, std::size_t cap,
                       std::unordered_map<PTRef, std::size_t, PTRefHash> & memo) {
    auto it = memo.find(fla);
    if (it != memo.end()) { return it->second; }
    std::size_t result = 1;
    bool const conjunction = logic.isAnd(fla);
    if (conjunction or logic.isOr(fla)) {
        result = conjunction ? 1 : 0;
        Pterm const & term = logic.getPterm(fla);
        for (int i = 0; i < term.size(); ++i) {
            std::size_t const child = countCubes(logic, term[i], cap, memo);
            result = conjunction ? result * child : result + child;
            if (result > cap) {
                result = cap + 1;
                break;
            }
        }
    }
    memo.emplace(fla, result);
    return result;
}

// One input of the closure: the polyhedron over-approximating its arithmetic literals, plus the
// conjuncts that constrain no arithmetic variable.
struct Disjunct {
    std::vector<LinearAtom> polyhedron;
    std::vector<PTRef> boolConjuncts;
};

/*
 * A two-literal clause whose literals negate to `sum c_j x_j <= k` and `sum -c_j x_j <= -k` says
 * `sum c_j x_j != k`: a disequality spelled as a clause. It is what NNF makes of the negation of an
 * equality written as two inequalities, e.g. `not (and (<= 0 x) (<= 0 (* -1 x)))`, the form in which
 * interpolants state equalities. Like any disequality it cannot be part of a convex polyhedron.
 */
bool isDisequalityClause(ArithLogic & logic, PTRef clause) {
    if (not logic.isOr(clause) or logic.getPterm(clause).size() != 2) { return false; }
    std::optional<LinearAtom> negations[2];
    for (int i = 0; i < 2; ++i) {
        PTRef lit = logic.getPterm(clause)[i];
        bool const negated = logic.isNot(lit);
        PTRef atom = negated ? logic.getPterm(lit)[0] : lit;
        if (not isArithmeticRelation(logic, atom)) { return false; }
        negations[i] = normalizeArithmeticLiteral(logic, atom, not negated);
        if (not negations[i] or negations[i]->equality) { return false; }
    }
    LinearAtom const & first = *negations[0];
    LinearAtom const & second = *negations[1];
    if (first.coefficients.empty() or first.coefficients.size() != second.coefficients.size() or
        first.constant != -second.constant) {
        return false;
    }
    return std::all_of(first.coefficients.begin(), first.coefficients.end(), [&second](auto const & entry) {
        auto it = std::find_if(second.coefficients.begin(), second.coefficients.end(),
                               [&entry](auto const & other) { return other.first == entry.first; });
        return it != second.coefficients.end() and it->second == -entry.second;
    });
}

/*
 * Drops the top-level conjuncts of an NNF formula that are disequalities spelled as clauses
 * (isDisequalityClause). Dropping a conjunct only weakens the formula, so this is sound; and it
 * keeps each such clause from counting as a mixed conjunct, which would double the number of cubes
 * the formula is expanded into, only for the hull to relax the split away again.
 */
PTRef dropDisequalityClauses(ArithLogic & logic, PTRef nnf) {
    vec<PTRef> kept;
    for (PTRef conj : TermUtils(logic).getTopLevelConjuncts(nnf)) {
        if (not isDisequalityClause(logic, conj)) { kept.push(conj); }
    }
    return logic.mkAnd(std::move(kept));
}

/*
 * Split the top-level conjuncts of an NNF formula. Returns nullopt when the conjunction is already
 * syntactically infeasible. Conjuncts that are dropped are dropped soundly, since removing a
 * conjunct only weakens the formula, and the closure over-approximates: disequalities (not convex),
 * and conjuncts mixing Boolean and arithmetic content, which set `hasMixed` so that the caller can
 * decide to expand the formula into cubes instead.
 */
std::optional<Disjunct> buildDisjunct(ArithLogic & logic, PTRef nnf, bool & hasMixed) {
    Disjunct disjunct;
    for (PTRef conj : TermUtils(logic).getTopLevelConjuncts(nnf)) {
        if (logic.isTrue(conj)) { continue; }
        if (logic.isFalse(conj)) { return std::nullopt; }
        PTRef lit = conj;
        bool negated = false;
        if (logic.isNot(conj)) {
            lit = logic.getPterm(conj)[0];
            negated = true;
        }
        if (isArithmeticRelation(logic, lit)) {
            auto normalized = normalizeArithmeticLiteral(logic, lit, negated);
            // A disequality cannot be part of a convex polyhedron.
            if (not normalized) { continue; }
            // Neither can a relation over a non-variable term such as `(mod t k)`, which the linear
            // decomposition would otherwise take for a variable; dropped like the conjuncts above.
            if (std::any_of(normalized->coefficients.begin(), normalized->coefficients.end(),
                            [&logic](auto const & entry) { return not logic.isNumVar(entry.first); })) {
                continue;
            }
            if (normalized->coefficients.empty()) {
                // A variable-free atom is either trivially true (drop it) or makes the polyhedron empty.
                bool const holds = normalized->equality ? normalized->constant.sign() == 0
                                                        : normalized->constant.sign() >= 0;
                if (not holds) { return std::nullopt; }
                continue;
            }
            disjunct.polyhedron.push_back(std::move(*normalized));
            continue;
        }
        if (isPureBoolean(logic, conj)) {
            disjunct.boolConjuncts.push_back(conj);
            continue;
        }
        hasMixed = true;
    }
    return disjunct;
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

// Orders coefficient vectors lexicographically, by variable and then by value.
struct CoefficientsLess {
    bool operator()(Coefficients const & a, Coefficients const & b) const {
        return std::lexicographical_compare(a.begin(), a.end(), b.begin(), b.end(), [](auto const & x, auto const & y) {
            return x.first.x != y.first.x ? x.first.x < y.first.x : x.second < y.second;
        });
    }
};

/*
 * Brings the normal of an atom into a canonical form: coefficients sorted by variable and scaled to
 * coprime integers, by a positive factor for an inequality and so that the first coefficient is positive
 * for an equality. Scaling does not change the set the atom describes, so atoms with parallel normals end
 * up with the same coefficients and differ only in their constants.
 */
void canonicalize(LinearAtom & atom) {
    std::sort(atom.coefficients.begin(), atom.coefficients.end(),
              [](auto const & a, auto const & b) { return a.first.x < b.first.x; });
    FastRational scale(1);
    for (auto const & [var, coeff] : atom.coefficients) {
        (void)var;
        scale = lcm(scale, coeff.get_den());
    }
    FastRational divisor(0);
    for (auto const & [var, coeff] : atom.coefficients) {
        (void)var;
        divisor = gcd(divisor, absoluteValue(coeff * scale));
    }
    scale = scale / divisor;
    if (atom.equality and atom.coefficients.front().second.sign() < 0) { scale = -scale; }
    if (scale.isOne()) { return; }
    for (auto & [var, coeff] : atom.coefficients) {
        (void)var;
        coeff = coeff * scale;
    }
    atom.constant = atom.constant * scale;
}

Coefficients negated(Coefficients coefficients) {
    for (auto & entry : coefficients) { entry.second = -entry.second; }
    return coefficients;
}

/*
 * A non-empty polyhedron as its tightest constant per normal: `upper` maps a canonical normal d to the
 * least k among its atoms d.x <= k, and `equal` maps a canonical normal to the constant of its equality.
 * Two bounds d.x <= k and -d.x <= -k become the equality d.x = k, and an equality makes every bound on
 * its normal or the opposite one redundant (the polyhedron is non-empty, so that bound holds). The
 * polyhedron described is the same; only redundant atoms are gone.
 */
class RowMap {
public:
    explicit RowMap(std::vector<LinearAtom> atoms) {
        for (auto & atom : atoms) {
            canonicalize(atom);
            auto & target = atom.equality ? equal : upper;
            auto [it, inserted] = target.emplace(atom.coefficients, atom.constant);
            if (not inserted and not atom.equality and atom.constant < it->second) { it->second = atom.constant; }
        }
        std::vector<Coefficients> paired;
        for (auto const & [normal, constant] : upper) {
            if (normal.front().second.sign() < 0) { continue; } // each pair once, from its canonical side
            auto opposite = upper.find(negated(normal));
            if (opposite != upper.end() and opposite->second == -constant) { paired.push_back(normal); }
        }
        for (auto const & normal : paired) { equal.emplace(normal, upper.at(normal)); }
        for (auto const & [normal, constant] : equal) {
            (void)constant;
            upper.erase(normal);
            upper.erase(negated(normal));
        }
    }

    // Syntactic containment: every atom of `other` is implied by an atom of this polyhedron.
    bool containedIn(RowMap const & other) const {
        for (auto const & [normal, constant] : other.upper) {
            if (not impliesUpper(normal, constant)) { return false; }
        }
        for (auto const & [normal, constant] : other.equal) {
            auto it = equal.find(normal);
            if (it == equal.end() or it->second != constant) { return false; }
        }
        return true;
    }

    std::vector<LinearAtom> atoms() const {
        std::vector<LinearAtom> result;
        for (auto const & [normal, constant] : equal) { result.push_back(LinearAtom{normal, constant, true}); }
        for (auto const & [normal, constant] : upper) { result.push_back(LinearAtom{normal, constant, false}); }
        return result;
    }

    // The least k such that some atom of this polyhedron states normal.x <= k, if any does.
    std::optional<FastRational> upperBound(Coefficients const & normal) const {
        std::optional<FastRational> bound;
        if (auto it = upper.find(normal); it != upper.end()) { bound = it->second; }
        bool const canonical = normal.front().second.sign() > 0;
        if (auto eq = equal.find(canonical ? normal : negated(normal)); eq != equal.end()) {
            FastRational const value = canonical ? eq->second : -eq->second;
            if (not bound or value < *bound) { bound = value; }
        }
        return bound;
    }

private:
    bool impliesUpper(Coefficients const & normal, FastRational const & constant) const {
        auto bound = upperBound(normal);
        return bound and *bound <= constant;
    }

    std::map<Coefficients, FastRational, CoefficientsLess> upper;
    std::map<Coefficients, FastRational, CoefficientsLess> equal;
};

/*
 * Exact reductions of the closure's inputs, which leave the hull unchanged: redundant atoms of each
 * polyhedron go (`RowMap`), and so does a polyhedron syntactically contained in another one, which adds
 * no point to the hull; of two equal ones the first is kept. Cubes expanded from one formula repeat its
 * common conjuncts, and a cube that only adds atoms to a sibling is contained in it.
 */
std::vector<std::vector<LinearAtom>> reducePolyhedra(std::vector<std::vector<LinearAtom>> polyhedra) {
    std::vector<RowMap> maps;
    for (auto & poly : polyhedra) { maps.emplace_back(std::move(poly)); }
    std::vector<bool> dropped(maps.size(), false);
    for (std::size_t i = 0; i < maps.size(); ++i) {
        for (std::size_t j = 0; j < maps.size() and not dropped[i]; ++j) {
            if (i == j or dropped[j] or not maps[i].containedIn(maps[j])) { continue; }
            bool const same = maps[j].containedIn(maps[i]);
            if (not same or j < i) { dropped[i] = true; }
        }
    }
    std::vector<std::vector<LinearAtom>> result;
    for (std::size_t i = 0; i < maps.size(); ++i) {
        if (not dropped[i]) { result.push_back(maps[i].atoms()); }
    }
    return result;
}

/*
 * Real copies of the source variables in a private QF_LRA logic. The closure is encoded there, since
 * its multipliers are rational, and redundancy is decided there, over the rationals, so that dropping
 * an atom never changes the rational polyhedron the encoding sees.
 */
class RationalCopies {
public:
    RationalCopies() : logic(opensmt::Logic_t::QF_LRA) {}

    PTRef copy(PTRef var) {
        auto it = toCopy.find(var);
        if (it != toCopy.end()) { return it->second; }
        std::string name = "cc_x_" + std::to_string(var.x);
        PTRef copied = logic.mkRealVar(name.c_str());
        toCopy.emplace(var, copied);
        toOriginal.emplace(copied, var);
        return copied;
    }

    PTRef atom(LinearAtom const & atom) {
        SRef sort = logic.getSort_real();
        vec<PTRef> summands;
        for (auto const & [var, coeff] : atom.coefficients) {
            summands.push(logic.mkTimes(logic.mkConst(sort, coeff), copy(var)));
        }
        PTRef lhs = summands.size() == 1 ? summands[0] : logic.mkPlus(summands);
        PTRef rhs = logic.mkConst(sort, atom.constant);
        return atom.equality ? logic.mkEq(lhs, rhs) : logic.mkLeq(lhs, rhs);
    }

    ArithLogic logic;
    std::unordered_map<PTRef, PTRef, PTRefHash> toCopy;
    std::unordered_map<PTRef, PTRef, PTRefHash> toOriginal;
};

/*
 * Which conjuncts to keep so that none is implied by the others, the conjunction staying equivalent.
 * Greedy, in order: a conjunct is checked against the ones kept so far and the ones not checked yet,
 * so the result is irredundant. Each conjunct sits behind an activation literal, asserted once; a check
 * enables the other kept ones and the negated conjunct in a pushed frame.
 */
std::vector<bool> irredundant(Logic & logic, std::vector<PTRef> const & conjuncts) {
    std::vector<bool> keep(conjuncts.size(), true);
    if (conjuncts.size() < 2) { return keep; }
    SMTSolver solver(logic, SMTSolver::WitnessProduction::NONE);
    std::vector<PTRef> activation;
    for (std::size_t i = 0; i < conjuncts.size(); ++i) {
        std::string name = "cc_on_" + std::to_string(i);
        activation.push_back(logic.mkBoolVar(name.c_str()));
        solver.assertProp(logic.mkImpl(activation.back(), conjuncts[i]));
    }
    for (std::size_t i = 0; i < conjuncts.size(); ++i) {
        solver.push();
        for (std::size_t j = 0; j < conjuncts.size(); ++j) {
            if (j != i and keep[j]) { solver.assertProp(activation[j]); }
        }
        solver.assertProp(logic.mkNot(conjuncts[i]));
        keep[i] = solver.check() != SMTSolver::Answer::UNSAT;
        solver.pop();
    }
    return keep;
}

// The atoms of `poly` that no other atom of it implies, over the rationals.
void dropImpliedAtoms(RationalCopies & copies, std::vector<LinearAtom> & poly) {
    if (poly.size() < 2) { return; }
    std::vector<PTRef> terms;
    for (auto const & atom : poly) { terms.push_back(copies.atom(atom)); }
    auto keep = irredundant(copies.logic, terms);
    std::vector<LinearAtom> kept;
    for (std::size_t i = 0; i < poly.size(); ++i) {
        if (keep[i]) { kept.push_back(std::move(poly[i])); }
    }
    poly = std::move(kept);
}

/*
 * Merges the atoms of a closure on parallel normals into the tightest one (`RowMap`). Each round of the
 * elimination contributes the literals it found implied, so the same facet recurs with different
 * constants; the merged polyhedron is the same, and its atoms are what the next closures over pobs built
 * from it start with. A result that is not a conjunction of linear atoms is returned unchanged.
 */
PTRef mergeParallelAtoms(ArithLogic & logic, PTRef hull) {
    std::vector<LinearAtom> atoms;
    for (PTRef conj : TermUtils(logic).getTopLevelConjuncts(hull)) {
        PTRef lit = conj;
        bool const negated = logic.isNot(conj);
        if (negated) { lit = logic.getPterm(conj)[0]; }
        if (not isArithmeticRelation(logic, lit)) { return hull; }
        auto atom = normalizeArithmeticLiteral(logic, lit, negated);
        if (not atom or atom->coefficients.empty()) { return hull; }
        atoms.push_back(std::move(*atom));
    }
    if (atoms.size() < 2) { return hull; }
    return polyhedronToTerm(logic, RowMap(std::move(atoms)).atoms());
}

// The satisfiable inputs of a closure: their polyhedra, reduced, and the Boolean conjuncts they all share.
struct Inputs {
    bool satisfiable = false;       // some input is satisfiable
    bool arithUnconstrained = false; // some satisfiable input constrains no arithmetic variable
    std::vector<PTRef> sharedBoolConjuncts;
    std::vector<std::vector<LinearAtom>> polyhedra;
};

Inputs collectInputs(ArithLogic & logic, std::vector<Disjunct> disjuncts, RationalCopies * copies) {
    Inputs inputs;
    for (auto & disjunct : disjuncts) {
        if (not disjunct.polyhedron.empty() or not disjunct.boolConjuncts.empty()) {
            // The syntactic convex closure is exact only for non-empty polyhedra: for an empty one the
            // sigma_i = 0 case still admits its recession cone and would add spurious directions.
            // The Boolean conjuncts take part in the check as well, so an input that only its Boolean
            // part makes unsatisfiable contributes neither its conjuncts nor its polyhedron.
            SMTSolver solver(logic, SMTSolver::WitnessProduction::NONE);
            if (not disjunct.polyhedron.empty()) { solver.assertProp(polyhedronToTerm(logic, disjunct.polyhedron)); }
            for (PTRef conj : disjunct.boolConjuncts) { solver.assertProp(conj); }
            if (solver.check() == SMTSolver::Answer::UNSAT) { continue; }
        }

        if (not inputs.satisfiable) {
            // The order of the first surviving input decides the order of the result.
            inputs.sharedBoolConjuncts = disjunct.boolConjuncts;
            inputs.satisfiable = true;
        } else {
            std::unordered_set<PTRef, PTRefHash> present(disjunct.boolConjuncts.begin(), disjunct.boolConjuncts.end());
            auto & shared = inputs.sharedBoolConjuncts;
            shared.erase(std::remove_if(shared.begin(), shared.end(),
                                        [&present](PTRef conj) { return present.find(conj) == present.end(); }),
                         shared.end());
        }

        if (disjunct.polyhedron.empty()) {
            inputs.arithUnconstrained = true;
        } else {
            inputs.polyhedra.push_back(std::move(disjunct.polyhedron));
        }
    }
    inputs.polyhedra = reducePolyhedra(std::move(inputs.polyhedra));
    if (copies) {
        for (auto & poly : inputs.polyhedra) { dropImpliedAtoms(*copies, poly); }
    }
    return inputs;
}

} // namespace

ConvexClosure::ConvexClosure(Logic & logic, QEOptions options, std::size_t maxCubesPerFormula, bool dropImplied)
    : logic(logic), options(options), maxCubesPerFormula(maxCubesPerFormula), dropImplied(dropImplied) {
    if (not options.compute_overapproximation) {
        throw std::invalid_argument(
            "ConvexClosure requires QEOptions::compute_overapproximation to be set");
    }
    if (options.max_disjunctions_in_over != 1) {
        throw std::invalid_argument(
            "ConvexClosure requires QEOptions::max_disjunctions_in_over to be 1");
    }
}

PTRef ConvexClosure::getConvexClosure(vec<PTRef> const & formulas) {
    auto * arithLogic = dynamic_cast<ArithLogic *>(&logic);
    if (not arithLogic) { throw std::logic_error("ConvexClosure currently supports only arithmetic logics"); }
    if (formulas.size() == 0) { return logic.getTerm_true(); }

    // Split every input into its arithmetic polyhedron and its Boolean conjuncts. A formula holding
    // a conjunct that mixes the two is expanded into its cubes when the budget allows it, so that
    // the Boolean case split becomes several inputs instead of being thrown away.
    std::vector<Disjunct> disjuncts;
    for (PTRef formula : formulas) {
        PTRef nnf = dropDisequalityClauses(*arithLogic, TermUtils(logic).toNNF(formula));
        bool hasMixed = false;
        auto disjunct = buildDisjunct(*arithLogic, nnf, hasMixed);
        if (hasMixed) { fprintf(stderr, "@@CC_MIXED@@\n"); }
        if (hasMixed and maxCubesPerFormula > 0) {
            std::unordered_map<PTRef, std::size_t, PTRefHash> memo;
            if (countCubes(logic, nnf, maxCubesPerFormula, memo) <= maxCubesPerFormula) {
                fprintf(stderr, "@@CC_EXPANDED@@\n");
                for (PTRef cube : TermUtils(logic).getTopLevelDisjuncts(TermUtils(logic).toDNF(nnf))) {
                    bool cubeHasMixed = false;
                    auto expandedCube = buildDisjunct(*arithLogic, cube, cubeHasMixed);
                    assert(not cubeHasMixed);
                    if (expandedCube) { disjuncts.push_back(std::move(*expandedCube)); }
                }
                continue;
            }
        }
        if (disjunct) { disjuncts.push_back(std::move(*disjunct)); }
    }

    // Keep the satisfiable inputs, reduce their polyhedra, and intersect their Boolean conjuncts.
    RationalCopies copies;
    Inputs inputs = collectInputs(*arithLogic, std::move(disjuncts), dropImplied ? &copies : nullptr);

    // Every input formula is unsatisfiable, so is their disjunction.
    if (not inputs.satisfiable) { return logic.getTerm_false(); }

    // Every conjunct left here is a conjunct of each satisfiable input, hence it holds in their
    // union: conjoining it to the closure is sound, and it is all that is left of the Boolean part.
    PTRef sharedBool = logic.getTerm_true();
    {
        vec<PTRef> conjuncts;
        for (PTRef conj : inputs.sharedBoolConjuncts) { conjuncts.push(conj); }
        if (conjuncts.size() > 0) { sharedBool = logic.mkAnd(std::move(conjuncts)); }
    }

    // A satisfiable input that constrains no arithmetic variable makes the arithmetic part of the
    // closure unconstrained; the shared Boolean part is still valid.
    if (inputs.arithUnconstrained) { return sharedBool; }

    std::vector<std::vector<LinearAtom>> & polyhedra = inputs.polyhedra;

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
    if (variables.empty()) { return sharedBool; }

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

    // The hull of a single polyhedron is that polyhedron.
    if (polyhedra.size() == 1) { return logic.mkAnd(sharedBool, polyhedronToTerm(*arithLogic, polyhedra.front())); }

    // The syntactic convex closure needs rational multipliers, so the encoding is always built in a
    // private LRA logic over shadow copies of the original variables. Over the integers this is the
    // rational relaxation of the convex closure, which still over-approximates the union; the result
    // is mapped back to integer atoms (and tightened) by `BackTranslator`.
    ArithLogic & encodingLogic = copies.logic;
    SRef encodingSort = encodingLogic.getSort_real();
    auto encodingConst = [&](FastRational const & value) { return encodingLogic.mkConst(encodingSort, value); };

    std::unordered_map<PTRef, std::size_t, PTRefHash> variableIndex;
    std::vector<PTRef> shadowVariables;
    for (std::size_t j = 0; j < variables.size(); ++j) {
        variableIndex[variables[j]] = j;
        shadowVariables.push_back(copies.copy(variables[j]));
    }
    std::unordered_map<PTRef, PTRef, PTRefHash> shadowToOriginal = copies.toOriginal;

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
    QEResult result = qe.eliminate(closureFormula, varsToEliminate, options);
    // The encoding is a cube, so the disjunction budget of 1 costs nothing; without a projection
    // budget the inner loop also runs to completion. The elimination is then exact.
    assert(options.max_mbp_per_poly > 0 or result.precise_over);
    if (result.over == PTRef_Undef) { return sharedBool; }

    // Anything the elimination failed to remove cannot be expressed in the source logic; giving up
    // and returning the trivial over-approximation is always sound.
    for (PTRef var : TermUtils(encodingLogic).getVars(result.over)) {
        if (shadowToOriginal.find(var) == shadowToOriginal.end()) { return sharedBool; }
    }

    PTRef over = result.over;
    if (dropImplied) {
        auto const conjuncts = TermUtils(encodingLogic).getTopLevelConjuncts(over);
        std::vector<PTRef> terms(conjuncts.begin(), conjuncts.end());
        auto keep = irredundant(encodingLogic, terms);
        vec<PTRef> kept;
        for (std::size_t i = 0; i < terms.size(); ++i) {
            if (keep[i]) { kept.push(terms[i]); }
        }
        over = encodingLogic.mkAnd(std::move(kept));
    }
    BackTranslator translator(encodingLogic, *arithLogic, std::move(shadowToOriginal), integers);
    return logic.mkAnd(sharedBool, mergeParallelAtoms(*arithLogic, translator.translate(over)));
}

} // namespace golem
