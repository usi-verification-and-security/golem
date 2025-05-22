/*
 * Copyright (c) 2020-2025, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "TermUtils.h"

namespace golem {
namespace {
struct ShiftedVar {
    PTRef var;
    PTRef shift;
};
std::optional<ShiftedVar> tryAsShiftedVar(PTRef term, ArithLogic & logic) {
    if (not logic.yieldsSortNum(term)) { return std::nullopt; }
    if (logic.isVar(term)) { return ShiftedVar{.var = term, .shift = logic.getZeroForSort(logic.getSortRef(term))}; }
    if (logic.isPlus(term)) {
        auto const & pterm = logic.getPterm(term);
        if (pterm.size() != 2) { return std::nullopt; }
        PTRef arg1 = pterm[0];
        PTRef arg2 = pterm[1];
        if (logic.isVar(arg1) and logic.isNumConst(arg2)) { return ShiftedVar{.var = arg1, .shift = arg2}; }
        if (logic.isVar(arg2) and logic.isNumConst(arg1)) { return ShiftedVar{.var = arg2, .shift = arg1}; }
        return std::nullopt;
    }
    return std::nullopt;
}

template<typename TKeep> PTRef tryEliminateVars(PTRef fla, Logic & logic, TKeep shouldKeepVar) {
    ArithLogic & arithLogic = dynamic_cast<ArithLogic &>(logic);
    auto res = TermUtils(logic).extractSubstitutionsAndSimplify(fla);
    PTRef simplifiedFormula = res.result;
    auto & substitutions = res.substitutionsUsed;
    logic.substitutionsTransitiveClosure(substitutions);
    // Substitutions where key is TBE (to be eliminated) var can be simply dropped.
    // Others need to be brought back.
    // If there is a TBE variable on RHS, we should revert the substitution so that this TBE var is eliminated instead.
    // For now we only revert if RHS is exactly TBE var
    Logic::SubstMap substitutionsToReapply;
    vec<PTRef> equalitiesToRestore;
    std::size_t nonvarKeys = 0;
    std::unordered_set<PTRef, PTRefHash> eliminatedVars;
    // std::cout << "====================================\n";
    for (auto const & key : substitutions.getKeys()) {
        //        std::cout << logic.pp(key) << " -> " << logic.pp(substitutions[key]) << std::endl;
        if (not logic.isVar(key)) { // TODO: Handle array terms (selects) properly in substitutions
            equalitiesToRestore.push(logic.mkEq(key, substitutions[key]));
            ++nonvarKeys;
            continue;
        }
        if (shouldKeepVar(key)) {
            // If it is not a variable we wanted to eliminate, we need to insert back the equality
            // Unless we can extract TBE var from the RHS
            PTRef rhs = substitutions[key];
            auto canUseVarForSubstitution = [&](PTRef var) {
                assert(arithLogic.isVar(var));
                return not shouldKeepVar(var) and not substitutionsToReapply.has(var);
            };
            if (logic.isVar(rhs) and canUseVarForSubstitution(rhs)) {
                substitutionsToReapply.insert(rhs, key);
                continue;
            }
            if (auto shiftedVar = tryAsShiftedVar(rhs, arithLogic);
                shiftedVar and canUseVarForSubstitution(shiftedVar->var)) {
                substitutionsToReapply.insert(shiftedVar->var, arithLogic.mkMinus(key, shiftedVar->shift));
                continue;
            }
            equalitiesToRestore.push(logic.mkEq(key, rhs));
            continue;
        } else { // Substitution of TBE var. Can ignore if Bool or Real var
            if (arithLogic.yieldsSortInt(key)) {
                // MB: Integer equalities can bear information about divisibility constraints
                //     We need to keep this information
                PTRef rhs = substitutions[key];
                Pterm const & term = logic.getPterm(rhs);
                // TODO: This should not be needed anymore with OpenSMT 2.9
                if (std::any_of(term.begin(), term.end(), [&](PTRef arg) {
                        auto varConstant = arithLogic.splitTermToVarAndConst(arg);
                        return not arithLogic.getNumConst(varConstant.second).isInteger();
                    })) { // There are some fractions on the RHS, better keep this substitution, just in case
                    equalitiesToRestore.push(logic.mkEq(key, rhs));
                    continue;
                }
            }
            eliminatedVars.insert(key);
        }
    }
    // std::cout << "====================================\n";
    if (equalitiesToRestore.size() > 0) {
        equalitiesToRestore.push(simplifiedFormula);
        simplifiedFormula = logic.mkAnd(std::move(equalitiesToRestore));
    }
    if (nonvarKeys > 0) {
        for (PTRef var : eliminatedVars) {
            substitutionsToReapply.insert(var, substitutions[var]);
        }
    }
    if (substitutionsToReapply.getSize() > 0) {
        logic.substitutionsTransitiveClosure(substitutionsToReapply);
        simplifiedFormula = Substitutor(logic, substitutionsToReapply).rewrite(simplifiedFormula);
    }
    // std::cout << logic.pp(simplifiedFormula) << std::endl;
    return simplifiedFormula;
}
} // namespace

PTRef TrivialQuantifierElimination::tryEliminateVars(vec<PTRef> const & vars, PTRef fla) const {
    if (vars.size() == 0) { return fla; }
    return golem::tryEliminateVars(fla, logic,
                                   [&](PTRef var) { return std::find(vars.begin(), vars.end(), var) == vars.end(); });
}

PTRef TrivialQuantifierElimination::tryEliminateVarsExcept(vec<PTRef> const & vars, PTRef fla) const {
    return golem::tryEliminateVars(fla, logic,
                                   [&](PTRef var) { return std::find(vars.begin(), vars.end(), var) != vars.end(); });
}

PTRef TrivialQuantifierElimination::tryEliminateVarsExcept(std::vector<PTRef> const & vars, PTRef fla) const {
    return golem::tryEliminateVars(fla, logic,
                                   [&](PTRef var) { return std::find(vars.begin(), vars.end(), var) != vars.end(); });
}

PTRef LATermUtils::expressZeroTermFor(PTRef zeroTerm, PTRef var) {
    assert(logic.isLinearTerm(zeroTerm) and logic.isNumVar(var));
    assert(termContainsVar(zeroTerm, var));
    SRef sortRef = logic.getSortRef(zeroTerm);
    // split the zeroTerm to the factor with the variable 'var' and rest
    if (logic.isLinearFactor(zeroTerm)) {
        // simple case of 'c * v = 0', the resulting term is simply zero
        return logic.getZeroForSort(sortRef);
    } else {
        assert(logic.isPlus(zeroTerm));
        PTRef varCoeff = PTRef_Undef;
        vec<PTRef> otherFactors;
        auto size = logic.getPterm(zeroTerm).size();
        for (int i = 0; i < size; ++i) {
            PTRef factor = logic.getPterm(zeroTerm)[i];
            assert(logic.isLinearFactor(factor));
            auto [factorVar, coeff] = logic.splitTermToVarAndConst(factor);
            if (factorVar == var) {
                varCoeff = coeff;
            } else {
                otherFactors.push(factor);
            }
        }
        assert(varCoeff != PTRef_Undef);
        // now we have 't = 0' where 't = c * var + t1' => 'var = t1/-c'logic.mkC
        PTRef res = logic.mkTimes(logic.mkPlus(otherFactors),
                                  logic.mkConst(sortRef, FastRational(-1) / logic.getNumConst(varCoeff)));
        return res;
    }
}

void TermUtils::printTermWithLets(std::ostream & out, PTRef root) {
    // true means parent and we should put it in the order; false means child and we should process it
    struct Entry {
        PTRef node;
        bool treatAsParent;
    };
    // collect mapping of id to let expressions
    auto toLetId = [](PTRef x) -> std::string { return "l" + std::to_string(x.x); };
    std::vector<PTRef> dfsOrder;
    std::vector<Entry> queue;
    std::unordered_set<PTRef, PTRefHash> visited;
    queue.push_back({root, false});
    while (not queue.empty()) {
        auto current = queue.back();
        queue.pop_back();
        if (current.treatAsParent) {
            dfsOrder.push_back(current.node);
            continue;
        }
        PTRef ref = current.node;
        visited.insert(ref);
        queue.push_back({ref, true});
        Pterm const & pterm = logic.getPterm(ref);
        for (PTRef child : pterm) {
            if (visited.find(child) == visited.end()) { queue.push_back({child, false}); }
        }
    }

    std::unordered_map<PTRef, std::string, PTRefHash> strRepr;

    auto toStr = [this, &strRepr](PTRef ref) -> std::string {
        Pterm const & pterm = logic.getPterm(ref);
        SymRef symbol = pterm.symb();
        if (pterm.size() == 0) {
            if (auto * arithLogic = dynamic_cast<ArithLogic *>(&logic); arithLogic and arithLogic->isNumConst(symbol)) {
                // TODO: OpenSMT should override printSym in ArithLogic in a similar manner it overrides printTerm
                return logic.printTerm(ref);
            }
            return logic.printSym(symbol);
        }
        std::stringstream ss;
        ss << '(' << logic.printSym(symbol) << ' ';
        for (PTRef child : pterm) {
            ss << strRepr.at(child) << ' ';
        }
        ss << ')';
        return ss.str();
    };

    int letCount = 0;
    for (PTRef ref : dfsOrder) {
        auto actualRepr = toStr(ref);
        bool introduceLet = logic.isAnd(ref) or logic.isOr(ref);
        if (introduceLet) {
            out << "(let " << '(' << '(' << toLetId(ref) << ' ' << actualRepr << ')' << ')';
            strRepr.insert({ref, toLetId(ref)});
            ++letCount;
        } else {
            strRepr.insert({ref, std::move(actualRepr)});
        }
    }
    out << strRepr.at(root) << std::string(letCount, ')');
}

// TODO: Make this available in OpenSMT?
TermUtils::SimplificationResult TermUtils::extractSubstitutionsAndSimplify(PTRef fla) {
    SimplificationResult result;
    PTRef root = fla;
    Logic::SubstMap allsubsts;
    while (true) {
        PTRef simp_formula = root;
        MapWithKeys<PTRef, lbool, PTRefHash> new_units;
        vec<PtAsgn> current_units_vec;
        logic.getNewFacts(simp_formula, new_units);
        const auto & new_units_vec = new_units.getKeys();
        for (PTRef key : new_units_vec) {
            current_units_vec.push(PtAsgn{key, new_units[key]});
        }

        auto [res, newsubsts] = logic.retrieveSubstitutions(current_units_vec);
        logic.substitutionsTransitiveClosure(newsubsts);

        for (PTRef key : newsubsts.getKeys()) {
            if (!allsubsts.has(key)) {
                const auto target = newsubsts[key];
                allsubsts.insert(key, target);
            }
        }

        if (res != l_Undef) root = (res == l_True ? logic.getTerm_true() : logic.getTerm_false());

        PTRef new_root = Substitutor(logic, newsubsts).rewrite(root);

        bool cont = new_root != root;
        root = new_root;
        if (!cont) break;
    }

    result.result = root;
    result.substitutionsUsed = std::move(allsubsts);
    return result;
}

class NNFTransformer {
    Logic & logic;

    std::unordered_map<PTRef, PTRef, PTRefHash> transformed;
    std::unordered_map<PTRef, PTRef, PTRefHash> negated;

    PTRef transform(PTRef);
    PTRef negate(PTRef);

public:
    NNFTransformer(Logic & logic) : logic(logic) {}

    PTRef toNNF(PTRef fla) { return transform(fla); };
};

PTRef NNFTransformer::transform(PTRef fla) {
    auto it = transformed.find(fla);
    if (it != transformed.end()) { return it->second; }
    if (logic.isAtom(fla)) {
        transformed.insert({fla, fla});
        return fla;
    }
    if (logic.isAnd(fla)) {
        auto size = logic.getPterm(fla).size();
        vec<PTRef> nargs;
        nargs.capacity(size);
        for (int i = 0; i < size; ++i) {
            PTRef child = logic.getPterm(fla)[i];
            nargs.push(transform(child));
        }
        PTRef nfla = logic.mkAnd(nargs);
        transformed.insert({fla, nfla});
        return nfla;
    }
    if (logic.isOr(fla)) {
        auto size = logic.getPterm(fla).size();
        vec<PTRef> nargs;
        nargs.capacity(size);
        for (int i = 0; i < size; ++i) {
            PTRef child = logic.getPterm(fla)[i];
            nargs.push(transform(child));
        }
        PTRef nfla = logic.mkOr(nargs);
        transformed.insert({fla, nfla});
        return nfla;
    }
    if (logic.isNot(fla)) {
        PTRef npos = transform(logic.getPterm(fla)[0]);
        PTRef nfla = negate(npos);
        transformed.insert({fla, nfla});
        return nfla;
    }
    if (logic.getSymRef(fla) == logic.getSym_eq()) { // Boolean equality
        // a <=> b iff (~a or b) and (~b or a)
        assert(logic.getPterm(fla).size() == 2);
        PTRef firstTransformed = transform(logic.getPterm(fla)[0]);
        PTRef secondTransformed = transform(logic.getPterm(fla)[1]);
        PTRef firstTransformNegated = negate(firstTransformed);
        PTRef secondTransformNegated = negate(secondTransformed);
        PTRef nfla = logic.mkAnd(logic.mkOr(firstTransformNegated, secondTransformed),
                                 logic.mkOr(secondTransformNegated, firstTransformed));
        transformed.insert({fla, nfla});
        return nfla;
    }
    assert(false);
    throw std::logic_error("Unexpected formula in NNF transformation");
}

PTRef NNFTransformer::negate(PTRef fla) {
    assert(logic.isAnd(fla) or logic.isOr(fla) or logic.isAtom(fla) or
           (logic.isNot(fla) and logic.isAtom(logic.getPterm(fla)[0])));
    auto it = negated.find(fla);
    if (it != negated.end()) { return it->second; }
    if (logic.isNot(fla)) {
        assert(logic.isAtom(logic.getPterm(fla)[0]));
        PTRef nfla = logic.getPterm(fla)[0];
        negated.insert({fla, nfla});
        return nfla;
    }
    if (logic.isAtom(fla)) {
        PTRef nfla = logic.mkNot(fla);
        negated.insert({fla, nfla});
        return nfla;
    }
    if (logic.isAnd(fla)) {
        auto size = logic.getPterm(fla).size();
        vec<PTRef> nargs;
        nargs.capacity(size);
        for (int i = 0; i < size; ++i) {
            PTRef child = logic.getPterm(fla)[i];
            nargs.push(negate(child));
        }
        PTRef nfla = logic.mkOr(nargs);
        negated.insert({fla, nfla});
        return nfla;
    }
    if (logic.isOr(fla)) {
        auto size = logic.getPterm(fla).size();
        vec<PTRef> nargs;
        nargs.capacity(size);
        for (int i = 0; i < size; ++i) {
            PTRef child = logic.getPterm(fla)[i];
            nargs.push(negate(child));
        }
        PTRef nfla = logic.mkAnd(nargs);
        negated.insert({fla, nfla});
        return nfla;
    }
    assert(false);
    throw std::logic_error("Unexpected formula in NNF transformation");
}

PTRef TermUtils::toNNF(PTRef fla) {
    if (not logic.hasSortBool(fla)) { throw std::invalid_argument("toNNF called with non-boolean formula!"); }
    NNFTransformer nnfTransformer(logic);
    return nnfTransformer.toNNF(fla);
}

PTRef TermUtils::conjoin(PTRef what, PTRef to) {
    auto args = getTopLevelConjuncts(to);
    args.push(what);
    return logic.mkAnd(args);
}

bool LATermUtils::termContainsVar(PTRef term, PTRef var) {
    assert(logic.isLinearTerm(term));
    auto getVarFromFactor = [this](PTRef factor) {
        auto [fvar, constant] = logic.splitTermToVarAndConst(factor);
        return fvar;
    };
    if (logic.isLinearFactor(term)) {
        return getVarFromFactor(term) == var;
    } else {
        assert(logic.isPlus(term));
        for (int i = 0; i < logic.getPterm(term).size(); ++i) {
            PTRef factor = logic.getPterm(term)[i];
            PTRef factorVar = getVarFromFactor(factor);
            if (factorVar == var) { return true; }
        }
        return false;
    }
}

bool LATermUtils::atomContainsVar(PTRef atom, PTRef var) {
    if (logic.isBoolAtom(atom) or logic.isConstant(atom)) { return false; }
    assert(logic.isLeq(atom) || logic.isNumEq(atom));
    if (logic.isNumEq(atom)) {
        PTRef lhs = logic.getPterm(atom)[0];
        PTRef rhs = logic.getPterm(atom)[1];
        assert(logic.isLinearTerm(lhs) and logic.isLinearTerm(rhs));
        return termContainsVar(lhs, var) or termContainsVar(rhs, var);
    } else {
        // inequalities have form "constant <= term"
        PTRef term = logic.getPterm(atom)[1];
        return termContainsVar(term, var);
    }
}

PTRef LATermUtils::simplifyDisjunction(PTRef fla) {
    if (not logic.isOr(fla)) { return fla; }
    std::vector<PtAsgn> disjuncts;
    auto nargs = logic.getPterm(fla).size();
    disjuncts.reserve(nargs);
    for (int i = 0; i < nargs; ++i) {
        PTRef child = logic.getPterm(fla)[i];
        PtAsgn polarTerm(child, l_True);
        if (logic.isNot(child)) {
            polarTerm.sgn = l_False;
            polarTerm.tr = logic.getPterm(child)[0];
        }
        disjuncts.push_back(polarTerm);
    }
    simplifyDisjunction(disjuncts);
    vec<PTRef> args;
    args.capacity(disjuncts.size());
    for (PtAsgn lit : disjuncts) {
        args.push(lit.sgn == l_False ? logic.mkNot(lit.tr) : lit.tr);
    }
    return logic.mkOr(std::move(args));
}

PTRef LATermUtils::simplifyConjunction(PTRef fla) {
    if (not logic.isAnd(fla)) { return fla; }
    std::vector<PtAsgn> conjuncts;
    auto nargs = logic.getPterm(fla).size();
    conjuncts.reserve(nargs);
    for (int i = 0; i < nargs; ++i) {
        PTRef child = logic.getPterm(fla)[i];
        PtAsgn polarTerm(child, l_True);
        if (logic.isNot(child)) {
            polarTerm.sgn = l_False;
            polarTerm.tr = logic.getPterm(child)[0];
        }
        conjuncts.push_back(polarTerm);
    }
    simplifyConjunction(conjuncts);
    vec<PTRef> args;
    args.capacity(conjuncts.size());
    for (PtAsgn lit : conjuncts) {
        args.push(lit.sgn == l_False ? logic.mkNot(lit.tr) : lit.tr);
    }
    return logic.mkAnd(std::move(args));
}

namespace {
struct Conjunction {};
struct Disjunction {};

template<typename T> struct JunctionTraits {
    static bool isBetterLowerBound(FastRational const & first, FastRational const & second) = delete;
    static bool isBetterUpperBound(FastRational const & first, FastRational const & second) = delete;
};

template<> struct JunctionTraits<Conjunction> {
    static bool isBetterLowerBound(FastRational const & first, FastRational const & second) {
        return first > second;
    } // higher is stronger
    static bool isBetterUpperBound(FastRational const & first, FastRational const & second) {
        return first < second;
    } // lower is stronger
};

template<> struct JunctionTraits<Disjunction> {
    static bool isBetterLowerBound(FastRational const & first, FastRational const & second) {
        return first < second;
    } // lower is weaker
    static bool isBetterUpperBound(FastRational const & first, FastRational const & second) {
        return first > second;
    } // higher is weaker
};

template<typename T> void simplifyJunction(std::vector<PtAsgn> & juncts, ArithLogic & logic) {
    std::vector<PtAsgn> tmp;
    tmp.reserve(juncts.size());
    MapWithKeys<PtAsgn, PTRef, PtAsgnHash> bounds;
    for (PtAsgn literal : juncts) {
        auto sign = literal.sgn;
        PTRef ineq = literal.tr;
        if (not logic.isLeq(ineq)) {
            tmp.push_back(literal);
            continue;
        }
        auto pair = logic.leqToConstantAndTerm(ineq);
        PTRef constant = pair.first;
        PTRef term = pair.second;
        assert(logic.isConstant(constant) and logic.isLinearTerm(term));
        PtAsgn key(term, sign);
        PTRef currentValue;
        if (bounds.peek(key, currentValue)) {
            if (sign == l_True) { // positive literal -> lower bound
                if (JunctionTraits<T>::isBetterLowerBound(logic.getNumConst(constant),
                                                          logic.getNumConst(currentValue))) {
                    bounds[key] = constant;
                }
            } else {
                assert(sign == l_False);
                // negative literal -> upper bound
                if (JunctionTraits<T>::isBetterUpperBound(logic.getNumConst(constant),
                                                          logic.getNumConst(currentValue))) {
                    bounds[key] = constant;
                }
            }
        } else {
            bounds.insert(key, constant);
        }
    }
    auto const & keys = bounds.getKeys();
    if (keys.size() + tmp.size() < juncts.size()) { // something actually changed
        for (PtAsgn key : keys) {
            tmp.push_back(PtAsgn(logic.mkLeq(bounds[key], key.tr), key.sgn));
        }
        juncts = std::move(tmp);
    }
}
} // namespace

void LATermUtils::simplifyDisjunction(std::vector<PtAsgn> & disjuncts) {
    simplifyJunction<Disjunction>(disjuncts, logic);
}

void LATermUtils::simplifyConjunction(std::vector<PtAsgn> & conjuncts) {
    simplifyJunction<Conjunction>(conjuncts, logic);
}

PTRef TimeMachine::versionedFormulaToUnversioned(PTRef fla) const {
    class Config : public DefaultRewriterConfig {
        Logic const & logic;
        TimeMachine const & tm;

    public:
        Config(Logic const & logic, TimeMachine const & tm) : logic(logic), tm(tm) {}

        PTRef rewrite(PTRef term) override {
            if (logic.isVar(term)) {
                if (tm.isVersioned(term)) { return tm.getUnversioned(term); }
            }
            return term;
        }
    };
    Config config(logic, *this);
    Rewriter<Config> rewriter(logic, config);
    return rewriter.rewrite(fla);
}

//********** CANONICAL PREDICATE REPRESENTATION ********************/
void NonlinearCanonicalPredicateRepresentation::addRepresentation(SymRef sym, std::vector<PTRef> vars) {
    assert(not hasRepresentationFor(sym));
    VersionManager manager(logic);
    vec<PTRef> sourceVars(vars.size());
    std::transform(vars.begin(), vars.end(), sourceVars.begin(),
                   [&manager](PTRef var) { return manager.toSource(var); });
    PTRef sourceTerm = logic.insertTerm(sym, std::move(sourceVars));
    assert(sourceTermsByInstance.size() >= 1);
    this->sourceTermsByInstance[0].insert({sym, sourceTerm});

    vec<PTRef> targetVars(vars.size());
    std::transform(vars.begin(), vars.end(), targetVars.begin(),
                   [&manager](PTRef var) { return manager.toTarget(var); });
    PTRef targetTerm = logic.insertTerm(sym, std::move(targetVars));
    this->targetTerms.insert({sym, targetTerm});

    this->representation.insert({sym, std::move(vars)});
}

PTRef NonlinearCanonicalPredicateRepresentation::getTargetTermFor(SymRef sym) const {
    assert(targetTerms.count(sym) > 0);
    return targetTerms.at(sym);
}

PTRef NonlinearCanonicalPredicateRepresentation::getSourceTermFor(SymRef sym, unsigned instanceCount) const {
    if (instanceCount >= sourceTermsByInstance.size()) { sourceTermsByInstance.resize(instanceCount + 1); }
    auto & terms = sourceTermsByInstance[instanceCount];
    auto it = terms.find(sym);
    if (it != terms.end()) { return it->second; }
    // Create new representation for this instance
    auto const & vars = representation.at(sym);
    vec<PTRef> nVars(vars.size());
    std::transform(vars.begin(), vars.end(), nVars.begin(),
                   [this, instanceCount](PTRef var) { return VersionManager(logic).toSource(var, instanceCount); });
    PTRef instanceSourceTerm = logic.insertTerm(sym, std::move(nVars));
    terms.insert({sym, instanceSourceTerm});
    return instanceSourceTerm;
}

void LinearCanonicalPredicateRepresentation::addRepresentation(SymRef sym, std::vector<PTRef> vars) {
    assert(not hasRepresentationFor(sym));
    TimeMachine timeMachine(logic);
    vec<PTRef> sourceVars(vars.size());
    std::transform(vars.begin(), vars.end(), sourceVars.begin(),
                   [&timeMachine](PTRef var) { return timeMachine.getVarVersionZero(var); });
    PTRef sourceTerm = logic.insertTerm(sym, std::move(sourceVars));
    sourceTerms.insert({sym, sourceTerm});

    vec<PTRef> targetVars(vars.size());
    std::transform(vars.begin(), vars.end(), targetVars.begin(), [&timeMachine](PTRef var) {
        return timeMachine.sendVarThroughTime(timeMachine.getVarVersionZero(var), 1);
    });
    PTRef targetTerm = logic.insertTerm(sym, std::move(targetVars));
    this->targetTerms.insert({sym, targetTerm});

    this->representation.insert({sym, std::move(vars)});
}

PTRef LinearCanonicalPredicateRepresentation::getTargetTermFor(SymRef sym) const {
    assert(targetTerms.count(sym) > 0);
    return targetTerms.at(sym);
}

PTRef LinearCanonicalPredicateRepresentation::getSourceTermFor(SymRef sym) const {
    assert(sourceTerms.count(sym) > 0);
    return sourceTerms.at(sym);
}

void VersionManager::ensureNoVersion(std::string & varName) {
    auto pos = versionPosition(varName);
    if (pos == std::string::npos) { return; }
    varName.erase(pos);
}

void VersionManager::removeTag(std::string & varName) {
    auto pos = tagPosition(varName);
    assert(pos != std::string::npos);
    varName.erase(pos);
}

PTRef VersionManager::baseFormulaToSource(PTRef fla, unsigned int instance) const {
    return rewrite(fla, [instance, this](PTRef var) { return toSource(var, instance); });
}

PTRef VersionManager::baseFormulaToTarget(PTRef fla) const {
    return rewrite(fla, [this](PTRef var) { return toTarget(var); });
}

PTRef VersionManager::sourceFormulaToBase(PTRef fla) const {
    return rewrite(fla, [this](PTRef var) { return toBase(var); });
}

PTRef VersionManager::targetFormulaToBase(PTRef fla) const {
    return rewrite(fla, [this](PTRef var) { return toBase(var); });
}

PTRef VersionManager::sourceFormulaToTarget(PTRef fla) const {
    return rewrite(fla, [this](PTRef var) { return toTarget(toBase(var)); });
}
} // namespace golem
