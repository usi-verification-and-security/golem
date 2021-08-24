//
// Created by Martin Blicha on 20.08.20.
//

#include "TermUtils.h"

/** Given an equality 'eq' containing variable 'var', try to derive a definition of 'var' from 'eq'.
    Returns the derived definition or PTRef_Undef is no definition could be derived
 */
PTRef TrivialQuantifierElimination::tryGetSubstitutionFromEquality(PTRef var, PTRef eq) const {
    assert(logic.isVar(var) and logic.isEquality(eq));
    PTRef lhs = logic.getPterm(eq)[0];
    PTRef rhs = logic.getPterm(eq)[1];
    if (logic.hasSortBool(var)) {
        // the only possibility how to get definition here is if one side of 'eq' is 'not var'
        PTRef varNeg = logic.mkNot(var);
        if (lhs == varNeg) {
            return logic.mkNot(rhs);
        }
        if (rhs == varNeg) {
            return logic.mkNot(lhs);
        }
        return PTRef_Undef;
    }
    if (logic.getLogic() == opensmt::Logic_t::QF_LIA || logic.getLogic() == opensmt::Logic_t::QF_LRA) {
        LALogic & lalogic = dynamic_cast<LALogic &>(logic);
        if (not lalogic.isNumVar(var)) {
            return PTRef_Undef;
        }
        if (logic.hasSortBool(lhs)) {
            assert(logic.hasSortBool(rhs));
            return PTRef_Undef;
        }
        PTRef zeroTerm = lalogic.mkNumMinus(lhs, rhs);
        PTRef substitutionTerm = LATermUtils(lalogic).expressZeroTermFor(zeroTerm, var);
        // For LIA we should most likely check the coefficients in the result are Integers
        if (lalogic.getLogic() == opensmt::Logic_t::QF_LIA) {
            auto hasIntegerCoeff = [&lalogic](PTRef factor) {
                assert(lalogic.isLinearFactor(factor));
                PTRef v, c;
                lalogic.splitTermToVarAndConst(factor, v, c);
                return lalogic.getNumConst(c).isInteger();
            };
            if (lalogic.isLinearFactor(substitutionTerm)) {
                if (not hasIntegerCoeff(substitutionTerm)) {
                    return PTRef_Undef;
                }
            } else {
                auto argsCount = lalogic.getPterm(substitutionTerm).size();
                for (int i = 0; i < argsCount; ++i) {
                    PTRef factor = lalogic.getPterm(substitutionTerm)[i];
                    if (not hasIntegerCoeff(factor)) {
                        return PTRef_Undef;
                    }
                }
            }
        }
        return substitutionTerm;

    }
    return PTRef_Undef;
}

PTRef LATermUtils::expressZeroTermFor(PTRef zeroTerm, PTRef var) {
    assert(logic.isLinearTerm(zeroTerm) and logic.isNumVar(var));
    assert(termContainsVar(zeroTerm, var));
    // split the zeroTerm to the factor with the variable 'var' and rest
    if (logic.isLinearFactor(zeroTerm)) {
        // simple case of 'c * v = 0', the resulting term is simply zero
        return logic.getTerm_NumZero();
    } else {
        assert(logic.isNumPlus(zeroTerm));
        PTRef varCoeff = PTRef_Undef;
        vec<PTRef> otherFactors;
        auto size = logic.getPterm(zeroTerm).size();
        for (int i = 0; i < size; ++i) {
            PTRef factor = logic.getPterm(zeroTerm)[i];
            assert(logic.isLinearFactor(factor));
            PTRef factorVar;
            PTRef coeff;
            logic.splitTermToVarAndConst(factor, factorVar, coeff);
            if (factorVar == var) {
                varCoeff = coeff;
            } else {
                otherFactors.push(factor);
            }
        }
        assert(varCoeff != PTRef_Undef);
        // now we have 't = 0' where 't = c * var + t1' => 'var = t1/-c'
        PTRef res = logic.mkNumTimes(logic.mkNumPlus(otherFactors), logic.mkConst(FastRational(-1) / logic.getNumConst(varCoeff)));
        return res;
    }
}

void TermUtils::printTermWithLets(ostream & out, PTRef root) {
    // collect mapping of id to let expressions
    auto toLetId = [](PTRef x) -> std::string { return "l" + std::to_string(x.x); };
    std::vector<PTRef> dfsOrder;
    std::vector<std::pair<bool, PTRef>> queue; // true means parent and we should put it in the order; false means child and we should process it
    std::unordered_set<PTRef, PTRefHash> visited;
    queue.push_back({false, root});
    while (not queue.empty()) {
        auto current = queue.back();
        queue.pop_back();
        if (current.first) {
            dfsOrder.push_back(current.second);
            continue;
        }
        PTRef ref = current.second;
        visited.insert(ref);
        queue.push_back({true, ref});
        Pterm const & pterm = logic.getPterm(ref);
        for (int i = 0; i < pterm.size(); ++i) {
            if (visited.find(pterm[i]) == visited.end()) {
                queue.push_back({false, pterm[i]});
            }
        }
    }

    std::unordered_map<PTRef, std::string, PTRefHash> strRepr;

    auto toStr = [this, &strRepr](PTRef ref) -> std::string {
        Pterm const & pterm = logic.getPterm(ref);
        char * symbol = logic.printSym(pterm.symb());
        if (pterm.size() == 0) {
            std::string res(symbol);
            free(symbol);
            return res;
        }
        std::stringstream ss;
        ss << '(' << symbol << ' ';
        for (int i = 0; i < pterm.size(); ++i) {
            ss << strRepr.at(pterm[i]) << ' ';
        }
        ss << ')';
        free(symbol);
        return ss.str();
    };

    int letCount = 0;
    for (PTRef ref : dfsOrder) {
        auto actualRepr = toStr(ref);
        bool introduceLet = false;
        if (logic.isAnd(ref) or logic.isOr(ref)) { introduceLet = true; }
        if (introduceLet) {
            out << "(let " << '(' << toLetId(ref) << ' ' << actualRepr << ')';
            strRepr.insert({ref, toLetId(ref)});
        } else {
            strRepr.insert({ref, std::move(actualRepr)});
        }
    }

    out << strRepr.at(root) << std::string(letCount, ')');
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
    if (it != transformed.end()) {
        return it->second;
    }
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
        PTRef nfla = logic.mkAnd(
            logic.mkOr(firstTransformNegated, secondTransformed),
            logic.mkOr(secondTransformNegated, firstTransformed)
        );
        transformed.insert({fla, nfla});
        return nfla;
    }
    assert(false);
    throw std::logic_error("Unexpected formula in NNF transformation");
}

PTRef NNFTransformer::negate(PTRef fla) {
    assert(logic.isAnd(fla) or logic.isOr(fla) or logic.isAtom(fla) or (logic.isNot(fla) and logic.isAtom(logic.getPterm(fla)[0])));
    auto it = negated.find(fla);
    if (it != negated.end()) {
        return it->second;
    }
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
        transformed.insert({fla, nfla});
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
        transformed.insert({fla, nfla});
        return nfla;
    }
    assert(false);
    throw std::logic_error("Unexpected formula in NNF transformation");
}


PTRef TermUtils::toNNF(PTRef fla) {
    if (not logic.hasSortBool(fla)) {
        throw std::invalid_argument("toNNF called with non-boolean formula!");
    }
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
        PTRef fvar, constant;
        logic.splitTermToVarAndConst(factor, fvar, constant);
        return fvar;
    };
    if (logic.isLinearFactor(term)) {
        return getVarFromFactor(term) == var;
    } else {
        assert(logic.isNumPlus(term));
        for (int i = 0; i < logic.getPterm(term).size(); ++i) {
            PTRef factor = logic.getPterm(term)[i];
            PTRef factorVar = getVarFromFactor(factor);
            if (factorVar == var) { return true; }
        }
        return false;
    }
}

bool LATermUtils::atomContainsVar(PTRef atom, PTRef var) {
    if (logic.isBoolAtom(atom) or logic.isConstant(atom)) { return false;}
    assert(logic.isNumLeq(atom) || logic.isNumEq(atom));
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
    return logic.mkOr(args);
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
    return logic.mkOr(args);
}

namespace {
struct Conjunction {};
struct Disjunction {};

template<typename T>
struct JunctionTraits {
    static bool isBetterLowerBound(FastRational const& first, FastRational const& second) = delete;
    static bool isBetterUpperBound(FastRational const& first, FastRational const& second) = delete;
};

template<>
struct JunctionTraits<Conjunction> {
    static bool isBetterLowerBound(FastRational const& first, FastRational const& second) { return first > second; } // higher is stronger
    static bool isBetterUpperBound(FastRational const& first, FastRational const& second) { return first < second; } // lower is stronger
};

template<>
struct JunctionTraits<Disjunction> {
    static bool isBetterLowerBound(FastRational const& first, FastRational const& second) { return first < second; } // lower is weaker
    static bool isBetterUpperBound(FastRational const& first, FastRational const& second) { return first > second; } // higher is weaker
};



template<typename T>
void simplifyJunction(std::vector<PtAsgn> & juncts, LALogic & logic) {
    std::vector<PtAsgn> tmp;
    tmp.reserve(juncts.size());
    MapWithKeys<PtAsgn, PTRef, PtAsgnHash> bounds;
    for (PtAsgn literal : juncts) {
        auto sign = literal.sgn;
        PTRef ineq = literal.tr;
        if (not logic.isNumLeq(ineq)) {
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
                if (JunctionTraits<T>::isBetterLowerBound(logic.getNumConst(constant), logic.getNumConst(currentValue))) {
                    bounds[key] = constant;
                }
            } else {
                assert(sign == l_False);
                // negative literal -> upper bound
                if (JunctionTraits<T>::isBetterUpperBound(logic.getNumConst(constant), logic.getNumConst(currentValue))) {
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
            tmp.push_back(PtAsgn(logic.mkNumLeq(bounds[key], key.tr), key.sgn));
        }
        juncts = std::move(tmp);
    }
}
}

void LATermUtils::simplifyDisjunction(std::vector<PtAsgn> & disjuncts) {
    simplifyJunction<Disjunction>(disjuncts, logic);
}

void LATermUtils::simplifyConjunction(std::vector<PtAsgn> & conjuncts) {
    simplifyJunction<Conjunction>(conjuncts, logic);
}