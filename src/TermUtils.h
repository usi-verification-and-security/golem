//
// Created by Martin Blicha on 04.08.20.
//

#ifndef OPENSMT_TERMUTILS_H
#define OPENSMT_TERMUTILS_H

#include "osmt_terms.h"

#include <algorithm>

class TermUtils {
    Logic & logic;
public:
    TermUtils(Logic & logic) : logic(logic) {}

    using substitutions_map = std::unordered_map<PTRef, PTRef, PTRefHash>;

    bool isUPOrConstant(PTRef term) const {
        return logic.isUP(term) || (logic.hasSortBool(term) && logic.getPterm(term).nargs() == 0);
    }

    vec<PTRef> getVars(PTRef term) const {
        MapWithKeys<PTRef,bool,PTRefHash> vars;
        ::getVars(term, logic, vars);
        vec<PTRef> keys;
        vars.getKeys().copyTo(keys);
        return keys;
    }

    std::vector<PTRef> getVarsFromPredicateInOrder(PTRef predicate) const {
        assert(isUPOrConstant(predicate));
        auto const & pterm = logic.getPterm(predicate);
        assert(std::all_of(pterm.begin(), pterm.end(), [&](PTRef child) { return logic.isVar(child); }));
        std::vector<PTRef> vars;
        vars.resize(pterm.size());
        std::copy(pterm.begin(), pterm.end(), vars.begin());
        return vars;
    }

    void transitiveClosure(substitutions_map & subMap) const {
        MapWithKeys<PTRef, PTRef, PTRefHash> map;
        for (auto const & entry : subMap) {
            map.insert(entry.first, entry.second);
        }
        logic.substitutionsTransitiveClosure(map);
        subMap.clear();
        for (auto const & key : map.getKeys()) {
            subMap.insert({key, map[key]});
        }
    }

    PTRef varSubstitute(PTRef term, substitutions_map const & subMap) const {
        MapWithKeys<PTRef, PTRef, PTRefHash> map;
        for (auto const & entry : subMap) {
            map.insert(entry.first, entry.second);
        }
        return Substitutor(logic, map).rewrite(term);
    }

    void printDefine(std::ostream & out, PTRef function, PTRef definition) const {
        out << "(define " << logic.printTerm(function) << ' ' << logic.printTerm(definition) << ")\n";
    }


    struct Conjunction {
        static bool isCorrectJunction(Logic & logic, PTRef term) { return logic.isAnd(term); }
        static bool isOtherJunction(Logic & logic, PTRef term) { return logic.isOr(term); }
    };

    struct Disjunction {
        static bool isCorrectJunction(Logic & logic, PTRef term) { return logic.isOr(term); }
        static bool isOtherJunction(Logic & logic, PTRef term) { return logic.isAnd(term); }
    };

    template<typename Junction, typename TPred>
    vec<PTRef> getTopLevelJuncts(PTRef root, TPred predicate) const {
        // Inspired by Logic::getNewFacts
        vec<PTRef> res;
        Map<PtAsgn,bool,PtAsgnHash> isdup;
        vec<PtAsgn> queue;
        {
            PTRef p;
            lbool sign;
            logic.purify(root, p, sign);
            queue.push(PtAsgn(p, sign));
        }
        while (queue.size() != 0) {
            PtAsgn pta = queue.last(); queue.pop();
            if (isdup.has(pta)) continue;
            isdup.insert(pta, true);
            Pterm const & t = logic.getPterm(pta.tr);
            if (Junction::isCorrectJunction(logic, pta.tr) and pta.sgn == l_True) {
                for (int i = 0; i < t.size(); i++) {
                    PTRef c;
                    lbool c_sign;
                    logic.purify(t[i], c, c_sign);
                    queue.push(PtAsgn(c, c_sign));
                }
            } else if (Junction::isOtherJunction(logic, pta.tr) and (pta.sgn == l_False)) {
                for (int i = 0; i < t.size(); i++) {
                    PTRef c;
                    lbool c_sign;
                    logic.purify(t[i], c, c_sign);
                    queue.push(PtAsgn(c, c_sign ^ true));
                }
            } else {
                PTRef term = pta.sgn == l_False ? logic.mkNot(pta.tr) : pta.tr;
                if (predicate(term)) {
                    res.push(term);
                }
            }
        }
        return res;
    }

    template<typename TPred>
    vec<PTRef> getTopLevelConjuncts(PTRef root, TPred predicate) const {
        return getTopLevelJuncts<Conjunction>(root, predicate);
    }

    vec<PTRef> getTopLevelConjuncts(PTRef root) const {
        return getTopLevelConjuncts(root, [](PTRef){ return true; });
    }

    template<typename TPred>
    vec<PTRef> getTopLevelDisjuncts(PTRef root, TPred predicate) const {
        return getTopLevelJuncts<Disjunction>(root, predicate);
    }

    vec<PTRef> getTopLevelDisjuncts(PTRef root) const {
        return getTopLevelDisjuncts(root, [](PTRef){ return true; });
    }

    PTRef conjoin (PTRef what, PTRef to);

    void insertVarPairsFromPredicates(PTRef domain, PTRef codomain, substitutions_map & subst) const {
        assert(isUPOrConstant(domain) and isUPOrConstant(codomain));
        auto domainVars = getVarsFromPredicateInOrder(domain);
        auto codomainVars = getVarsFromPredicateInOrder(codomain);
        assert(domainVars.size() == codomainVars.size());
        for (int i = 0; i < domainVars.size(); ++i) {
            assert(logic.isVar(domainVars[i]) and logic.isVar(codomainVars[i]));
            subst.insert({domainVars[i], codomainVars[i]});
        }
    }

    void printTermWithLets(ostream & out, PTRef term);

    PTRef simplifyMax(PTRef root) {
        if (logic.isAnd(root) or logic.isOr(root)) {
            root = ::rewriteMaxArityAggresive(logic, root);
            return ::simplifyUnderAssignment_Aggressive(root, logic);
        }
        return root;
    }

    PTRef toNNF(PTRef fla);
};

class LATermUtils {
    LALogic & logic;
public:
    LATermUtils(LALogic & logic) : logic(logic) {}


    /**
     * Given a term 't' and a var 'v' present in the term, returns a term 's' such that
     * 'v = s' is equivalent to 't = 0'
     *
     * @param zeroTerm term that is equal to 0
     * @param var variable present in the term
     * @return term 's' such that 'var = s' is equivalent to 'zeroTerm = 0'
     */
    PTRef expressZeroTermFor(PTRef zeroTerm, PTRef var);

    bool atomContainsVar(PTRef atom, PTRef var);
    bool termContainsVar(PTRef term, PTRef var);

    PTRef simplifyDisjunction(PTRef fla);
    void simplifyDisjunction(std::vector<PtAsgn> & disjuncts);

    PTRef simplifyConjunction(PTRef fla);
    void simplifyConjunction(std::vector<PtAsgn> & disjuncts);
};

class TimeMachine {
    Logic & logic;
    const std::string versionSeparator = "##";

    class VersioningConfig : public DefaultRewriterConfig {
        TimeMachine & owner;
        Logic const & logic;
        int versioningNumber = 0;
    public:
        VersioningConfig(TimeMachine & machine, Logic const & logic) : owner(machine), logic(logic) {}

        void setVersioningNumber(int number) { versioningNumber = number; }

        PTRef rewrite(PTRef term) override {
            if (logic.isVar(term)) {
                return owner.sendVarThroughTime(term, versioningNumber);
            }
            return term;
        }
    };

    class VersioningRewriter : public Rewriter<VersioningConfig> {
    public:
        VersioningRewriter(Logic & logic, VersioningConfig & config) : Rewriter<VersioningConfig>(logic, config) {}
    };

    VersioningConfig config;

public:
    TimeMachine(Logic & logic) : logic(logic), config(*this, logic) {}
    // Returns version of var 'steps' steps in the future (if positive) or in the past (if negative)
    PTRef sendVarThroughTime(PTRef var, int steps) const {
        assert(logic.isVar(var));
        assert(isVersioned(var));
        std::string varName = logic.getSymName(var);
        auto pos = varName.rfind(versionSeparator);
        auto numPos = pos + versionSeparator.size();
        auto numStr = varName.substr(numPos);
        int version = std::stoi(numStr);
        version += steps;
        varName.replace(numPos, std::string::npos, std::to_string(version));
        return logic.mkVar(logic.getSortRef(var), varName.c_str());
    }

    // Given a variable with no version, compute the zero version representing current state
    PTRef getVarVersionZero(PTRef var) {
        assert(logic.isVar(var));
        assert(not isVersioned(var));
        SRef sort = logic.getSortRef(var);
        std::stringstream ss;
        ss << logic.getSymName(var) << versionSeparator << 0;
        std::string newName = ss.str();
        return logic.mkVar(sort, newName.c_str());
    }

    PTRef getVarVersionZero(std::string const & name, SRef sort) {
        assert(not isVersionedName(name));
        std::stringstream ss;
        ss << name << versionSeparator << 0;
        std::string newName = ss.str();
        return logic.mkVar(sort, newName.c_str());
    }

    int getVersionNumber(PTRef var) {
        assert(logic.isVar(var));
        assert(isVersioned(var));
        std::string varName = logic.getSymName(var);
        auto pos = varName.rfind(versionSeparator);
        auto numPos = pos + versionSeparator.size();
        auto numStr = varName.substr(numPos);
        int version = std::stoi(numStr);
        return version;
    }

    PTRef sendFlaThroughTime(PTRef fla, int steps) {
        if (steps == 0) { return fla; }
        config.setVersioningNumber(steps);
        VersioningRewriter rewriter(logic, config);
        return rewriter.rewrite(fla);
    }

    bool isVersionedName(std::string const & name) const {
        auto pos = name.rfind(versionSeparator);
        return pos != std::string::npos;
    }

    bool isVersioned(PTRef var) const {
        assert(logic.isVar(var));
        std::string varName = logic.getSymName(var);
        return isVersionedName(varName);
    }
};

class CanonicalPredicateRepresentation {
    using RepreType = std::unordered_map<SymRef, PTRef, SymRefHash>;
    RepreType stateVersion;
    RepreType nextVersion;
public:
    void addRepresentation(SymRef sym, PTRef stateRepre, PTRef nextStateRepre) {
        stateVersion.insert({sym, stateRepre});
        nextVersion.insert({sym, nextStateRepre});
    }

    PTRef getStateRepresentation(SymRef sym) const { return stateVersion.at(sym); }
    PTRef getNextStateRepresentation(SymRef sym) const { return nextVersion.at(sym); }
};

class TrivialQuantifierElimination {
    Logic & logic;

    PTRef tryGetSubstitutionFromEquality(PTRef var, PTRef eq) const;
public:
    TrivialQuantifierElimination(Logic & logic) : logic(logic) {}

    PTRef tryEliminateVars(vec<PTRef> const & vars, PTRef fla) const {
        if (vars.size() == 0) { return fla; }
        TermUtils::substitutions_map substMap;
        std::unordered_set<PTRef, PTRefHash> forbiddenVars;
        TermUtils utils(logic);
        auto topLevelEqualities = utils.getTopLevelConjuncts(fla, [&](PTRef conjunct) { return logic.isEquality(conjunct); });

        for (PTRef var : vars) {
            assert(logic.isVar(var));
            if (not logic.isVar(var)) {
                throw std::invalid_argument("Quantifier elimination error: " + std::string(logic.printTerm(var)) + " is not a var!");
            }
            if (forbiddenVars.count(var) != 0) { continue; }
            for (PTRef equality : topLevelEqualities) {
                auto eqVars = utils.getVars(equality);
                auto it = std::find(eqVars.begin(), eqVars.end(), var);
                if (it != eqVars.end()) {
                    PTRef subst = tryGetSubstitutionFromEquality(var, equality);
                    if (subst != PTRef_Undef) {
                        substMap.insert({var, subst});
                        forbiddenVars.insert(eqVars.begin(), eqVars.end());
                        break;
                    }
                }
            }
        }

        if (substMap.empty()) {
            return fla;
        }
        utils.transitiveClosure(substMap);
        PTRef res = utils.varSubstitute(fla, substMap);
        return res;
    }
};


#endif //OPENSMT_TERMUTILS_H
