/*
 * Copyright (c) 2020-2022, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef OPENSMT_TERMUTILS_H
#define OPENSMT_TERMUTILS_H

#include "osmt_terms.h"

#include <algorithm>
#include <iostream>
#include <sstream>

template<typename TPred>
class VariableGathererConfig : public DefaultVisitorConfig {
    Logic & logic;
    TPred predicate;
    vec<PTRef> gatheredVariables;
public:
    VariableGathererConfig(Logic & logic, TPred predicate): logic(logic), predicate(predicate) {}

    void visit(PTRef term) override {
        if (logic.isVar(term) and predicate(term)) {
            gatheredVariables.push(term);
        }
    }

    vec<PTRef> && extractGatheredVariables() { return std::move(gatheredVariables); }
};

class TermUtils {
    Logic & logic;
public:
    TermUtils(Logic & logic) : logic(logic) {}

    using substitutions_map = std::unordered_map<PTRef, PTRef, PTRefHash>;

    bool isUPOrConstant(PTRef term) const {
        return logic.isUP(term) || (logic.hasSortBool(term) && logic.getPterm(term).nargs() == 0);
    }

    vec<PTRef> getVars(PTRef term) const {
        return ::variables(logic, term);
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
        if (subMap.empty()) { return term; }

        MapWithKeys<PTRef, PTRef, PTRefHash> map;
        for (auto const & entry : subMap) {
            map.insert(entry.first, entry.second);
        }
        return Substitutor(logic, map).rewrite(term);
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
        for (std::size_t i = 0; i < domainVars.size(); ++i) {
            assert(logic.isVar(domainVars[i]) and logic.isVar(codomainVars[i]));
            subst.insert({domainVars[i], codomainVars[i]});
        }
    }

    void printTermWithLets(std::ostream & out, PTRef term);

    PTRef simplifyMax(PTRef root) {
        if (logic.isAnd(root) or logic.isOr(root)) {
            root = ::rewriteMaxArityAggresive(logic, root);
            return ::simplifyUnderAssignment_Aggressive(root, logic);
        }
        return root;
    }

    PTRef toNNF(PTRef fla);

    struct SimplificationResult {
        Logic::SubstMap substitutionsUsed;
        PTRef result;
    };
    SimplificationResult extractSubstitutionsAndSimplify(PTRef fla);
};

class LATermUtils {
    ArithLogic & logic;
public:
    LATermUtils(ArithLogic & logic) : logic(logic) {}


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

    PTRef getUnversioned(PTRef var) {
        assert(logic.isVar(var));
        assert(isVersioned(var));
        SRef sort = logic.getSortRef(var);
        std::string varName = logic.getSymName(var);
        auto pos = varName.rfind(versionSeparator);
        varName.erase(pos);
        return logic.mkVar(sort, varName.c_str());
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

class VersionManager {
    Logic & logic;
    inline static const char sourceSuffix = 's';
    inline static const char targetSuffix = 't';
    inline static const std::string instanceSeparator = "##";
    inline static const std::string tagSeparator = "__";

    static void ensureNoVersion(std::string & varName);
    static void removeTag(std::string & varName);

    template<typename TVarTransform>
    class VersioningConfig : public DefaultRewriterConfig {
        Logic const & logic;
        TVarTransform varTransform;
    public:
        VersioningConfig(Logic const & logic, TVarTransform varTransform) : logic(logic), varTransform(varTransform) {}

        PTRef rewrite(PTRef term) override {
            if (logic.isVar(term)) {
                return varTransform(term);
            }
            return term;
        }
    };

    template<typename TVarTransform>
    class VersioningRewriter : public Rewriter<VersioningConfig<TVarTransform>> {
    public:
        VersioningRewriter(Logic & logic, VersioningConfig<TVarTransform> & config) : Rewriter<VersioningConfig<TVarTransform>>(logic, config) {}
    };

    template<typename TVarTransform>
    PTRef rewrite(PTRef fla, TVarTransform transform) const {
        VersioningConfig<TVarTransform> config(logic, transform);
        return VersioningRewriter<TVarTransform>(logic, config).rewrite(fla);
    }

public:
    VersionManager(Logic & logic) : logic(logic) {}

    PTRef baseFormulaToTarget(PTRef fla) const;
    PTRef baseFormulaToSource(PTRef fla, unsigned instance = 0) const;
    PTRef targetFormulaToBase(PTRef fla) const;
    PTRef sourceFormulaToBase(PTRef fla) const;
    PTRef sourceFormulaToTarget(PTRef fla) const;

    PTRef toBase(PTRef var) const {
        assert(logic.isVar(var));
        std::string varName = logic.getSymName(var);
        ensureNoVersion(varName);
        removeTag(varName);
        return logic.mkVar(logic.getSortRef(var), varName.c_str());
    }

    PTRef toSource(PTRef var, unsigned instance = 0) const {
        assert(logic.isVar(var));
        assert(not isVersioned(var));
        SRef sort = logic.getSortRef(var);
        std::stringstream ss;
        ss << logic.getSymName(var) << tagSeparator << sourceSuffix << instanceSeparator << instance;
        std::string newName = ss.str();
        return logic.mkVar(sort, newName.c_str());
    }

    PTRef toTarget(PTRef var) const {
        assert(logic.isVar(var));
        assert(not isVersioned(var));
        assert(not isTagged(var));
        SRef sort = logic.getSortRef(var);
        std::stringstream ss;
        ss << logic.getSymName(var) << tagSeparator << targetSuffix;
        std::string newName = ss.str();
        return logic.mkVar(sort, newName.c_str());
    }

    static auto versionPosition(std::string const & name) {
        return name.rfind(instanceSeparator);
    }

    static auto tagPosition(std::string const & name) {
        return name.rfind(tagSeparator);
    }

    static bool isTaggedName(std::string const & name) {
        return tagPosition(name) != std::string::npos;
    }

    static bool isVersionedName(std::string const & name) {
        return versionPosition(name) != std::string::npos;
    }

    bool isTagged(PTRef var) const {
        assert(logic.isVar(var));
        std::string varName = logic.getSymName(var);
        return isTaggedName(varName);
    }

    bool isVersioned(PTRef var) const {
        assert(logic.isVar(var));
        std::string varName = logic.getSymName(var);
        return isVersionedName(varName);
    }
};

class LinearCanonicalPredicateRepresentation {
    using VariableRepresentation = std::unordered_map<SymRef, std::vector<PTRef>, SymRefHash>;
    using TermRepresentation = std::unordered_map<SymRef, PTRef, SymRefHash>;
    VariableRepresentation representation {};
    TermRepresentation targetTerms {};
    TermRepresentation sourceTerms {};
    Logic & logic;
public:
    LinearCanonicalPredicateRepresentation(Logic & logic) : logic(logic) {}

    void addRepresentation(SymRef sym, std::vector<PTRef> vars);

    PTRef getTargetTermFor(SymRef sym) const;

    PTRef getSourceTermFor(SymRef sym) const;

    bool hasRepresentationFor(SymRef sym) const {
        return representation.count(sym) > 0;
    }
};

class NonlinearCanonicalPredicateRepresentation {
    using VariableRepresentation = std::unordered_map<SymRef, std::vector<PTRef>, SymRefHash>;
    using TermRepresentation = std::unordered_map<SymRef, PTRef, SymRefHash>;
    VariableRepresentation representation {};
    TermRepresentation targetTerms {};
    mutable std::vector<TermRepresentation> sourceTermsByInstance {{}};
    Logic & logic;
public:
    NonlinearCanonicalPredicateRepresentation(Logic & logic) : logic(logic) {}

    void addRepresentation(SymRef sym, std::vector<PTRef> vars);

    bool hasRepresentationFor(SymRef sym) const {
        return representation.count(sym) > 0;
    }

    PTRef getTargetTermFor(SymRef sym) const;

    PTRef getSourceTermFor(SymRef sym, unsigned instanceCount = 0) const;

    class CountingProxy {
        NonlinearCanonicalPredicateRepresentation & parent;
        std::unordered_map<SymRef, unsigned, SymRefHash> counts;
    public:
        CountingProxy(NonlinearCanonicalPredicateRepresentation & parent) : parent(parent) {}

        PTRef getSourceTermFor(SymRef sym) {
            auto count = counts[sym]++;
            return parent.getSourceTermFor(sym, count);
        }
    };

    CountingProxy createCountingProxy() { return CountingProxy(*this); }
};

class TrivialQuantifierElimination {
    Logic & logic;
public:
    TrivialQuantifierElimination(Logic & logic) : logic(logic) {}

    PTRef tryEliminateVars(vec<PTRef> const & vars, PTRef fla) const;

    PTRef tryEliminateVarsExcept(vec<PTRef> const & vars, PTRef fla) const;
};

inline vec<PTRef> operator+(vec<PTRef> const & first, vec<PTRef> const & second) {
    vec<PTRef> res;
    first.copyTo(res);
    for (PTRef term : second) {
        res.push(term);
    }
    return res;
}

#endif //OPENSMT_TERMUTILS_H
