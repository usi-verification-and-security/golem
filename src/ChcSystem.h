//
// Created by Martin Blicha on 15.07.20.
//

#ifndef OPENSMT_CHCSYSTEM_H
#define OPENSMT_CHCSYSTEM_H

#include "osmt_terms.h"

#include <vector>
#include <unordered_set>
#include <iosfwd>

struct UninterpretedPredicate {
    PTRef predicate;
};

inline bool operator==(UninterpretedPredicate const& p1, UninterpretedPredicate const& p2) { return p1.predicate == p2.predicate; }
inline bool operator!=(UninterpretedPredicate const& p1, UninterpretedPredicate const& p2) { return !(p1 == p2); }

struct InterpretedFla {
    PTRef fla;
};

inline bool operator==(InterpretedFla const & f1, InterpretedFla const & f2) { return f1.fla == f2.fla; }
inline bool operator!=(InterpretedFla const & f1, InterpretedFla const & f2) { return not(f1 == f2); }

struct ChcHead {
    UninterpretedPredicate predicate;
};

inline bool operator==(ChcHead const & h1, ChcHead const & h2) {
    return h1.predicate == h2.predicate;
}
inline bool operator!=(ChcHead const & h1, ChcHead const & h2) { return not(h1 == h2); }

struct ChcBody {
    InterpretedFla interpretedPart;
    std::vector<UninterpretedPredicate> uninterpretedPart;
};

inline bool operator==(ChcBody const & b1, ChcBody const & b2) {
    if (b1.interpretedPart != b2.interpretedPart) { return false; }
    if (b1.uninterpretedPart.size() != b2.uninterpretedPart.size()) { return false; }
    for (std::size_t i = 0; i < b1.uninterpretedPart.size(); ++i) {
        if (b1.uninterpretedPart[i] != b2.uninterpretedPart[i]) { return false; }
    }
    return true;
}
inline bool operator!=(ChcBody const & b1, ChcBody const & b2) { return not(b1 == b2); }

struct ChClause {
    ChcHead head;
    ChcBody body;
};

inline bool operator== (ChClause const & c1, ChClause const & c2) {
    return c1.head == c2.head && c1.body == c2.body;
}

class ChcSystem {
    std::vector<ChClause> clauses;
    std::unordered_set<SymRef, SymRefHash> knownUninterpretedPredicates;

public:
    void addUninterpretedPredicate(SymRef sym) { knownUninterpretedPredicates.insert(sym); }

    bool isUninterpretedPredicate(SymRef sym) { return knownUninterpretedPredicates.count(sym) != 0; }

    void addClause(ChClause clause) { clauses.push_back(std::move(clause)); }
    void addClause(ChcHead head, ChcBody body) { clauses.push_back(ChClause{.head = std::move(head), .body = std::move(body)}); }

    std::vector<ChClause> const & getClauses() const { return clauses; }


};

class ChcPrinter {
    Logic& logic;
    std::ostream * defaultOut;
public:
    ChcPrinter(Logic& logic, std::ostream & out) : logic(logic), defaultOut(&out) {}
    ChcPrinter(Logic& logic) : logic(logic), defaultOut(nullptr) {}

    void print(ChcSystem const & system, std::ostream & out) const;
    void print(ChClause const & clause, std::ostream & out) const;
    void print(ChcSystem const & system) const { if (defaultOut) { print(system, *defaultOut); } }
    void print(ChClause const & clause) const { if (defaultOut) { print(clause, *defaultOut); } }
};

class PTRefToCHC {
public:
    static ChcHead constructHead(PTRef head) { return ChcHead{head};}
//    static ChcHead constructEmptyHead() { return ChcHead{PTRef_Undef};}
    static ChcBody constructBody(PTRef interpreted, std::vector<PTRef> const & uninterpreted) {
        return constructBody(interpreted, uninterpreted.begin(), uninterpreted.end());
    }
    template<typename TIt>
    static ChcBody constructBody(PTRef interpreted, TIt uninterpretedBegin, TIt uninterpretedEnd) {
        std::vector<UninterpretedPredicate> uninterpretedPart;
        std::transform(uninterpretedBegin, uninterpretedEnd, std::back_inserter(uninterpretedPart), [](PTRef ref) {
            return UninterpretedPredicate{.predicate = ref};
        });
        return ChcBody{{interpreted}, std::move(uninterpretedPart)};
    }
};

#endif //OPENSMT_CHCSYSTEM_H
