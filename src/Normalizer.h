//
// Created by Martin Blicha on 01.09.20.
//

#ifndef OPENSMT_NORMALIZER_H
#define OPENSMT_NORMALIZER_H

#include "ChcSystem.h"
#include "TermUtils.h"

#include <memory>
#include <unordered_map>

struct NormalizedChcSystem{
    std::unique_ptr<ChcSystem> normalizedSystem;
    CanonicalPredicateRepresentation canonicalPredicateRepresentation;
};

class Normalizer{
    Logic& logic;
    TimeMachine timeMachine;
    std::unordered_map<SymRef, std::vector<PTRef>, SymRefHash> predicateToUniqVars;
    vec<PTRef> topLevelEqualities;
    long long counter = 0;

    ChClause normalize(ChClause const& clause) {
        auto const& head = clause.head;
        auto const& body = clause.body;
        topLevelEqualities.clear();
        ChcHead newHead = normalize(head);
        ChcBody newBody = normalize(body);
        ChClause res = eliminateRedundantVariables(ChClause{.head = std::move(newHead), .body = std::move(newBody)});
        topLevelEqualities.clear();
        return res;
    }

    ChcHead normalize(ChcHead const& head) {
        auto predicate = head.predicate.predicate;
        auto predicateSymbol = logic.getSymRef(predicate);
        if (predicateToUniqVars.count(predicateSymbol) == 0) {
            createUniqueRepresentation(predicate);
        }
        assert(predicateToUniqVars.count(predicateSymbol) > 0);
        auto const& representation = predicateToUniqVars.at(predicateSymbol);
        assert(representation.size() == logic.getPterm(predicate).size());
        vec<PTRef> newArgs;
        for (int i = 0; i < representation.size(); ++i) {
            PTRef nextStateVar = timeMachine.sendVarThroughTime(representation[i], 1);
            PTRef arg = logic.getPterm(predicate)[i];
            topLevelEqualities.push(logic.mkEq(nextStateVar, arg));
            newArgs.push(nextStateVar);
        }
        PTRef newPredicate = logic.insertTerm(predicateSymbol, std::move(newArgs));
        return ChcHead{newPredicate};
    }

    void createUniqueRepresentation(PTRef predicate) {
        auto size = logic.getPterm(predicate).size();
        std::vector<PTRef> repre;
        for (int i = 0; i < size; ++i) {
            SRef sort = logic.getSortRef(logic.getPterm(predicate)[i]);
            std::string uniq_name = "x#" + std::to_string(counter++);
            PTRef versionlessVar = logic.mkVar(sort, uniq_name.c_str());
            repre.push_back(timeMachine.getVarVersionZero(versionlessVar));
        }
        predicateToUniqVars.insert(std::make_pair(logic.getSymRef(predicate), std::move(repre)));
    }

    ChcBody normalize(ChcBody const& body);

    CanonicalPredicateRepresentation getCanonicalPredicateRepresentation() const {
        CanonicalPredicateRepresentation repre;
        for (auto const & entry : predicateToUniqVars) {
            auto const & vars = entry.second;
            vec<PTRef> stateVars;
            vec<PTRef> nextVars;
            for (PTRef var : vars) {
                assert(logic.isVar(var));
                assert(timeMachine.isVersioned(var));
                stateVars.push(var);
                nextVars.push(timeMachine.sendVarThroughTime(var, 1));
            }
            SymRef symbol = entry.first;
            repre.addRepresentation(symbol, logic.insertTerm(symbol, std::move(stateVars)), logic.insertTerm(symbol, std::move(nextVars)));
        }
        return repre;
    }

    ChClause eliminateRedundantVariables(ChClause && clause);

    PTRef eliminateItes(PTRef fla);
    PTRef eliminateDivMod(PTRef fla);

public:
    Normalizer(Logic& logic) : logic(logic), timeMachine(logic) {}

    NormalizedChcSystem normalize(ChcSystem const & system);

};


#endif //OPENSMT_NORMALIZER_H
