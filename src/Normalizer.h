/*
 * Copyright (c) 2020-2022, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef OPENSMT_NORMALIZER_H
#define OPENSMT_NORMALIZER_H

#include "ChcSystem.h"
#include "TermUtils.h"

#include <memory>
#include <unordered_map>

struct NormalizedChcSystem{
    std::unique_ptr<ChcSystem> normalizedSystem;
    NonlinearCanonicalPredicateRepresentation canonicalPredicateRepresentation;
};

class Normalizer{
    Logic& logic;
    TimeMachine timeMachine;
    NonlinearCanonicalPredicateRepresentation canonicalPredicateRepresentation;
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

    ChcHead normalize(ChcHead const& head);

    ChcBody normalize(ChcBody const& body);

    void createUniqueRepresentation(PTRef predicate) {
        auto size = logic.getPterm(predicate).size();
        std::vector<PTRef> repre; repre.reserve(size);
        for (int i = 0; i < size; ++i) {
            SRef sort = logic.getSortRef(logic.getPterm(predicate)[i]);
            std::string uniq_name = "x#" + std::to_string(counter++);
            PTRef versionlessVar = logic.mkVar(sort, uniq_name.c_str());
            repre.push_back(versionlessVar);
        }
        canonicalPredicateRepresentation.addRepresentation(logic.getSymRef(predicate), std::move(repre));
    }

    NonlinearCanonicalPredicateRepresentation getCanonicalPredicateRepresentation() const {
        return canonicalPredicateRepresentation;
    }

    ChClause eliminateRedundantVariables(ChClause && clause);

    PTRef eliminateItes(PTRef fla);
    PTRef eliminateDivMod(PTRef fla);

public:
    Normalizer(Logic& logic) : logic(logic), timeMachine(logic), canonicalPredicateRepresentation(logic) {}

    NormalizedChcSystem normalize(ChcSystem const & system) &&;

};


#endif //OPENSMT_NORMALIZER_H
