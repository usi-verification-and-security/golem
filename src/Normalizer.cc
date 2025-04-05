/*
 * Copyright (c) 2020-2025, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "Normalizer.h"

namespace golem {
NormalizedChcSystem Normalizer::normalize(const ChcSystem & system) {
    this->canonicalPredicateRepresentation.addRepresentation(logic.getSym_true(), {});
    std::vector<ChClause> normalized;
    auto const& clauses = system.getClauses();
    for (auto const & clause : clauses) {
        normalized.push_back(normalize(clause));
    }
    NonlinearCanonicalPredicateRepresentation cpr = getCanonicalPredicateRepresentation();
    // build graph out of normalized system
    auto newSystem = std::make_unique<ChcSystem>();
    for (auto const & clause : normalized) {
        newSystem->addClause(clause);
    }
    return NormalizedChcSystem{.normalizedSystem = std::move(newSystem), .canonicalPredicateRepresentation = std::move(cpr)};
}

ChClause Normalizer::normalize(ChClause const & clause) {
    auto const & head = clause.head;
    auto const & body = clause.body;
    topLevelEqualities.clear();
    ChcHead newHead = normalize(head);
    ChcBody newBody = normalize(body);
    ChClause res = normalizeAuxiliaryVariables(ChClause{.head = std::move(newHead), .body = std::move(newBody)});
    normalizingEqualities.push_back(std::move(topLevelEqualities));
    topLevelEqualities.clear();
    return res;
}

ChClause Normalizer::normalizeAuxiliaryVariables(ChClause && clause) {
    TermUtils utils(logic);
    std::unordered_set<PTRef, PTRefHash> predicateVars;
    // vars from head
    {
        auto headVars = utils.predicateArgsInOrder(clause.head.predicate.predicate);
        predicateVars.insert(headVars.begin(), headVars.end());
    }
    // vars from uninterpreted body
    for (auto const & pred : clause.body.uninterpretedPart) {
        auto vars = utils.predicateArgsInOrder(pred.predicate);
        predicateVars.insert(vars.begin(), vars.end());
    }

    PTRef newInterpretedBody = clause.body.interpretedPart.fla;
    auto isVarToNormalize = [&](PTRef var) {
        return logic.isVar(var) and predicateVars.find(var) == predicateVars.end();
    };
    auto localVars = matchingSubTerms(logic, newInterpretedBody, isVarToNormalize);
    if (localVars.size() > 0) {
        // there are some local variables left, rename them and make them versioned
        TermUtils::substitutions_map subst;
        for (PTRef localVar : localVars) {
            SRef sort = logic.getSortRef(localVar);
            std::string uniq_name = "aux#" + std::to_string(counter++);
            PTRef renamed = timeMachine.getVarVersionZero(uniq_name, sort);
            subst.insert({localVar, renamed});
            topLevelEqualities.push({.normalizedVar = renamed, .originalArg = localVar});
        }
        newInterpretedBody = utils.varSubstitute(newInterpretedBody, subst);
    }
    return ChClause{clause.head, ChcBody{{newInterpretedBody}, clause.body.uninterpretedPart}};
}


ChcHead Normalizer::normalize(ChcHead const& head) {
    auto predicate = head.predicate.predicate;
    auto predicateSymbol = logic.getSymRef(predicate);
    if (not canonicalPredicateRepresentation.hasRepresentationFor(predicateSymbol)) {
        createUniqueRepresentation(predicate);
    }
    assert(canonicalPredicateRepresentation.hasRepresentationFor(predicateSymbol));
    PTRef targetTerm = canonicalPredicateRepresentation.getTargetTermFor(predicateSymbol);
    auto size = logic.getPterm(targetTerm).size();
    assert(size == logic.getPterm(predicate).size());
    for (int i = 0; i < size; ++i) {
        PTRef targetVar = logic.getPterm(targetTerm)[i];
        PTRef arg = logic.getPterm(predicate)[i];
        topLevelEqualities.push({.normalizedVar = targetVar, .originalArg = arg});
    }
    return ChcHead{targetTerm};
}

ChcBody Normalizer::normalize(const ChcBody & body) {
    // uninterpreted part
    std::vector<UninterpretedPredicate> newUninterpretedPart;
    auto const& uninterpreted = body.uninterpretedPart;
    auto proxy = canonicalPredicateRepresentation.createCountingProxy();
    for (auto const& predicateWrapper : uninterpreted) {
        PTRef predicate = predicateWrapper.predicate;
        auto predicateSymbol = logic.getSymRef(predicate);
        if (not canonicalPredicateRepresentation.hasRepresentationFor(predicateSymbol)) {
            createUniqueRepresentation(predicate);
        }
        assert(canonicalPredicateRepresentation.hasRepresentationFor(predicateSymbol));
        PTRef sourceTerm = proxy.getSourceTermFor(predicateSymbol);
        auto size = logic.getPterm(sourceTerm).size();
        assert(size == logic.getPterm(predicate).size());
        for (int i = 0; i < size; ++i) {
            PTRef arg = logic.getPterm(predicate)[i];
            PTRef sourceVar = logic.getPterm(sourceTerm)[i];
            topLevelEqualities.push({.normalizedVar = sourceVar, .originalArg = arg});
        }
        newUninterpretedPart.push_back(UninterpretedPredicate{sourceTerm});
    }
    // interpreted part
    PTRef newInterpretedPart = body.interpretedPart.fla;

    vec<PTRef> equalities;
    equalities.capacity(topLevelEqualities.size());
    TermUtils::substitutions_map subst;
    for (auto [normalizedVar, originalArg] : topLevelEqualities) {
        if (logic.isVar(originalArg) and subst.find(originalArg) == subst.end()) {
            subst.insert({originalArg, normalizedVar});
        } else { // originalArg is not variable or it has substitution assigned already
            // MB: We try to avoid creating equalities with original arguments, which would need to be rewritten later
            PTRef value = logic.isVar(originalArg) ? subst.at(originalArg) : originalArg;
            equalities.push(logic.mkEq(normalizedVar, value));
        }
    }
    if (equalities.size() > 0) {
        newInterpretedPart = logic.mkAnd(newInterpretedPart, logic.mkAnd(std::move(equalities)));
    }
    newInterpretedPart = TermUtils(logic).varSubstitute(newInterpretedPart, subst);
    return ChcBody{InterpretedFla{newInterpretedPart}, std::move(newUninterpretedPart)};
}
} // namespace golem


