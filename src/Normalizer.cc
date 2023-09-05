/*
 * Copyright (c) 2020-2022, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "Normalizer.h"

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
    ChClause res = eliminateRedundantVariables(ChClause{.head = std::move(newHead), .body = std::move(newBody)});
    normalizingEqualities.push_back(std::move(topLevelEqualities));
    topLevelEqualities.clear();
    return res;
}

ChClause Normalizer::eliminateRedundantVariables(ChClause && clause) {
    // For now we just eliminate variables left over after normalization
    // In the future we can do variable elimination here
    TermUtils utils(logic);
    std::unordered_set<PTRef, PTRefHash> validVars;
    // vars from head
    {
        auto headVars = utils.predicateArgsInOrder(clause.head.predicate.predicate);
        validVars.insert(headVars.begin(), headVars.end());
    }
    // vars from uninterpreted body
    for (auto const & pred : clause.body.uninterpretedPart) {
        auto vars = utils.predicateArgsInOrder(pred.predicate);
        validVars.insert(vars.begin(), vars.end());
    }

    PTRef newInterpretedBody = clause.body.interpretedPart.fla;
    ////////////////////// DEALING with LOCAL VARIABLES /////////////////////////
    {
        // Let's try to do variable elimination already here
        auto isVarToEliminate = [&](PTRef var) {
            return logic.isVar(var) and validVars.find(var) == validVars.end();
        };
        auto gatherVariables = [&](PTRef fla) {
            return matchingSubTerms(logic, fla, isVarToEliminate);
        };
        auto toEliminateVars = gatherVariables(newInterpretedBody);
        if (toEliminateVars.size() > 0) {
//            std::cout << "Before variable elimination: " << logic.printTerm(newInterpretedBody) << std::endl;
            newInterpretedBody = TrivialQuantifierElimination(logic).tryEliminateVars(toEliminateVars, newInterpretedBody);
//            std::cout << "After variable elimination: " << logic.printTerm(newInterpretedBody) << std::endl;
        }
        auto localVars = gatherVariables(newInterpretedBody);
        if (localVars.size() > 0) {
            // there are some local variables left, rename them and make them versioned
            TermUtils::substitutions_map subst;
            for (PTRef localVar : localVars) {
                SRef sort = logic.getSortRef(localVar);
                std::string uniq_name = "aux#" + std::to_string(counter++);
                PTRef renamed = timeMachine.getVarVersionZero(uniq_name, sort);
                subst.insert({localVar, renamed});
            }
            newInterpretedBody = utils.varSubstitute(newInterpretedBody, subst);
        }
    }
    ////////////////////// END OF DEALING with LOCAL VARIABLES /////////////////////////

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

    newInterpretedPart = eliminateItes(newInterpretedPart);
    newInterpretedPart = eliminateDivMod(newInterpretedPart);
    newInterpretedPart = eliminateDistincts(newInterpretedPart);
    return ChcBody{InterpretedFla{newInterpretedPart}, std::move(newUninterpretedPart)};
}

PTRef Normalizer::eliminateDivMod(PTRef fla) {
    ArithLogic * lalogic = dynamic_cast<ArithLogic *>(&logic);
    if (lalogic and lalogic->hasIntegers()) {
        return DivModRewriter(*lalogic).rewrite(fla);
    }
    return fla;
}

PTRef Normalizer::eliminateItes(PTRef fla) {
    return IteHandler(logic).rewrite(fla);
}

PTRef Normalizer::eliminateDistincts(PTRef fla) {
    return DistinctRewriter(logic).rewrite(fla);
}
