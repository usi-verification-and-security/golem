/*
 * Copyright (c) 2020-2022, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "Normalizer.h"

NormalizedChcSystem Normalizer::normalize(const ChcSystem & system) && {
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

ChClause Normalizer::eliminateRedundantVariables(ChClause && clause) {
    // For now we just eliminate variables left over after normalization
    // In the future we can do variable elimination here
    TermUtils utils(logic);
    std::unordered_set<PTRef, PTRefHash> validVars;
    // vars from head
    {
        auto headVars = utils.getVarsFromPredicateInOrder(clause.head.predicate.predicate);
        validVars.insert(headVars.begin(), headVars.end());
    }
    // vars from uninterpreted body
    for (auto const & pred : clause.body.uninterpretedPart) {
        auto vars = utils.getVarsFromPredicateInOrder(pred.predicate);
        validVars.insert(vars.begin(), vars.end());
    }
    // build substitution map
    std::unordered_map<PTRef, PTRef, PTRefHash> subst;
    for (PTRef eq : topLevelEqualities) {
        if (not logic.isEquality(eq)) { continue; } // It could be the result of simplifying boolean equality to constant
        PTRef lhs = logic.getPterm(eq)[0];
        PTRef rhs = logic.getPterm(eq)[1];
        if (logic.isVar(lhs) && validVars.find(lhs) == validVars.end()) {
            if (subst.count(lhs) == 0) {
                subst.insert({lhs, rhs});
            }
            continue;
        }
        if (logic.isVar(rhs) && validVars.find(rhs) == validVars.end()) {
            if (subst.count(rhs) == 0) {
                subst.insert({rhs, lhs});
            }
        }
    }
    PTRef newInterpretedBody = utils.varSubstitute(clause.body.interpretedPart.fla, subst);
    ////////////////////// DEALING with LOCAL VARIABLES /////////////////////////
    {
        // Let's try to do variable elimination already here
        auto allVars = utils.getVars(newInterpretedBody);
        auto isValidVar = [&validVars](PTRef var) {
            return validVars.find(var) != validVars.end();
        };
        auto newEnd = std::remove_if(allVars.begin(), allVars.end(), isValidVar);
        allVars.shrink_(allVars.end() - newEnd);
        if (allVars.size() > 0) {
//            std::cout << "Before variable elimination: " << logic.printTerm(newInterpretedBody) << std::endl;
            newInterpretedBody = TrivialQuantifierElimination(logic).tryEliminateVars(allVars, newInterpretedBody);
//            std::cout << "After variable elimination: " << logic.printTerm(newInterpretedBody) << std::endl;
        }
        auto varsAfterElimination = utils.getVars(newInterpretedBody);
        auto localsEnd = std::remove_if(varsAfterElimination.begin(), varsAfterElimination.end(), isValidVar);
        if (localsEnd != varsAfterElimination.begin()) {
            // there are some local variables left, rename them and make them versioned
            subst.clear();
            for (auto it = varsAfterElimination.begin(); it != localsEnd; ++it) {
                PTRef localVar = *it;
                SRef sort = logic.getSortRef(localVar);
                std::string uniq_name = "aux#" + std::to_string(counter++);
                PTRef renamed = timeMachine.getVarVersionZero(uniq_name, sort);
                subst.insert({localVar, renamed});
            }
            newInterpretedBody = utils.varSubstitute(newInterpretedBody, subst);
        }
    }
    ////////////////////// END OF DEALING with LOCAL VARIABLES /////////////////////////

    return ChClause{clause.head, ChcBody{newInterpretedBody, clause.body.uninterpretedPart}};
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
        topLevelEqualities.push(logic.mkEq(targetVar, arg));
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
            PTRef narg = logic.getPterm(sourceTerm)[i];
            topLevelEqualities.push(logic.mkEq(narg, arg));
        }
        newUninterpretedPart.push_back(UninterpretedPredicate{sourceTerm});
    }
    // interpreted part
    // just add the toplevel equalities collected for this clause; Here we assume 'head' has already been processed
    PTRef newInterpretedPart = logic.mkAnd(body.interpretedPart.fla, logic.mkAnd(topLevelEqualities));

    newInterpretedPart = eliminateItes(newInterpretedPart);
    newInterpretedPart = eliminateDivMod(newInterpretedPart);
    return ChcBody{InterpretedFla{newInterpretedPart}, std::move(newUninterpretedPart)};
}

PTRef Normalizer::eliminateDivMod(PTRef fla) {
    LIALogic * lialogic = dynamic_cast<LIALogic *>(&logic);
    if (lialogic) {
        return DivModRewriter(*lialogic).rewrite(fla);
    }
    return fla;
}

PTRef Normalizer::eliminateItes(PTRef fla) {
    return IteHandler(logic).rewrite(fla);
}
