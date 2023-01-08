/*
 * Copyright (c) 2023, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef GOLEM_COMMONUTILS_H
#define GOLEM_COMMONUTILS_H

#include "graph/ChcGraph.h"
#include "Witnesses.h"

class EdgeConverter {
    Logic & logic;
    TermUtils utils;
    TimeMachine timeMachine;
    VersionManager manager;
    NonlinearCanonicalPredicateRepresentation const & predicateRepresentation;
public:
    EdgeConverter(Logic & logic, NonlinearCanonicalPredicateRepresentation const & predicateRepresentation) :
        logic(logic), utils(logic), timeMachine(logic), manager(logic), predicateRepresentation(predicateRepresentation) {}

    DirectedEdge operator()(DirectedHyperEdge const & edge) {
        assert(edge.from.size() == 1);
        auto source = edge.from[0];
        auto target = edge.to;
        TermUtils::substitutions_map subst;
        {
            auto sourceVars = utils.predicateArgsInOrder(predicateRepresentation.getSourceTermFor(source));
            for (PTRef sourceVar : sourceVars) {
                PTRef newVar = timeMachine.getVarVersionZero(manager.toBase(sourceVar));
                subst.insert({sourceVar, newVar});
            }
        }
        {
            auto targetVars = utils.predicateArgsInOrder(predicateRepresentation.getTargetTermFor(target));
            for (PTRef targetVar : targetVars) {
                PTRef newVar = timeMachine.sendVarThroughTime(timeMachine.getVarVersionZero(manager.toBase(targetVar)), 1);
                subst.insert({targetVar, newVar});
            }
        }

        PTRef newLabel = TermUtils(logic).varSubstitute(edge.fla.fla, subst);
        return DirectedEdge{.from = edge.from[0], .to = edge.to, .fla = {newLabel}, .id = {edge.id}};
    }
};

class VersionedPredicate {
    Logic & logic;
    TermUtils utils;
    TimeMachine timeMachine;
    VersionManager manager;
    NonlinearCanonicalPredicateRepresentation const & predicateRepresentation;
public:
    VersionedPredicate(Logic & logic, NonlinearCanonicalPredicateRepresentation const & predicateRepresentation) :
        logic(logic), utils(logic), timeMachine(logic), manager(logic), predicateRepresentation(predicateRepresentation) {}

    PTRef operator()(SymRef predicateSymbol) {
        vec<PTRef> baseVars;
        auto sourceVars = utils.predicateArgsInOrder(predicateRepresentation.getSourceTermFor(predicateSymbol));
        for (PTRef sourceVar : sourceVars) {
            PTRef newVar = timeMachine.getVarVersionZero(manager.toBase(sourceVar));
            baseVars.push(newVar);
        }
        return logic.insertTerm(predicateSymbol, std::move(baseVars));
    }
};

InvalidityWitness::Derivation replaceSummarizingStep(
    InvalidityWitness::Derivation const & derivation,
    std::size_t stepIndex,
    std::vector<DirectedHyperEdge> const & replacedChain,
    DirectedHyperEdge const & replacingEdge,
    NonlinearCanonicalPredicateRepresentation const & predicateRepresentation,
    Logic & logic
    );

#endif //GOLEM_COMMONUTILS_H
