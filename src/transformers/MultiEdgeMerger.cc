/*
 * Copyright (c) 2022-2023, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "MultiEdgeMerger.h"

Transformer::TransformationResult MultiEdgeMerger::transform(std::unique_ptr<ChcDirectedHyperGraph> graph) {
    auto backtranslator = std::make_unique<BackTranslator>(graph->getLogic(), graph->predicateRepresentation());
    backtranslator->mergedEdges = graph->mergeMultiEdges();
    return {std::move(graph), std::move(backtranslator)};
}

InvalidityWitness MultiEdgeMerger::BackTranslator::translate(InvalidityWitness witness) {
    if (mergedEdges.empty()) { return witness; }
    auto & derivation = witness.getDerivation();
    for (auto & step : derivation) {
        auto eid = step.clauseId;
        auto it = std::find_if(mergedEdges.begin(), mergedEdges.end(),
                               [eid](auto const & mergedEntry) { return mergedEntry.second.id == eid; });
        if (it == mergedEdges.end()) { continue; }
        auto const & replacedEdges = it->first;
        auto const & replacingEdge = it->second;
        // Figure out which of the replaced edges can be used to derive the same fact
        TermUtils utils(logic);
        TermUtils::substitutions_map subst;
        { // build the substitution map
            auto fillVariables = [&](PTRef derivedFact, PTRef normalizedPredicate) {
                assert(logic.getSymRef(derivedFact) == logic.getSymRef(normalizedPredicate));
                auto const & term = logic.getPterm(derivedFact);
                (void)term;
                assert(std::all_of(term.begin(), term.end(), [&](PTRef arg) { return logic.isConstant(arg); }));
                utils.mapFromPredicate(normalizedPredicate, derivedFact, subst);
            };
            // collect values from the derived fact
            auto targetVertex = replacingEdge.to;
            assert(predicateRepresentation.hasRepresentationFor(targetVertex));
            PTRef targetTerm = predicateRepresentation.getTargetTermFor(targetVertex);
            PTRef derivedFact = step.derivedFact;
            assert(logic.getPterm(targetTerm).size() == logic.getPterm(derivedFact).size());
            assert(logic.getSymRef(targetTerm) == targetVertex and logic.getSymRef(derivedFact) == targetVertex);
            fillVariables(derivedFact, targetTerm);
            // and collect values from the premise as well
            auto const & premises = step.premises;
            assert(premises.size() == 1); // TODO: Generalize this when we generalize MultiEdgeMerge to HyperEdges
            auto const & premiseStep = derivation[premises[0]];
            auto sourceVertex = replacingEdge.from[0];
            PTRef premise = premiseStep.derivedFact;
            PTRef sourceTerm = predicateRepresentation.getSourceTermFor(sourceVertex);
            assert(logic.getPterm(sourceTerm).size() == logic.getPterm(premise).size());
            assert(logic.getSymRef(sourceTerm) == sourceVertex and logic.getSymRef(premise) == sourceVertex);
            fillVariables(premise, sourceTerm);
        } // substitution map is built

        auto chosenEdgeIndex = [&]() -> std::optional<std::size_t> {
            std::vector<PTRef> evaluatedLabels;
            for (std::size_t i = 0u; i < replacedEdges.size(); ++i) {
                PTRef evaluatedLabel = utils.varSubstitute(replacedEdges[i].fla.fla, subst);
                if (evaluatedLabel == logic.getTerm_true()) { return i; }
                evaluatedLabels.push_back(evaluatedLabel);
            }
            // No edge evaluate to true, try to find one with satisfiable label
            for (std::size_t i = 0u; i < evaluatedLabels.size(); ++i) {
                if (evaluatedLabels[i] == logic.getTerm_false()) { continue; }
                SMTConfig config;
                MainSolver solver(logic, config, "");
                solver.insertFormula(evaluatedLabels[i]);
                if (solver.check() == s_True) { return i; }
            }
            return {};
        }();
        if (not chosenEdgeIndex.has_value()) {
            return InvalidityWitness{}; // TODO: Change API to allow return NoWitness with reason
        }
        auto const & chosenEdge = replacedEdges[chosenEdgeIndex.value()];
        step.clauseId = chosenEdge.id;
    }
    return witness;
}

ValidityWitness MultiEdgeMerger::BackTranslator::translate(ValidityWitness witness) {
    return witness;
}
