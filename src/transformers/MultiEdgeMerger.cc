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
    if (mergedEdges.empty()) {
        return witness;
    }
    auto & derivation = witness.getDerivation();
    for (auto & step : derivation) {
        auto eid = step.clauseId;
        auto it = std::find_if(mergedEdges.begin(), mergedEdges.end(), [eid](auto const & mergedEntry) {
           return mergedEntry.second.id == eid;
        });
        if (it == mergedEdges.end()) { continue; }
        auto const& replacedEdges = it->first;
        auto const& replacingEdge = it->second;
        // Figure out which of the replaced edges can be used to derive the same fact
        auto model = [&]() -> std::unique_ptr<Model> {
            ModelBuilder builder(logic);
            // collect values from the derived fact
            auto targetVertex = replacingEdge.to;
            assert(predicateRepresentation.hasRepresentationFor(targetVertex));
            PTRef targetTerm = predicateRepresentation.getTargetTermFor(targetVertex);
            PTRef derivedFact = step.derivedFact;
            assert(logic.getPterm(targetTerm).size() == logic.getPterm(derivedFact).size());
            assert(logic.getSymRef(targetTerm) == targetVertex and logic.getSymRef(derivedFact) == targetVertex);
            auto argsCount = logic.getPterm(targetTerm).size();
            for (auto i = 0u; i < argsCount; ++i) {
                builder.addVarValue(logic.getPterm(targetTerm)[i], logic.getPterm(derivedFact)[i]);
            }
            // and collect values from the premise as well
            auto const& premises = step.premises;
            assert(premises.size() == 1); // TODO: Generalize this when we generalize MultiEdgeMerge to HyperEdges
            auto const& premiseStep = derivation[premises[0]];
            auto sourceVertex = replacingEdge.from[0];
            PTRef premise = premiseStep.derivedFact;
            PTRef sourceTerm = predicateRepresentation.getSourceTermFor(sourceVertex);
            assert(logic.getPterm(sourceTerm).size() == logic.getPterm(premise).size());
            assert(logic.getSymRef(sourceTerm) == sourceVertex and logic.getSymRef(premise) == sourceVertex);
            argsCount = logic.getPterm(sourceTerm).size();
            for (auto i = 0u; i < argsCount; ++i) {
                builder.addVarValue(logic.getPterm(sourceTerm)[i], logic.getPterm(premise)[i]);
            }
            return builder.build();
        }();

        auto chosenEdgeIndex = [&]() -> std::optional<std::size_t> {
            for (std::size_t i = 0u; i < replacedEdges.size(); ++i) {
                if (model->evaluate(replacedEdges[i].fla.fla) == logic.getTerm_true()) { return i; }
            }
            // No edge evaluate to true, try to find one with satisfiable label
            for (std::size_t i = 0u; i < replacedEdges.size(); ++i) {
                PTRef simplifiedLabel = model->evaluate(replacedEdges[i].fla.fla);
                if (simplifiedLabel == logic.getTerm_false()) { continue; }
                SMTConfig config;
                MainSolver solver(logic, config, "");
                solver.insertFormula(simplifiedLabel);
                if (solver.check() == s_True) { return i; }
            }
            return {};
        }();
        if (not chosenEdgeIndex.has_value()) { return InvalidityWitness{}; } // TODO: Change API to allow return NoWitness with reason
        auto const & chosenEdge = replacedEdges[chosenEdgeIndex.value()];
        step.clauseId = chosenEdge.id;
    }
    return std::move(witness);
}

ValidityWitness MultiEdgeMerger::BackTranslator::translate(ValidityWitness witness) {
    return witness;
}
