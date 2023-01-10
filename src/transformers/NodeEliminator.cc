/*
 * Copyright (c) 2022-2023, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "NodeEliminator.h"

#include "CommonUtils.h"

void NodeEliminator::BackTranslator::notifyRemovedVertex(SymRef sym, ContractionResult && contractionResult) {
    assert(removedNodes.count(sym) == 0);
    removedNodes.insert({sym, std::move(contractionResult)});
}

Transformer::TransformationResult NodeEliminator::transform(std::unique_ptr<ChcDirectedHyperGraph> graph) {
    auto backTranslator = std::make_unique<BackTranslator>(graph->getLogic(), graph->predicateRepresentation());
    while(true) {
        auto adjancencyRepresentation = AdjacencyListsGraphRepresentation::from(*graph);
        auto vertices = adjancencyRepresentation.getNodes();
        // ignore entry and exit, those should never be removed
        vertices.erase(std::remove_if(vertices.begin(), vertices.end(),[&graph](SymRef vertex) {
            return vertex == graph->getEntry() or vertex == graph->getExit();
        }), vertices.end());
        auto predicateWrapper = [&](SymRef vertex) {
            return this->shouldEliminateNode(vertex, adjancencyRepresentation, *graph);
        };
        auto candidateForRemovalIt = std::find_if(vertices.begin(), vertices.end(), predicateWrapper);
        if (candidateForRemovalIt == vertices.end()) { break; }
        auto vertexToRemove = *candidateForRemovalIt;
        auto contractionResult = graph->contractVertex(vertexToRemove);
        backTranslator->notifyRemovedVertex(vertexToRemove, std::move(contractionResult));
    }
    return {std::move(graph), std::move(backTranslator)};
}

bool IsNonLoopNode::operator()(
    SymRef vertex,
    AdjacencyListsGraphRepresentation const & adjacencyRepresentation,
    ChcDirectedHyperGraph const & graph
    ) const {
    // Vertex can be contracted if
    // 1. It does not have a self-loop
    // 2. If it does not have a hyperedge; TODO: Remove this constraint
    auto const & outgoing = adjacencyRepresentation.getOutgoingEdgesFor(vertex);
    if (std::any_of(outgoing.begin(), outgoing.end(), [&](EId eid){ return graph.getTarget(eid) == vertex or graph.getSources(eid).size() > 1; })) {
        return false;
    }
    auto const & incoming = adjacencyRepresentation.getIncomingEdgesFor(vertex);
    return std::none_of(incoming.begin(), incoming.end(), [&](EId eid){ return graph.getSources(eid).size() > 1; });
}

InvalidityWitness NodeEliminator::BackTranslator::translate(InvalidityWitness witness) {
    if (this->removedNodes.empty()) { return witness; }

    using ContractionInfo = std::pair<DirectedHyperEdge, std::pair<DirectedHyperEdge, DirectedHyperEdge>>;
    auto findContractionInfo = [&](EId eid) -> std::optional<ContractionInfo> {
        for (auto const & [node, contractionResult] : removedNodes) {
            for (auto const & [replacing, inout] : contractionResult.replacing) {
                if (replacing.id == eid) {
                    return std::make_pair(replacing,
                                          std::make_pair(contractionResult.incoming[inout.first],
                                                         contractionResult.outgoing[inout.second])
                                         );
                }
            }
        }
        return std::nullopt;
    };
    while(true) {
        auto & derivation = witness.getDerivation();
        // For each step, check if it uses one of the newly created edges
        bool stepReplaced = false;
        for (auto it = derivation.begin(); it != derivation.end(); ++it) {
            auto eid = it->clauseId;
            if (auto possibleContractInfo = findContractionInfo(eid); possibleContractInfo.has_value()) {
                auto const & contractionInfo = possibleContractInfo.value();
                std::vector<DirectedHyperEdge> chain = {contractionInfo.second.first, contractionInfo.second.second};
                auto const & replacingEdge = contractionInfo.first;
                std::size_t index = it - derivation.begin();
                auto newDerivation = replaceSummarizingStep(derivation, index, chain, replacingEdge, predicateRepresentation, logic);
                witness.setDerivation(std::move(newDerivation));
                stepReplaced = true;
                break;
            }
        }
        if (not stepReplaced) {
            break;
        }
    }
    return witness;
}

ValidityWitness NodeEliminator::BackTranslator::translate(ValidityWitness witness) {
    if (this->removedNodes.empty()) { return witness; }
    auto definitions = witness.getDefinitions();

    auto definitionFor = [&](SymRef vertex) {
        if (vertex == logic.getSym_false()) { return logic.getTerm_false(); }
        if (vertex == logic.getSym_true()) { return logic.getTerm_true(); }
        auto it = std::find_if(definitions.begin(), definitions.end(), [&](auto const & entry){
            return logic.getSymRef(entry.first) == vertex;
        });
        return it != definitions.end() ? it->second : PTRef_Undef;
    };
    VersionManager manager(logic);
    TermUtils utils(logic);
    for (auto && [vertex, entry] : this->removedNodes) {
        vec<PTRef> incomingFormulas;
        for (auto const & edge : entry.incoming) {
            if (edge.from.size() != 1) { throw std::logic_error("NonLoopEliminator should not have processed hyperEdges!"); }
            PTRef sourceDef = definitionFor(edge.from[0]);
            assert(sourceDef != PTRef_Undef);
            if (sourceDef == PTRef_Undef) { // Missing definition, cannot backtranslate
                return ValidityWitness{};
            }
            sourceDef = manager.baseFormulaToSource(sourceDef);
            incomingFormulas.push(logic.mkAnd(sourceDef, edge.fla.fla));
        }
        vec<PTRef> outgoingFormulas;
        for (auto const & edge : entry.outgoing) {
            if (edge.from.size() != 1) { throw std::logic_error("NonLoopEliminator should not have processed hyperEdges!"); }
            PTRef targetDef = definitionFor(edge.to);
            assert(targetDef != PTRef_Undef);
            if (targetDef == PTRef_Undef) { // Missing definition, cannot backtranslate
                return ValidityWitness{};
            }
            targetDef = manager.baseFormulaToTarget(targetDef);
            outgoingFormulas.push(logic.mkAnd(edge.fla.fla, logic.mkNot(targetDef)));
        }
        TermUtils::substitutions_map substitutionsMap;
        utils.mapFromPredicate(predicateRepresentation.getSourceTermFor(vertex), predicateRepresentation.getTargetTermFor(vertex), substitutionsMap);
        PTRef incomingPart = logic.mkOr(std::move(incomingFormulas));
        PTRef outgoingPart = logic.mkOr(std::move(outgoingFormulas));
        outgoingPart = utils.varSubstitute(outgoingPart, substitutionsMap);
        SMTConfig config;
        const char * msg;
        config.setOption(SMTConfig::o_produce_models, SMTOption(false), msg);
        config.setOption(SMTConfig::o_produce_inter, SMTOption(true), msg);
        MainSolver solver(logic, config, "solver");
        solver.insertFormula(incomingPart);
        solver.insertFormula(outgoingPart);
        auto res = solver.check();
        if (res != s_False) {
            throw std::logic_error("Error in backtranslating of nonloops elimination");
        }
        auto itpContext = solver.getInterpolationContext();
        vec<PTRef> itps;
        ipartitions_t Amask = 1;
        itpContext->getSingleInterpolant(itps, Amask);
        PTRef vertexSolution = manager.targetFormulaToBase(itps[0]);
        PTRef predicate = manager.sourceFormulaToBase(predicateRepresentation.getSourceTermFor(vertex));
        assert(definitions.count(predicate) == 0);
        definitions.insert({predicate, vertexSolution});
    }
    return ValidityWitness(std::move(definitions));
}