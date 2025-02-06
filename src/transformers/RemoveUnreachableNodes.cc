/*
 * Copyright (c) 2022-2025, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "RemoveUnreachableNodes.h"

Transformer::TransformationResult RemoveUnreachableNodes::transform(std::unique_ptr<ChcDirectedHyperGraph> graph) {
    auto adjacencyLists = AdjacencyListsGraphRepresentation::from(*graph);
    auto allNodes = adjacencyLists.getNodes();
    auto & logic = graph->getLogic();

    if (adjacencyLists.getIncomingEdgesFor(graph->getExit()).empty() or
        adjacencyLists.getOutgoingEdgesFor(graph->getEntry()).empty()) {
        // All edges can be removed
        // We return empty graph, and remember all removed vertices for backtranslation
        allNodes.erase(std::remove_if(allNodes.begin(), allNodes.end(), [&](SymRef node) {
            return node == graph->getEntry() or node == graph->getExit();
        }), allNodes.end());
        auto backtranslator = adjacencyLists.getIncomingEdgesFor(graph->getExit()).empty() ?
            std::make_unique<BackTranslator>(graph->getLogic(), std::vector<SymRef>{}, std::move(allNodes)) :
            std::make_unique<BackTranslator>(graph->getLogic(), std::move(allNodes), std::vector<SymRef>{});
        return {
            ChcDirectedHyperGraph::makeEmpty(logic),
            std::move(backtranslator)
        };
    }

    std::unordered_set<SymRef, SymRefHash> backwardReachable;

    vec<SymRef> queue;
    queue.push(graph->getExit());
    backwardReachable.insert(graph->getExit());
    backwardReachable.insert(graph->getEntry());
    while (queue.size_() > 0) {
        auto vertex = queue.last();
        queue.pop();
        for (auto incomingId : adjacencyLists.getIncomingEdgesFor(vertex)) {
            auto const & sources = graph->getSources(incomingId);
            for (auto source : sources) {
                auto inserted = backwardReachable.insert(source);
                if (inserted.second) {
                    queue.push(source);
                }
            }
        }
    }

    std::vector<SymRef> removedNodes;

    for (auto node : allNodes) {
        if (backwardReachable.find(node) == backwardReachable.end()) {
            removedNodes.push_back(node);
            graph->deleteNode(node);
        }
    }

    return {std::move(graph), std::make_unique<BackTranslator>(logic, std::vector<SymRef>{}, std::move(removedNodes))};
}

ValidityWitness RemoveUnreachableNodes::BackTranslator::translate(ValidityWitness witness) {
    if (unreachableFromTrue.empty() and backwardUnreachableFromFalse.empty()) { return witness; }
    auto definitions = witness.getDefinitions();
    for (auto node : backwardUnreachableFromFalse) {
        assert(definitions.find(node) == definitions.end());
        definitions.insert({node, logic.getTerm_true()});
    }
    for (auto node : unreachableFromTrue) {
        assert(definitions.find(node) == definitions.end());
        definitions.insert({node, logic.getTerm_false()});
    }
    return ValidityWitness(std::move(definitions));
}
