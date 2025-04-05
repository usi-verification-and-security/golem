/*
 * Copyright (c) 2022-2025, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "RemoveUnreachableNodes.h"

namespace golem {
namespace {
std::vector<SymRef> computeBackwardUnreachable(ChcDirectedHyperGraph const & graph,
                                               AdjacencyListsGraphRepresentation const & adjacencyLists) {
    std::unordered_set<SymRef, SymRefHash> backwardReachable;
    std::vector<SymRef> queue;
    queue.push_back(graph.getExit());
    backwardReachable.insert(graph.getExit());
    backwardReachable.insert(graph.getEntry());
    while (not queue.empty()) {
        auto vertex = queue.back();
        queue.pop_back();
        for (auto incomingId : adjacencyLists.getIncomingEdgesFor(vertex)) {
            auto const & sources = graph.getSources(incomingId);
            for (auto source : sources) {
                auto inserted = backwardReachable.insert(source);
                if (inserted.second) { queue.push_back(source); }
            }
        }
    }

    std::vector<SymRef> backwardUnreachable;
    for (auto node : adjacencyLists.getNodes()) {
        if (backwardReachable.find(node) == backwardReachable.end()) { backwardUnreachable.push_back(node); }
    }
    return backwardUnreachable;
}

std::vector<SymRef> computeForwardUnreachable(ChcDirectedHyperGraph const & graph,
                                              AdjacencyListsGraphRepresentation const & adjacencyLists) {
    std::vector<SymRef> queue;
    std::unordered_set<SymRef, SymRefHash> forwardReachable;
    forwardReachable.insert(graph.getEntry());
    queue.push_back(graph.getEntry());
    while (not queue.empty()) {
        auto node = queue.back();
        queue.pop_back();
        for (EId eid : adjacencyLists.getOutgoingEdgesFor(node)) {
            auto target = graph.getTarget(eid);
            if (forwardReachable.count(target)) { continue; }
            auto const & sources = graph.getSources(eid);
            bool allSourcesReachable = std::all_of(sources.begin(), sources.end(),
                                                   [&](auto source) { return forwardReachable.count(source); });
            if (allSourcesReachable) {
                forwardReachable.insert(target);
                queue.push_back(target);
            }
        }
    }

    std::vector<SymRef> forwardUnreachable;
    for (auto node : adjacencyLists.getNodes()) {
        if (forwardReachable.find(node) == forwardReachable.end()) { forwardUnreachable.push_back(node); }
    }
    return forwardUnreachable;
}

} // namespace

Transformer::TransformationResult RemoveUnreachableNodes::transform(std::unique_ptr<ChcDirectedHyperGraph> graph) {
    auto adjacencyLists = AdjacencyListsGraphRepresentation::from(*graph);
    auto & logic = graph->getLogic();

    if (adjacencyLists.getIncomingEdgesFor(graph->getExit()).empty() or
        adjacencyLists.getOutgoingEdgesFor(graph->getEntry()).empty()) {
        // All edges can be removed
        // We return empty graph, and remember all removed vertices for backtranslation
        auto allNodes = adjacencyLists.getNodes();
        allNodes.erase(
            std::remove_if(allNodes.begin(), allNodes.end(),
                           [&](SymRef node) { return node == graph->getEntry() or node == graph->getExit(); }),
            allNodes.end());
        auto backtranslator =
            adjacencyLists.getIncomingEdgesFor(graph->getExit()).empty()
                ? std::make_unique<BackTranslator>(graph->getLogic(), std::vector<SymRef>{}, std::move(allNodes))
                : std::make_unique<BackTranslator>(graph->getLogic(), std::move(allNodes), std::vector<SymRef>{});
        return {ChcDirectedHyperGraph::makeEmpty(logic), std::move(backtranslator)};
    }

    auto backwardUnreachable = computeBackwardUnreachable(*graph, adjacencyLists);
    for (auto node : backwardUnreachable) {
        graph->deleteNode(node);
    }
    if (not backwardUnreachable.empty()) { adjacencyLists = AdjacencyListsGraphRepresentation::from(*graph); }
    auto forwardUnreachable = computeForwardUnreachable(*graph, adjacencyLists);
    for (auto node : forwardUnreachable) {
        graph->deleteNode(node);
    }

    return {std::move(graph),
            std::make_unique<BackTranslator>(logic, std::move(forwardUnreachable), std::move(backwardUnreachable))};
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
} // namespace golem