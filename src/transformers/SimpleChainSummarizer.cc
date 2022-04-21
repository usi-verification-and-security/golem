/*
 * Copyright (c) 2022, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "SimpleChainSummarizer.h"

Transformer::TransformationResult SimpleChainSummarizer::transform(std::unique_ptr<ChcDirectedHyperGraph> graph) {
    while(true) {
        AdjacencyListsGraphRepresentation adjacencyList = AdjacencyListsGraphRepresentation::from(*graph);
        auto isTrivial = [&](VId vid) {
            if (adjacencyList.getIncomingEdgesFor(vid).size() != 1) { return false; }
            auto out = adjacencyList.getOutgoingEdgesFor(vid);
            if (out.size() != 1) { return false; }
            return graph->getEdge(out[0]).from.size() == 1;
        };
        auto vertices = graph->getVertices();
        auto it = std::find_if(vertices.begin(), vertices.end(), isTrivial);
        if (it == vertices.end()) { break; }
        VId trivialVId = *it;
        graph->contractTrivialVertex(trivialVId, adjacencyList.getIncomingEdgesFor(trivialVId)[0], adjacencyList.getOutgoingEdgesFor(trivialVId)[0], logic);
    }
    return {std::move(graph), std::make_unique<SimpleChainBackTranslator>()};
}

InvalidityWitness SimpleChainSummarizer::SimpleChainBackTranslator::translate(InvalidityWitness witness) {
    return InvalidityWitness();
}

ValidityWitness SimpleChainSummarizer::SimpleChainBackTranslator::translate(ValidityWitness witness) {
    return ValidityWitness();
}
