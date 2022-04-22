/*
 * Copyright (c) 2022, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "SimpleChainSummarizer.h"

Transformer::TransformationResult SimpleChainSummarizer::transform(std::unique_ptr<ChcDirectedHyperGraph> graph) {
    auto translator = std::make_unique<SimpleChainBackTranslator>();
    while(true) {
        AdjacencyListsGraphRepresentation adjacencyList = AdjacencyListsGraphRepresentation::from(*graph);
        auto isTrivial = [&](SymRef sym) {
            if (adjacencyList.getIncomingEdgesFor(sym).size() != 1) { return false; }
            auto out = adjacencyList.getOutgoingEdgesFor(sym);
            if (out.size() != 1) { return false; }
            return graph->getSources(out[0]).size() == 1;
        };
        auto vertices = graph->getVertices();
        auto it = std::find_if(vertices.begin(), vertices.end(), isTrivial);
        if (it == vertices.end()) { break; }
        auto trivialVertex = *it;
        auto trivialChain = [&](SymRef vertex) {
            std::vector<EId> edges;
            auto current = vertex;
            do {
                auto const & outgoing = adjacencyList.getOutgoingEdgesFor(current);
                assert(outgoing.size() == 1);
                edges.push_back(outgoing[0]);
                current = graph->getTarget(outgoing[0]);
            } while (isTrivial(current));
            current = vertex;
            do {
                auto const & incoming = adjacencyList.getIncomingEdgesFor(current);
                assert(incoming.size() == 1);
                edges.insert(edges.begin(), incoming[0]);
                auto const & sources = graph->getSources(incoming[0]);
                assert(sources.size() == 1);
                current = sources[0];
            } while (isTrivial(current));
            return edges;
        }(trivialVertex);
        std::vector<DirectedHyperEdge> summarizedChain;
        std::transform(trivialChain.begin(), trivialChain.end(), std::back_inserter(summarizedChain), [&](EId eid) {
            return graph->getEdge(eid);
        });
        auto summaryEdge = graph->contractTrivialChain(trivialChain);
        translator->addSummarizedChain({summarizedChain, summaryEdge});
    }
    return {std::move(graph), std::move(translator)};
}

InvalidityWitness SimpleChainSummarizer::SimpleChainBackTranslator::translate(InvalidityWitness witness) {
    return InvalidityWitness();
}

ValidityWitness SimpleChainSummarizer::SimpleChainBackTranslator::translate(ValidityWitness witness) {
    return ValidityWitness();
}
