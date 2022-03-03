//
// Created by Martin Blicha on 30.11.21.
//

#include "GraphTransformations.h"

namespace {
std::vector<EId> getSelfLoops(ChcDirectedGraph const & graph) {
    auto edges = graph.getEdges();
    edges.erase(std::remove_if(edges.begin(), edges.end(), [&graph](EId edge) {
        return graph.getSource(edge) != graph.getTarget(edge);
    }), edges.end());
    return edges;
}

std::unordered_set<VId, VertexHasher> getNodesWithSelfLoop(ChcDirectedGraph const & graph){
    auto selfLoops = getSelfLoops(graph);
    std::unordered_set<VId, VertexHasher> selfLoopNodes;
    std::transform(selfLoops.begin(), selfLoops.end(), std::inserter(selfLoopNodes, selfLoopNodes.end()), [&graph](EId eid) {
       assert(graph.getEdge(eid).from == graph.getEdge(eid).to);
       return graph.getEdge(eid).from;
    });
    return selfLoopNodes;
}
}

ChcDirectedGraph GraphTransformations::eliminateNodes(const ChcDirectedGraph & graph) {
    ChcDirectedGraph copy = graph;
    eliminateNonLoopingNodes(copy);
    removeAlwaysValidClauses(copy);
    mergeMultiEdges(copy);
    return copy;
}

void GraphTransformations::eliminateNonLoopingNodes(ChcDirectedGraph & graph) {
    while(true) {
        auto selfLoopNodes = getNodesWithSelfLoop(graph);
        auto vertices = graph.getVertices();
        vertices.erase(std::remove_if(vertices.begin(), vertices.end(), [&](VId vid) {
            return selfLoopNodes.find(vid) != selfLoopNodes.end() or vid == graph.getEntryId() or
                   vid == graph.getExitId();
        }), vertices.end());
        if (vertices.empty()) { return; }
        graph.contractVertex(vertices[0], logic);
    }
}

void GraphTransformations::removeAlwaysValidClauses(ChcDirectedGraph & graph) {
    graph.removeEdges([this](DirectedEdge const & edge) { return edge.fla.fla == logic.getTerm_false(); });
}

void GraphTransformations::mergeMultiEdges(ChcDirectedGraph & graph) {
    graph.mergeMultiEdges(logic);
}

void GraphTransformations::eliminateSimpleNodes(ChcDirectedGraph & graph) {
//    std::cout << graph.getVertices().size() << std::endl;
    while(true) {
        AdjacencyListsGraphRepresentation adjacencyList = AdjacencyListsGraphRepresentation::from(graph);
        auto vertices = graph.getVertices();
        vertices.erase(std::remove_if(vertices.begin(), vertices.end(), [&](VId vid) {
            return not((adjacencyList.getIncomingEdgesFor(vid).size() == 1 and adjacencyList.getOutgoingEdgesFor(vid).size() >= 1)
            or (adjacencyList.getIncomingEdgesFor(vid).size() >= 1 and adjacencyList.getOutgoingEdgesFor(vid).size() == 1));
        }), vertices.end());
        if (vertices.empty()) { break; }
        graph.contractVertex(vertices[0], logic);
    }
//    std::cout << graph.getVertices().size() << std::endl;
}