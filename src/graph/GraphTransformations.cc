//
// Created by Martin Blicha on 30.11.21.
//

#include "GraphTransformations.h"

namespace {
std::vector<EId> getSelfLoops(ChcDirectedGraph const & graph) {
    std::vector<EId> selfLoops;
    graph.forEachEdge([&](DirectedEdge const & edge){
       if (edge.from == edge.to) {
           selfLoops.push_back(edge.id);
       }
    });
    return selfLoops;
}

auto getNodesWithSelfLoop(ChcDirectedGraph const & graph){
    auto selfLoops = getSelfLoops(graph);
    std::unordered_set<SymRef, SymRefHash> selfLoopNodes;
    std::transform(selfLoops.begin(), selfLoops.end(), std::inserter(selfLoopNodes, selfLoopNodes.end()), [&graph](EId eid) {
       assert(graph.getSource(eid) == graph.getTarget(eid));
       return graph.getSource(eid);
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
        vertices.erase(std::remove_if(vertices.begin(), vertices.end(), [&](auto vid) {
            return selfLoopNodes.find(vid) != selfLoopNodes.end() or vid == graph.getEntry() or
                   vid == graph.getExit();
        }), vertices.end());
        if (vertices.empty()) { return; }
        graph.contractVertex(vertices[0]);
    }
}

void GraphTransformations::removeAlwaysValidClauses(ChcDirectedGraph & graph) {
    graph.deleteMatchingEdges([this](DirectedEdge const & edge) { return edge.fla.fla == logic.getTerm_false(); });
}

void GraphTransformations::mergeMultiEdges(ChcDirectedGraph & graph) {
    graph.mergeMultiEdges();
}