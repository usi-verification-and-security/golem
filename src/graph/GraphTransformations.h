//
// Created by Martin Blicha on 30.11.21.
//

#ifndef GOLEM_GRAPHTRANSFORMATIONS_H
#define GOLEM_GRAPHTRANSFORMATIONS_H

#include "ChcGraph.h"

class GraphTransformations {
    Logic & logic;
public:
    GraphTransformations(Logic & logic) : logic(logic) {}

    ChcDirectedGraph eliminateNodes(ChcDirectedGraph const & graph);

    // Simple node is a node with max one incoming or outgoing edges
    void eliminateSimpleNodes(ChcDirectedGraph & graph);
    void eliminateSimpleNodes(ChcDirectedHyperGraph & graph);

private:
    void eliminateNonLoopingNodes(ChcDirectedGraph & graph);

    void removeAlwaysValidClauses(ChcDirectedGraph & graph);

    void mergeMultiEdges(ChcDirectedGraph & graph);
};


#endif //GOLEM_GRAPHTRANSFORMATIONS_H
