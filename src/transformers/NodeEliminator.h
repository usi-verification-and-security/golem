/*
 * Copyright (c) 2022-2025, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef GOLEM_NODEELIMINATOR_H
#define GOLEM_NODEELIMINATOR_H

#include "Transformer.h"

namespace golem {
/*
 * Transformation pass that eliminates some nodes from the graph, using contraction.
 *
 * The predicate determining the nodes to eliminate is passed to the constructor.
 */
class NodeEliminator : public Transformer {
    using predicate_t = std::function<bool(SymRef,AdjacencyListsGraphRepresentation const &, ChcDirectedHyperGraph const &)>;
public:
    explicit NodeEliminator(predicate_t shouldEliminateNode) : shouldEliminateNode(std::move(shouldEliminateNode)) {}

    TransformationResult transform(std::unique_ptr<ChcDirectedHyperGraph> graph) override;

    class BackTranslator : public WitnessBackTranslator {
    public:
        using ContractionResult = ChcDirectedHyperGraph::VertexContractionResult;

        BackTranslator(Logic & logic, NonlinearCanonicalPredicateRepresentation predicateRepresentation)
        : logic(logic), predicateRepresentation(std::move(predicateRepresentation)) {}

        InvalidityWitness translate(InvalidityWitness witness) override;

        ValidityWitness translate(ValidityWitness witness) override;

        void notifyRemovedVertex(SymRef sym, ContractionResult && edges);
    private:
        std::unordered_map<SymRef, ContractionResult, SymRefHash> nodeInfo;
        std::vector<SymRef> removedNodes;
        Logic & logic;
        NonlinearCanonicalPredicateRepresentation predicateRepresentation;
    };

    predicate_t shouldEliminateNode;
};

struct SimpleNodeEliminatorPredicate {
    bool operator()(SymRef, AdjacencyListsGraphRepresentation const &, ChcDirectedHyperGraph const & graph) const;
};

class SimpleNodeEliminator : public NodeEliminator {
public:
    SimpleNodeEliminator() : NodeEliminator(SimpleNodeEliminatorPredicate()) {}
};
} // namespace golem

#endif //GOLEM_NODEELIMINATOR_H
