/*
 * Copyright (c) 2022-2023, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef GOLEM_NODEELIMINATOR_H
#define GOLEM_NODEELIMINATOR_H

#include "Transformer.h"

/*
 * Transformation pass that eliminates some nodes from the graph, using contraction.
 *
 * The predicate determining the nodes to eliminate is passed to the constructor.
 */
class NodeEliminator : public Transformer {
    using predicate_t = std::function<bool(SymRef,AdjacencyListsGraphRepresentation const &, ChcDirectedHyperGraph const &)>;
public:
    NodeEliminator(predicate_t shouldEliminateNode) : shouldEliminateNode(std::move(shouldEliminateNode)) {}

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
        std::unordered_map<SymRef, ContractionResult, SymRefHash> removedNodes;
        Logic & logic;
        NonlinearCanonicalPredicateRepresentation predicateRepresentation;
    };

    predicate_t shouldEliminateNode;
};

struct NonLoopEliminatorPredicate {
    bool operator()(SymRef, AdjacencyListsGraphRepresentation const &, ChcDirectedHyperGraph const & graph) const;
};

class NonLoopEliminator : public NodeEliminator {
public:
    NonLoopEliminator() : NodeEliminator(NonLoopEliminatorPredicate{}) {}
};

struct SimpleNodeEliminatorPredicate {
    bool operator()(SymRef, AdjacencyListsGraphRepresentation const &, ChcDirectedHyperGraph const & graph) const;
};

class SimpleNodeEliminator : public NodeEliminator {
public:
    SimpleNodeEliminator() : NodeEliminator(SimpleNodeEliminatorPredicate()) {}
};

#endif //GOLEM_NODEELIMINATOR_H
