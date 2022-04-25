/*
 * Copyright (c) 2022, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef GOLEM_NONLOOPELIMINATOR_H
#define GOLEM_NONLOOPELIMINATOR_H

#include "Transformer.h"

/*
 * Tries to eliminate all nodes that do not have a self-loop edge
 */
class NonLoopEliminator : public Transformer {
public:
    TransformationResult transform(std::unique_ptr<ChcDirectedHyperGraph> graph) override;

    class BackTranslator : public WitnessBackTranslator {
    public:
        struct Entry {
            std::vector<DirectedHyperEdge> incoming;
            std::vector<DirectedHyperEdge> outgoing;
        };

        BackTranslator(Logic & logic, NonlinearCanonicalPredicateRepresentation predicateRepresentation)
        : logic(logic), predicateRepresentation(std::move(predicateRepresentation)) {}

        InvalidityWitness translate(InvalidityWitness witness) override;

        ValidityWitness translate(ValidityWitness witness) override;

        void notifyRemovedVertex(SymRef sym, Entry edges);
    private:
        std::unordered_map<SymRef, Entry, SymRefHash> removedNodes;
        Logic & logic;
        NonlinearCanonicalPredicateRepresentation predicateRepresentation;
    };

private:
    std::vector<SymRef> nonloopingVertices(ChcDirectedHyperGraph const & graph, AdjacencyListsGraphRepresentation const &);

};


#endif //GOLEM_NONLOOPELIMINATOR_H
