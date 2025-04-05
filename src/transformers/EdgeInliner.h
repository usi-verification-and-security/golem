/*
 * Copyright (c) 2024-2025, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef EDGEINLINER_H
#define EDGEINLINER_H

#include "Transformer.h"

namespace golem {
class EdgeInliner : public Transformer {

public:
    TransformationResult transform(std::unique_ptr<ChcDirectedHyperGraph> graph) override;

    class BackTranslator : public WitnessBackTranslator {
        struct Deletion {
            DirectedHyperEdge deletedEdge;
        };
        struct Replacement {
            DirectedHyperEdge addedEdge;
            DirectedHyperEdge removedEdge;
            DirectedHyperEdge predecessor;
        };
        using Entry = std::variant<Deletion, Replacement>;
        using Predecessors = std::vector<DirectedHyperEdge>;

        Logic & logic;
        NonlinearCanonicalPredicateRepresentation predicateRepresentation;
        std::vector<Entry> entries;
        std::map<EId, Predecessors> predecessors; // at the time of removal
    public:
        BackTranslator(Logic & logic, NonlinearCanonicalPredicateRepresentation predicateRepresentation)
            : logic(logic), predicateRepresentation(std::move(predicateRepresentation)) {}

        InvalidityWitness translate(InvalidityWitness witness) override;
        ValidityWitness translate(ValidityWitness witness) override;

        void notifyEdgeDeleted(DirectedHyperEdge const &, Predecessors);

        void notifyEdgeReplaced(DirectedHyperEdge const & newEdge, DirectedHyperEdge const & removedEdge,
                                DirectedHyperEdge const & predecessor, Predecessors);

    private:
        std::vector<PTRef> getAuxiliaryVarsFor(SymRef node) const;

        PTRef computeInterpolantFor(SymRef node, PTRef incoming, PTRef outgoing) const;
    };
};
} // namespace golem

#endif // EDGEINLINER_H
