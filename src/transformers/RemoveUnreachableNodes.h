/*
 * Copyright (c) 2022, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef GOLEM_REMOVEUNREACHABLENODES_H
#define GOLEM_REMOVEUNREACHABLENODES_H

#include "Transformer.h"

class RemoveUnreachableNodes : public Transformer {
public:
    TransformationResult transform(std::unique_ptr<ChcDirectedHyperGraph> graph) override;

    class BackTranslator : public WitnessBackTranslator {
        Logic & logic;
        NonlinearCanonicalPredicateRepresentation predicateRepresentation;
        std::vector<SymRef> removedNodes;

    public:
        BackTranslator(Logic & logic, NonlinearCanonicalPredicateRepresentation predicateRepresentation, std::vector<SymRef> && removedNodes) :
            logic(logic),
            predicateRepresentation(std::move(predicateRepresentation)),
            removedNodes(std::move(removedNodes))
            {}

        InvalidityWitness translate(InvalidityWitness witness) override { return witness; }
        ValidityWitness translate(ValidityWitness witness) override;
    };
};


#endif //GOLEM_REMOVEUNREACHABLENODES_H
