/*
 * Copyright (c) 2024, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef EDGEINLINER_H
#define EDGEINLINER_H

#include "Transformer.h"

class EdgeInliner : public Transformer {

public:
    TransformationResult transform(std::unique_ptr<ChcDirectedHyperGraph> graph) override;

    class BackTranslator : public WitnessBackTranslator {
        using ReplacementInfo = std::vector<std::pair<DirectedHyperEdge, std::pair<DirectedHyperEdge, DirectedHyperEdge>>>;
        Logic & logic;
        NonlinearCanonicalPredicateRepresentation predicateRepresentation;
    public:
        ReplacementInfo replacementInfo;

        BackTranslator(Logic & logic, NonlinearCanonicalPredicateRepresentation predicateRepresentation)
        : logic(logic), predicateRepresentation(std::move(predicateRepresentation)) {}

        InvalidityWitness translate(InvalidityWitness witness) override;
        ValidityWitness translate(ValidityWitness witness) override { return witness; }
    };
};



#endif //EDGEINLINER_H
