/*
 * Copyright (c) 2022-2023, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef GOLEM_MULTIEDGEMERGER_H
#define GOLEM_MULTIEDGEMERGER_H

#include "Transformer.h"

class MultiEdgeMerger : public Transformer {
public:
    TransformationResult transform(std::unique_ptr<ChcDirectedHyperGraph> graph) override;

    class BackTranslator : public WitnessBackTranslator {
    public:
        BackTranslator(Logic & logic, NonlinearCanonicalPredicateRepresentation predicateRepresentation)
            : logic(logic), predicateRepresentation(std::move(predicateRepresentation)) {}

        InvalidityWitness translate(InvalidityWitness witness) override;

        ValidityWitness translate(ValidityWitness witness) override;

        using MergedEdges = ChcDirectedHyperGraph::MergedEdges;

        MergedEdges mergedEdges{};
        Logic & logic;
        NonlinearCanonicalPredicateRepresentation predicateRepresentation;
    };
};

#endif // GOLEM_MULTIEDGEMERGER_H
