/*
 * Copyright (c) 2023, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef GOLEM_TRIVIALEDGEPRUNER_H
#define GOLEM_TRIVIALEDGEPRUNER_H

#include "Transformer.h"

/**
 * This transformation removes all direct edges from entry to exit nodes, unless one of such edges has satisfiable label.
 * In such a case, the transformation returns the trivial graph with only this edge.
 */
class TrivialEdgePruner : public Transformer {
    class BackTranslator : public WitnessBackTranslator {
    public:
        BackTranslator() = default;

        explicit BackTranslator(EId satisfiableEdge);

        InvalidityWitness translate(InvalidityWitness witness) override;

        ValidityWitness translate(ValidityWitness witness) override;

    private:
        std::optional<EId> satisfiableEdge;
    };

public:
    TrivialEdgePruner() = default;

    TransformationResult transform(std::unique_ptr<ChcDirectedHyperGraph> graph) override;
};

#endif // GOLEM_TRIVIALEDGEPRUNER_H
