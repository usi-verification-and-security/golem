/*
 * Copyright (c) 2022-2025, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef GOLEM_SIMPLECHAINSUMMARIZER_H
#define GOLEM_SIMPLECHAINSUMMARIZER_H

#include "Transformer.h"

namespace golem {
class SimpleChainSummarizer : public Transformer {
public:
    TransformationResult transform(std::unique_ptr<ChcDirectedHyperGraph> graph) override;

    SimpleChainSummarizer() = default;

    class BackTranslator : public WitnessBackTranslator {
    public:
        BackTranslator(Logic & logic, NonlinearCanonicalPredicateRepresentation predicateRepresentation)
        : logic(logic), predicateRepresentation(std::move(predicateRepresentation)) {}

        InvalidityWitness translate(InvalidityWitness witness) override;

        ValidityWitness translate(ValidityWitness witness) override;

        using SummarizedChain = std::pair<std::vector<DirectedHyperEdge>, DirectedHyperEdge>;

        void addSummarizedChain(SummarizedChain && chain) { summarizedChains.push_back(std::move(chain)); }

    private:
        std::vector<SummarizedChain> summarizedChains;
        Logic & logic;
        NonlinearCanonicalPredicateRepresentation predicateRepresentation;
    };
};
} // namespace golem

#endif //GOLEM_SIMPLECHAINSUMMARIZER_H
