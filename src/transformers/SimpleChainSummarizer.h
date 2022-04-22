/*
 * Copyright (c) 2022, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef GOLEM_SIMPLECHAINSUMMARIZER_H
#define GOLEM_SIMPLECHAINSUMMARIZER_H

#include "Transformer.h"

class SimpleChainSummarizer : public Transformer {
public:
    TransformationResult transform(std::unique_ptr<ChcDirectedHyperGraph> graph) override;

    SimpleChainSummarizer(Logic & logic) : logic(logic) {}

    class SimpleChainBackTranslator : public WitnessBackTranslator {
    public:
        InvalidityWitness translate(InvalidityWitness witness) override;

        ValidityWitness translate(ValidityWitness witness) override;

        using SummarizedChain = std::pair<std::vector<DirectedHyperEdge>, DirectedHyperEdge>;

        void addSummarizedChain(SummarizedChain && chain) { summarizedChains.push_back(std::move(chain)); }

    private:
        std::vector<SummarizedChain> summarizedChains;
    };
private:
    Logic & logic;

};


#endif //GOLEM_SIMPLECHAINSUMMARIZER_H
