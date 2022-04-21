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

    };
private:
    Logic & logic;

};


#endif //GOLEM_SIMPLECHAINSUMMARIZER_H
