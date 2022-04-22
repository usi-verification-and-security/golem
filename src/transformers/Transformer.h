/*
 * Copyright (c) 2022, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */


#ifndef GOLEM_TRANSFORMER_H
#define GOLEM_TRANSFORMER_H

#include "Witnesses.h"
#include "ChcGraph.h"

#include <memory>

class WitnessBackTranslator {
public:
    virtual InvalidityWitness translate(InvalidityWitness witness) = 0;
    virtual ValidityWitness translate(ValidityWitness witness) = 0;
    virtual ~WitnessBackTranslator() = default;
    GraphVerificationResult translate(GraphVerificationResult const & result) {
        switch (result.getAnswer()) {
            case VerificationResult::SAFE:
                return GraphVerificationResult(result.getAnswer(), translate(result.getValidityWitness()));
            case VerificationResult::UNSAFE:
                return GraphVerificationResult(result.getAnswer(), translate(result.getInvalidityWitness()));
            case VerificationResult::UNKNOWN:
                return result;
        }
        throw std::logic_error("Unreachable");
    }
};

class Transformer {
public:
    using TransformationResult = std::pair<std::unique_ptr<ChcDirectedHyperGraph>, std::unique_ptr<WitnessBackTranslator>>;
    virtual TransformationResult transform(std::unique_ptr<ChcDirectedHyperGraph> graph) = 0;
    virtual ~Transformer() = default;
};

#endif //GOLEM_TRANSFORMER_H
