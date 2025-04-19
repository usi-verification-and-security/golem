/*
 * Copyright (c) 2022-2025, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */


#ifndef GOLEM_TRANSFORMER_H
#define GOLEM_TRANSFORMER_H

#include "Witnesses.h"

#include <memory>

namespace golem {
class WitnessBackTranslator {
public:
    virtual InvalidityWitness translate(InvalidityWitness witness) = 0;
    virtual ValidityWitness translate(ValidityWitness witness) = 0;
    virtual ~WitnessBackTranslator() = default;
    VerificationResult translate(VerificationResult && result) {
        if (not result.hasWitness()) { return std::move(result); }
        auto answer = result.getAnswer();
        switch (answer) {
            case VerificationAnswer::SAFE:
                return {answer, translate(std::move(result).getValidityWitness())};
            case VerificationAnswer::UNSAFE:
                return {answer, translate(std::move(result).getInvalidityWitness())};
            case VerificationAnswer::UNKNOWN:
                return std::move(result);
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
} // namespace golem

#endif //GOLEM_TRANSFORMER_H
