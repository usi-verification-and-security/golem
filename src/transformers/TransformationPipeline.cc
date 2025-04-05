
/*
 * Copyright (c) 2022-2025, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "TransformationPipeline.h"

namespace golem {
Transformer::TransformationResult TransformationPipeline::transform(std::unique_ptr<ChcDirectedHyperGraph> graph) {
    BackTranslator::pipeline_t backtranslators;
    for (auto const & transformer : inner) {
        auto result = transformer->transform(std::move(graph));
        graph = std::move(result.first);
        backtranslators.push_back(std::move(result.second));
    }
    std::reverse(backtranslators.begin(), backtranslators.end());
    return {std::move(graph), std::make_unique<BackTranslator>(std::move(backtranslators))};
}

InvalidityWitness TransformationPipeline::BackTranslator::translate(InvalidityWitness witness) {
    for (auto const & backtranslator : inner) {
        witness = backtranslator->translate(std::move(witness));
    }
    return witness;
}

ValidityWitness TransformationPipeline::BackTranslator::translate(ValidityWitness witness) {
    for (auto const & backtranslator : inner) {
        witness = backtranslator->translate(std::move(witness));
    }
    return witness;
}
} // namespace golem