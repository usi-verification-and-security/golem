/*
 * Copyright (c) 2022, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "MultiEdgeMerger.h"

Transformer::TransformationResult MultiEdgeMerger::transform(std::unique_ptr<ChcDirectedHyperGraph> graph) {
    auto backtranslator = std::make_unique<BackTranslator>();
    backtranslator->somethingChanged = graph->mergeMultiEdges();
    return {std::move(graph), std::move(backtranslator)};
}

InvalidityWitness MultiEdgeMerger::BackTranslator::translate(InvalidityWitness witness) {
    if (somethingChanged) {
        return InvalidityWitness();
    } else {
        return witness;
    }
}

ValidityWitness MultiEdgeMerger::BackTranslator::translate(ValidityWitness witness) {
    return witness;
}
