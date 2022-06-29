/*
 * Copyright (c) 2022, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "FalseClauseRemoval.h"

Transformer::TransformationResult FalseClauseRemoval::transform(std::unique_ptr<ChcDirectedHyperGraph> graph) {
    graph->deleteFalseEdges();
    return {std::move(graph), std::make_unique<BackTranslator>()};
}
