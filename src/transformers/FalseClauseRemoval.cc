/*
 * Copyright (c) 2022-2025, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "FalseClauseRemoval.h"

namespace golem {
Transformer::TransformationResult FalseClauseRemoval::transform(std::unique_ptr<ChcDirectedHyperGraph> graph) {
    graph->deleteFalseEdges();
    return {std::move(graph), std::make_unique<BackTranslator>()};
}
} // namespace golem