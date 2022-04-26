/*
 * Copyright (c) 2022, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "DeadClauseRemoval.h"

Transformer::TransformationResult DeadClauseRemoval::transform(std::unique_ptr<ChcDirectedHyperGraph> graph) {
    graph->deleteDeadEdges();
    return {std::move(graph), std::make_unique<BackTranslator>()};
}
