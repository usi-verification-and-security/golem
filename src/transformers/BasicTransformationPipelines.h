/*
 * Copyright (c) 2022-2025, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef GOLEM_BASICTRANSFORMATIONPIPELINES_H
#define GOLEM_BASICTRANSFORMATIONPIPELINES_H

#include "TransformationPipeline.h"

namespace Transformations {

TransformationPipeline towardsTransitionSystems();

TransformationPipeline defaultTransformationPipeline();

inline TransformationPipeline TPAPreprocessing() {
    TransformationPipeline::pipeline_t stages;
    stages.push_back(std::make_unique<FalseClauseRemoval>());
    stages.push_back(std::make_unique<MultiEdgeMerger>());
    stages.push_back(std::make_unique<SimpleNodeEliminator>());
    stages.push_back(std::make_unique<MultiEdgeMerger>());
    stages.push_back(std::make_unique<TrivialEdgePruner>());
    TransformationPipeline pipeline(std::move(stages));
    return pipeline;
}

}

#endif //GOLEM_BASICTRANSFORMATIONPIPELINES_H
