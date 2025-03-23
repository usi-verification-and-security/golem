/*
 * Copyright (c) 2022-2025, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "BasicTransformationPipelines.h"

#include "ConstraintSimplifier.h"
#include "EdgeInliner.h"
#include "FalseClauseRemoval.h"
#include "MultiEdgeMerger.h"
#include "NodeEliminator.h"
#include "RemoveUnreachableNodes.h"
#include "SimpleChainSummarizer.h"
#include "TrivialEdgePruner.h"

namespace Transformations {
TransformationPipeline towardsTransitionSystems() {
    TransformationPipeline::pipeline_t stages;
    stages.push_back(std::make_unique<MultiEdgeMerger>());
    stages.push_back(std::make_unique<NonLoopEliminator>());
    stages.push_back(std::make_unique<FalseClauseRemoval>());
    stages.push_back(std::make_unique<RemoveUnreachableNodes>());
    stages.push_back(std::make_unique<MultiEdgeMerger>());
    stages.push_back(std::make_unique<TrivialEdgePruner>());
    TransformationPipeline pipeline(std::move(stages));
    return pipeline;
}

TransformationPipeline defaultTransformationPipeline() {
    TransformationPipeline::pipeline_t stages;
    stages.push_back(std::make_unique<ConstraintSimplifier>());
    stages.push_back(std::make_unique<SimpleChainSummarizer>());
    stages.push_back(std::make_unique<RemoveUnreachableNodes>());
    stages.push_back(std::make_unique<SimpleNodeEliminator>());
    stages.push_back(std::make_unique<EdgeInliner>());
    stages.push_back(std::make_unique<FalseClauseRemoval>());
    stages.push_back(std::make_unique<RemoveUnreachableNodes>());
    stages.push_back(std::make_unique<MultiEdgeMerger>());
    stages.push_back(std::make_unique<SimpleChainSummarizer>());
    stages.push_back(std::make_unique<RemoveUnreachableNodes>());
    stages.push_back(std::make_unique<SimpleNodeEliminator>());
    stages.push_back(std::make_unique<MultiEdgeMerger>());
    return TransformationPipeline(std::move(stages));
}
} // namespace Transformations