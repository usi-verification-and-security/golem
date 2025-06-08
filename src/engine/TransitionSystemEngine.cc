/*
* Copyright (c) 2025, Martin Blicha <martin.blicha@gmail.com>
*
* SPDX-License-Identifier: MIT
*/

#include "TransitionSystemEngine.h"

#include "Common.h"
#include "TransformationUtils.h"
#include "TransitionSystem.h"
#include "transformers/BasicTransformationPipelines.h"
#include "transformers/SingleLoopTransformation.h"

namespace golem {
VerificationResult TransitionSystemEngine::solve(ChcDirectedHyperGraph const & graph) {
    auto pipeline = Transformations::towardsTransitionSystems();
    auto transformationResult = pipeline.transform(std::make_unique<ChcDirectedHyperGraph>(graph));
    auto transformedGraph = std::move(transformationResult.first);
    auto translator = std::move(transformationResult.second);
    if (transformedGraph->isNormalGraph()) {
        auto normalGraph = transformedGraph->toNormalGraph();
        auto res = solve(*normalGraph);
        return computeWitness ? translator->translate(std::move(res)) : std::move(res);
    }
    return VerificationResult(VerificationAnswer::UNKNOWN);
}

VerificationResult TransitionSystemEngine::solve(ChcDirectedGraph const & graph) {
    if (isTrivial(graph)) {
        return solveTrivial(graph);
    }
    if (isTransitionSystem(graph)) {
        auto ts = toTransitionSystem(graph);
        ts = dealWithAuxiliaryVariables(std::move(ts));
        auto res = solve(*ts);
        return computeWitness ? translateTransitionSystemResult(res, graph, *ts) : VerificationResult(res.answer);
    }
    SingleLoopTransformation transformation;
    auto[ts, backtranslator] = transformation.transform(graph);
    assert(ts);
    auto res = solve(*ts);
    return computeWitness ? backtranslator->translate(res) : VerificationResult(res.answer);
}

TransitionSystemVerificationResult TransitionSystemEngine::solve(TransitionSystem const &) {
    return {VerificationAnswer::UNKNOWN, {0u}};
}

std::unique_ptr<TransitionSystem> TransitionSystemEngine::dealWithAuxiliaryVariables(std::unique_ptr<TransitionSystem> ts) {
    return ensureNoAuxiliaryVariablesInInitAndQuery(std::move(ts));
}

} // namespace golem

