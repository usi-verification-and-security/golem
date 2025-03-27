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

namespace {

struct SlightlyBetterNodeEliminatorPredicate {
    bool operator()(SymRef, AdjacencyListsGraphRepresentation const &, ChcDirectedHyperGraph const & graph) const;
};

bool SlightlyBetterNodeEliminatorPredicate::operator()(
    SymRef vertex,
    AdjacencyListsGraphRepresentation const & ar,
    ChcDirectedHyperGraph const & graph) const {
    if (not isNonLoopNode(vertex, ar, graph)) { return false; }
    // Here we do not consider hyperedges anymore
    if (hasHyperEdge(vertex, ar, graph)) { return false; }
    // We extend the definition of a simple node such that |incoming| x |outgoing| <= |incoming| + |outgoing|
    bool isSimple = [&]() {
        auto outgoingSize = ar.getOutgoingEdgesFor(vertex).size();
        auto incomingSize = ar.getIncomingEdgesFor(vertex).size();
        return incomingSize * outgoingSize <= incomingSize + outgoingSize;
    }();
    return isSimple;
}

/**
 * This node eliminator is designed to eliminate some nodes that SimpleNodeEliminator preserves.
 * Typical example is head of an outer loop; in graph terminology, node s1 which has one incoming, one outgoing edge,
 * and then for some s2 there are edges s1 -> s2, s2 -> s2, s2 -> s1.
 *
 * For simplicity, we no longer consider hyperedges in this eliminator.
 */
class SlightlyBetterNodeEliminator : public NodeEliminator {
public:
    SlightlyBetterNodeEliminator() : NodeEliminator(SlightlyBetterNodeEliminatorPredicate{}) {}
};
} // namespace

TransformationPipeline towardsTransitionSystems() {
    TransformationPipeline::pipeline_t stages;
    stages.push_back(std::make_unique<SlightlyBetterNodeEliminator>());
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
    stages.push_back(std::make_unique<FalseClauseRemoval>());
    stages.push_back(std::make_unique<RemoveUnreachableNodes>());
    stages.push_back(std::make_unique<MultiEdgeMerger>());
    stages.push_back(std::make_unique<TrivialEdgePruner>());
    return TransformationPipeline(std::move(stages));
}
} // namespace Transformations