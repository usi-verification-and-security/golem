/*
 * Copyright (c) 2024, Konstantin Britikov <britikovki@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef GOLEM_NESTED_LOOP_TRANSFORMATION_H
#define GOLEM_NESTED_LOOP_TRANSFORMATION_H

#include "CommonUtils.h"
#include "TransitionSystem.h"
#include "Witnesses.h"
#include "graph/ChcGraph.h"

namespace golem {
/**
 * This class implements a transformation from a general linear CHC system to a linear CHC system without
 * nested loops.
 *
 * It works by iteratively identifying some innermost loop and contracting it into a single vertex.
 *
 * Witness backtranslation is a generalization of the same process for transformation into a single loop
 * (see SingleLoopTransformation).
 */
class NestedLoopTransformation {

public:
    class WitnessBackTranslator {
        ChcDirectedGraph const & initialGraph;
        ChcDirectedGraph const & graph;
        std::vector<ContractionData> loopContractionInfos;

    public:
        WitnessBackTranslator(ChcDirectedGraph const & initialGraph, ChcDirectedGraph const & graph,
                              std::vector<ContractionData> loops)
            : initialGraph(initialGraph), graph(graph), loopContractionInfos(std::move(loops)) {}

        VerificationResult translate(VerificationResult & result);

    private:
        template<typename T> using ErrorOr = std::variant<NoWitness, T>;

        ErrorOr<InvalidityWitness> translateErrorPath(InvalidityWitness);

        ErrorOr<ValidityWitness> translateInvariant(ValidityWitness);

        std::unordered_set<PTRef, PTRefHash> getVarsForVertex(ContractionData const &) const;
    };

    std::tuple<std::unique_ptr<ChcDirectedGraph>, std::unique_ptr<WitnessBackTranslator>>
    transform(ChcDirectedGraph const & graph);
};
} // namespace golem

#endif // GOLEM_NESTED_LOOP_TRANSFORMATION_H
