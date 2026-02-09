/*
 * Copyright (c) 2023-2025, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */
#ifndef GOLEM_SINGLELOOPTRANSFORMATION_H
#define GOLEM_SINGLELOOPTRANSFORMATION_H

#include "CommonUtils.h"
#include "TransitionSystem.h"
#include "Witnesses.h"
#include "graph/ChcGraph.h"

namespace golem {
/**
 * This class implements a transformation from a general linear CHC system to a transition system (defined by initial
 * states, transition relation and bad states).
 *
 * We rely on subprocedure to contract a set of vertices into a single vertex.
 * We contract all vertices except the entry and exit vertices.
 * The final transition system is obtained by disjoining all facts (outgoing edges from entry) into initial states
 * and disjoining all queries (edges incoming to exit) into bad states.
 *
 * Backtranslating witness from transition system is currently based on the following reasoning:
 * To backtranslate proof, we have to identify which disjunct of the transition relation was used to make each step
 * in the error trace of the transition system. From that we can deduce which edge needs to be taken
 * (and with what values) in the CHC graph.
 *
 * For the model, we compute restriction of the TS invariant to each location by substituting appropriate constant
 * values for location variables. This may still leave some undesired variables in the invariant. We currently do our
 * best to eliminate these variables by simplifying the formula. We rely on quantifier elimination as the last resort.
 */
class SingleLoopTransformation {
public:
    class WitnessBackTranslator {
        ChcDirectedGraph originalGraph;
        ChcDirectedGraph contractedGraph;
        ContractionData contractionData;

    public:
        WitnessBackTranslator(ChcDirectedGraph originalGraph, ChcDirectedGraph contractedGraph,
                              ContractionData contractionData)
            : originalGraph(std::move(originalGraph)),
              contractedGraph(std::move(contractedGraph)),
              contractionData(std::move(contractionData)) {}

        VerificationResult translate(TransitionSystemVerificationResult result);

    private:
        template<typename T> using ErrorOr = std::variant<NoWitness, T>;

        ErrorOr<InvalidityWitness> translateErrorPath(std::size_t unrolling);

        ErrorOr<ValidityWitness> translateInvariant(PTRef inductiveInvariant);

        std::unordered_set<PTRef, PTRefHash> getVarsForVertex(SymRef vertex) const;
    };

    using TransformationResult = std::pair<std::unique_ptr<TransitionSystem>, std::unique_ptr<WitnessBackTranslator>>;

    TransformationResult transform(ChcDirectedGraph const & graph) const;
};
} // namespace golem

#endif // GOLEM_SINGLELOOPTRANSFORMATION_H
