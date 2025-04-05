/*
 * Copyright (c) 2020-2025, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "ChcGraphBuilder.h"

namespace golem {
std::unique_ptr<ChcDirectedHyperGraph> ChcGraphBuilder::buildGraph(NormalizedChcSystem const & system) {
    std::vector<DirectedHyperEdge> edges;
    ChcSystem const & chcSystem = *system.normalizedSystem;
    // Special case to cover initial clauses, we are adding artificial "TRUE" starting predicate
    SymRef init = logic.getSym_true();
    for (auto const & clause : chcSystem.getClauses()) {
        auto const& head = clause.head;
        auto const& body = clause.body;
        auto headSymbol = logic.getSymRef(head.predicate.predicate);

        std::vector<SymRef> from;
        for (auto const& bodyPredicate : body.uninterpretedPart) {
            from.push_back(logic.getSymRef(bodyPredicate.predicate));
        }
        if (from.empty()) {
            from.push_back(init);
        }
        edges.push_back(DirectedHyperEdge{.from = std::move(from), .to = headSymbol, .fla = body.interpretedPart, .id = {0}});
    }
    return std::make_unique<ChcDirectedHyperGraph>(std::move(edges), system.canonicalPredicateRepresentation, logic);
}
} // namespace golem