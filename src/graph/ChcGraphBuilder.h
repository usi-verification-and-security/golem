/*
 * Copyright (c) 2020-2025, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef GOLEM_CHCGRAPHBUILDER_H
#define GOLEM_CHCGRAPHBUILDER_H

#include "ChcGraph.h"
#include "Normalizer.h"

namespace golem {
class ChcGraphBuilder {
    Logic & logic;
public:
    explicit ChcGraphBuilder(Logic & logic) : logic(logic) {}

    std::unique_ptr<ChcDirectedHyperGraph> buildGraph(NormalizedChcSystem const & system);
};
}// namespace golem


#endif //GOLEM_CHCGRAPHBUILDER_H
