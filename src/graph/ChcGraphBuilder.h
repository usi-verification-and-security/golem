/*
 * Copyright (c) 2020-2022, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "ChcGraph.h"
#include "Normalizer.h"

#ifndef GOLEM_CHCGRAPHBUILDER_H
#define GOLEM_CHCGRAPHBUILDER_H


class ChcGraphBuilder {
    Logic & logic;
public:
    ChcGraphBuilder(Logic & logic) : logic(logic) {}

    std::unique_ptr<ChcDirectedHyperGraph> buildGraph(NormalizedChcSystem const & system);
};


#endif //GOLEM_CHCGRAPHBUILDER_H
