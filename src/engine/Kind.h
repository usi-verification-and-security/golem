/*
 * Copyright (c) 2022, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef GOLEM_KIND_H
#define GOLEM_KIND_H



#include "Engine.h"
#include "TransitionSystem.h"

class Kind : public Engine {
    Logic & logic;
//    Options const & options;
public:

    Kind(Logic& logic, Options const &) : logic(logic) {}

    virtual GraphVerificationResult solve(ChcDirectedHyperGraph & graph) override {
        if (graph.isNormalGraph()) {
            auto normalGraph = graph.toNormalGraph();
            return solve(*normalGraph);
        }
        return GraphVerificationResult(VerificationResult::UNKNOWN);
    }

    GraphVerificationResult solve(ChcDirectedGraph const & system);

private:
    GraphVerificationResult solveTransitionSystem(TransitionSystem const & system, ChcDirectedGraph const & graph);
};


#endif //GOLEM_KIND_H
