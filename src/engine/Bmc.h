/*
 * Copyright (c) 2020-2022, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef GOLEM_BMC_H
#define GOLEM_BMC_H

#include "Engine.h"
#include "TransitionSystem.h"

class BMC : public Engine {
    Logic & logic;
//    Options const & options;
public:

    BMC(Logic& logic, Options const &) : logic(logic) {}

    virtual GraphVerificationResult solve(ChcDirectedHyperGraph & graph) override {
        if (graph.isNormalGraph()) {
            auto normalGraph = graph.toNormalGraph();
            return solve(*normalGraph);
        }
        return GraphVerificationResult(VerificationResult::UNKNOWN);
    }

    GraphVerificationResult solve(ChcDirectedGraph const & system);

private:
    GraphVerificationResult solveTransitionSystem(TransitionSystem & system);
};


#endif //GOLEM_BMC_H
