/*
 * Copyright (c) 2024, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "Engine.h"

#ifndef DAR_H
#define DAR_H

class DAR : public Engine {
    Logic & logic;
    bool computeWitness = false;

public:
    DAR(Logic & logic, Options const & options) : logic(logic) {
        computeWitness = options.getOrDefault(Options::COMPUTE_WITNESS, "") == "true";
    }

    VerificationResult solve(ChcDirectedHyperGraph const & graph) override {
        if (graph.isNormalGraph()) {
            auto normalGraph = graph.toNormalGraph();
            return solve(*normalGraph);
        }
        return VerificationResult(VerificationAnswer::UNKNOWN);
    }

    VerificationResult solve(ChcDirectedGraph const & graph);

private:
    VerificationResult solveTransitionSystem(ChcDirectedGraph const & graph);
    TransitionSystemVerificationResult solveTransitionSystemInternal(TransitionSystem const & system);
};

#endif // DAR_H