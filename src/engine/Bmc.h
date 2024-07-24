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
    // Options const & options;
    bool needsWitness = false;
    int verbosity = 0;
    bool forceTransitionSystem = true;

public:
    BMC(Logic & logic, Options const & options) : logic(logic) {
        needsWitness = options.getOrDefault(Options::COMPUTE_WITNESS, "") == "true";
        verbosity = std::stoi(options.getOrDefault(Options::VERBOSE, "0"));
        forceTransitionSystem = options.getOrDefault(Options::FORCE_TS, "") == "true";
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
    VerificationResult solveGeneralLinearSystem(ChcDirectedGraph const & graph);
};

#endif // GOLEM_BMC_H
