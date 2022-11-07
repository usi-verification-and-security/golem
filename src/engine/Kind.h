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
    int verbosity {0};
    bool computeWitness {false};
public:

    Kind(Logic & logic, Options const & options) : logic(logic) {
        if (options.hasOption(Options::VERBOSE)) {
            verbosity = std::stoi(options.getOption(Options::VERBOSE));
        }
        if (options.hasOption(Options::COMPUTE_WITNESS)) {
            computeWitness = options.getOption(Options::COMPUTE_WITNESS) == "true";
        }
    }

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

    ValidityWitness witnessFromForwardInduction(ChcDirectedGraph const & graph,
                                                TransitionSystem const & transitionSystem, unsigned long k) const;

    ValidityWitness witnessFromBackwardInduction(ChcDirectedGraph const & graph,
                                                 TransitionSystem const & transitionSystem, unsigned long k) const;
};


#endif //GOLEM_KIND_H
