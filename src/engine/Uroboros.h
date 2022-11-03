//
// Created by Konstantin Britikov on 03.11.22.
//

#ifndef GOLEM_UROBOROS_H
#define GOLEM_UROBOROS_H

#include "Engine.h"
#include "TransitionSystem.h"

class Uroboros : public Engine {
    Logic & logic;
//    Options const & options;
    int verbosity = 0;
public:

    Uroboros(Logic & logic, Options const & options) : logic(logic) {
        if (options.hasOption(Options::VERBOSE)) {
            verbosity = std::stoi(options.getOption(Options::VERBOSE));
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
    PTRef lastIterationInterpolant(MainSolver & solver);
    sstat checkItp(PTRef & itp, PTRef & itpsOld, Logic & logic);
};


#endif //GOLEM_UROBOROS_H