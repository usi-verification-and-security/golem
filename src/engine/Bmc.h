//
// Created by Martin Blicha on 17.07.20.
//

#ifndef OPENSMT_BMC_H
#define OPENSMT_BMC_H

#include "Engine.h"

#include "TransitionSystem.h"

class BMC : public Engine {
    Logic & logic;
//    Options const & options;
public:

    BMC(Logic& logic, Options const &) : logic(logic) {}

    virtual GraphVerificationResult
    solve(ChcDirectedHyperGraph & graph) override {
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


#endif //OPENSMT_BMC_H
