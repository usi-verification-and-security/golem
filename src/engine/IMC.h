/*
 * Copyright (c) 2022, Konstantin Britikov <britikovki@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef GOLEM_IMC_H
#define GOLEM_IMC_H

#include "Engine.h"
#include "TransitionSystem.h"

class IMC : public Engine {
    Logic & logic;
//    Options const & options;
    int verbosity = 0;
public:
    struct InterpolantResult{
        lbool result;
        int depth;
        PTRef interpolant;
    };

    IMC(Logic & logic, Options const & options) : logic(logic) {
        if (options.hasOption(Options::VERBOSE)) {
            verbosity = std::stoi(options.getOption(Options::VERBOSE));
        }
    }

    virtual VerificationResult solve(ChcDirectedHyperGraph & graph) override {
        if (graph.isNormalGraph()) {
            auto normalGraph = graph.toNormalGraph();
            return solve(*normalGraph);
        }
        return VerificationResult(VerificationAnswer::UNKNOWN);
    }

    VerificationResult solve(ChcDirectedGraph const & system);

private:
    InterpolantResult finiteRun(PTRef init, PTRef transition, PTRef query, int k);
    VerificationResult solveTransitionSystem(TransitionSystem const & system, ChcDirectedGraph const & graph);
    PTRef lastIterationInterpolant(MainSolver& solver, ipartitions_t mask);
    sstat checkItp(PTRef itp, PTRef itpsOld);
};

#endif //GOLEM_IMC_H
