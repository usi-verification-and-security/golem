/*
 * Copyright (c) 2022, Konstantin Britikov <britikovki@gmail.com>
 * Copyright (c) 2023, Martin Blicha <martin.blicha@gmail.com>
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
        unsigned depth;
        PTRef interpolant;
    };

    IMC(Logic & logic, Options const & options) : logic(logic) {
        if (options.hasOption(Options::VERBOSE)) {
            verbosity = std::stoi(options.getOption(Options::VERBOSE));
        }
    }

    virtual VerificationResult solve(ChcDirectedHyperGraph const & graph) override {
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

    InterpolantResult finiteRun(TransitionSystem const & ts, unsigned k);

    PTRef computeFinalInductiveInvariant(PTRef inductiveInvariant, unsigned k, TransitionSystem const & ts);

    PTRef lastIterationInterpolant(MainSolver & solver, ipartitions_t const & mask);
    sstat checkItp(PTRef itp, PTRef itpsOld);
};

#endif //GOLEM_IMC_H
