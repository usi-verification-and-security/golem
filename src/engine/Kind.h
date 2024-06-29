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
        verbosity = std::stoi(options.getOrDefault(Options::VERBOSE, "0"));
        computeWitness = options.getOrDefault(Options::COMPUTE_WITNESS, "") == "true";
    }

    virtual VerificationResult solve(ChcDirectedHyperGraph const & graph) override;

    VerificationResult solve(ChcDirectedGraph const & graph);

private:
    VerificationResult solveTransitionSystem(ChcDirectedGraph const & graph);
    TransitionSystemVerificationResult solveTransitionSystemInternal(TransitionSystem const & system);

    PTRef invariantFromForwardInduction(TransitionSystem const & transitionSystem, unsigned long k) const;
    PTRef invariantFromBackwardInduction(TransitionSystem const & transitionSystem, unsigned long k) const;

};


#endif //GOLEM_KIND_H
