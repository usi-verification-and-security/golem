/*
 * Copyright (c) 2022, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef GOLEM_KIND_H
#define GOLEM_KIND_H



#include "TransitionSystemEngine.h"
#include "TransitionSystem.h"

class Kind : public TransitionSystemEngine {
    Logic & logic;
//    Options const & options;
    int verbosity {0};
public:

    Kind(Logic & logic, Options const & options) : logic(logic) {
        verbosity = std::stoi(options.getOrDefault(Options::VERBOSE, "0"));
        computeWitness = options.getOrDefault(Options::COMPUTE_WITNESS, "") == "true";
    }


    VerificationResult solve(ChcDirectedGraph const & graph) override;

private:
    VerificationResult solveTransitionSystem(ChcDirectedGraph const & graph);
    TransitionSystemVerificationResult solveTransitionSystemInternal(TransitionSystem const & system);

    PTRef invariantFromForwardInduction(TransitionSystem const & transitionSystem, unsigned long k) const;
    PTRef invariantFromBackwardInduction(TransitionSystem const & transitionSystem, unsigned long k) const;

};


#endif //GOLEM_KIND_H
