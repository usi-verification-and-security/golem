/*
* Copyright (c) 2023-2024, Stepan Henrych <stepan.henrych@gmail.com>
*
* SPDX-License-Identifier: MIT
*/

#ifndef GOLEM_PDKIND_H
#define GOLEM_PDKIND_H

#include "Engine.h"
#include "TransitionSystem.h"


/**
 * Uses PDKind algorithm [1] to solve a transition system.
 *
 * [1] https://ieeexplore.ieee.org/document/7886665
 */
class PDKind : public Engine {
        Logic & logic;
        bool computeWitness {false};
    public:

        PDKind (Logic & logic, Options const & options) : logic(logic) {
            if (options.hasOption(Options::COMPUTE_WITNESS)) {
                computeWitness = options.getOption(Options::COMPUTE_WITNESS) == "true";
            }
        }

        VerificationResult solve(ChcDirectedHyperGraph const & graph) override;

        VerificationResult solve(ChcDirectedGraph const & system);

    private:
        [[nodiscard]] TransitionSystemVerificationResult solveTransitionSystem(TransitionSystem const & system) const;
};

#endif // GOLEM_PDKIND_H