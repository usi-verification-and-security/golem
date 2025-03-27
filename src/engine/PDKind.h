/*
* Copyright (c) 2023-2024, Stepan Henrych <stepan.henrych@gmail.com>
*
* SPDX-License-Identifier: MIT
*/

#ifndef GOLEM_PDKIND_H
#define GOLEM_PDKIND_H

#include "TransitionSystemEngine.h"
#include "TransitionSystem.h"


/**
 * Uses PDKind algorithm [1] to solve a transition system.
 *
 * [1] https://ieeexplore.ieee.org/document/7886665
 */
class PDKind : public TransitionSystemEngine {
        Logic & logic;
    public:
        PDKind (Logic & logic, Options const & options) : logic(logic) {
            if (options.hasOption(Options::COMPUTE_WITNESS)) {
                computeWitness = options.getOption(Options::COMPUTE_WITNESS) == "true";
            }
        }

    private:
        [[nodiscard]] TransitionSystemVerificationResult solve(TransitionSystem const & system) override;
};

#endif // GOLEM_PDKIND_H