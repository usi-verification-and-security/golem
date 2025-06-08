/*
* Copyright (c) 2023-2024, Stepan Henrych <stepan.henrych@gmail.com>
* Copyright (c) 2025, Martin Blicha <martin.blicha@gmail.com>

*
* SPDX-License-Identifier: MIT
*/

#ifndef GOLEM_PDKIND_H
#define GOLEM_PDKIND_H

#include "Options.h"
#include "TransitionSystem.h"
#include "TransitionSystemEngine.h"

namespace golem {
/**
 * Uses PDKind algorithm [1] to solve a transition system.
 *
 * [1] https://ieeexplore.ieee.org/document/7886665
 */
class PDKind : public TransitionSystemEngine {
    Logic & logic;

public:
    PDKind(Logic & logic, Options const & options) : logic(logic) {
        if (options.hasOption(Options::COMPUTE_WITNESS)) {
            computeWitness = options.getOption(Options::COMPUTE_WITNESS) == "true";
        }
    }

private:
    [[nodiscard]] TransitionSystemVerificationResult solve(TransitionSystem const & system) override;
    std::unique_ptr<TransitionSystem> dealWithAuxiliaryVariables(std::unique_ptr<TransitionSystem>) override;
};
} // namespace golem

#endif // GOLEM_PDKIND_H