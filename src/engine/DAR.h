/*
 * Copyright (c) 2024-2025, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef DAR_H
#define DAR_H

#include "Options.h"
#include "TransitionSystemEngine.h"

namespace golem {
class DAR : public TransitionSystemEngine {
    Logic & logic;

public:
    DAR(Logic & logic, Options const & options) : logic(logic) {
        computeWitness = options.getOrDefault(Options::COMPUTE_WITNESS, "") == "true";
    }

private:
    TransitionSystemVerificationResult solve(TransitionSystem const & system) override;
};
} // namespace golem

#endif // DAR_H