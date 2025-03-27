/*
 * Copyright (c) 2024, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef DAR_H
#define DAR_H

#include "TransitionSystemEngine.h"

class DAR : public TransitionSystemEngine {
    Logic & logic;

public:
    DAR(Logic & logic, Options const & options) : logic(logic) {
        computeWitness = options.getOrDefault(Options::COMPUTE_WITNESS, "") == "true";
    }

private:
    TransitionSystemVerificationResult solve(TransitionSystem const & system) override;
};

#endif // DAR_H