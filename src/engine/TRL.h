/*
 * Copyright (c) 2025, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef GOLEM_TRL_H
#define GOLEM_TRL_H

#include "Options.h"
#include "TransitionSystemEngine.h"

namespace golem {

class TRL : public TransitionSystemEngine {
public:
    TRL(Logic & logic, Options const & options) : logic(logic) {
        if (options.hasOption(Options::COMPUTE_WITNESS)) {
            computeWitness = options.getOption(Options::COMPUTE_WITNESS) == "true";
        }
    }

private:
    [[nodiscard]] TransitionSystemVerificationResult solve(TransitionSystem const & system) override;

    Logic & logic;
};

} // namespace golem

#endif //GOLEM_TRL_H
