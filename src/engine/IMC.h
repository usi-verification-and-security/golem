/*
 * Copyright (c) 2022, Konstantin Britikov <britikovki@gmail.com>
 * Copyright (c) 2023-2025, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef GOLEM_IMC_H
#define GOLEM_IMC_H

#include "Options.h"
#include "TransitionSystem.h"
#include "TransitionSystemEngine.h"

#include "osmt_solver.h"

namespace golem {
class IMC : public TransitionSystemEngine {
    Logic & logic;
    // Options const & options;
    int verbosity = 0;

public:
    IMC(Logic & logic, Options const & options) : logic(logic) {
        verbosity = std::stoi(options.getOrDefault(Options::VERBOSE, "0"));
        computeWitness = options.getOrDefault(Options::COMPUTE_WITNESS, "") == "true";
    }

    using TransitionSystemEngine::solve;

private:
    TransitionSystemVerificationResult solve(TransitionSystem const & system) override;

    TransitionSystemVerificationResult finiteRun(TransitionSystem const & ts, unsigned k);

    PTRef computeFinalInductiveInvariant(PTRef inductiveInvariant, unsigned k, TransitionSystem const & ts);

    bool implies(PTRef antecedent, PTRef consequent) const;
};
} // namespace golem

#endif // GOLEM_IMC_H
