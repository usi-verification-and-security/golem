/*
 * Copyright (c) 2021-2022, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef GOLEM_TPA_H
#define GOLEM_TPA_H

#include "Options.h"
#include "TransitionSystemEngine.h"

#include "engine/TPABase.hh"

namespace golem {

enum class TPACore { BASIC, SPLIT };

class TPAEngine : public TransitionSystemEngine {
    Logic & logic;
    Options options;
    TPACore coreAlgorithm;
    friend class TransitionSystemNetworkManager;

public:
    TPAEngine(Logic & logic, Options options, TPACore core)
        : logic(logic), options(std::move(options)), coreAlgorithm(core) {
        computeWitness = this->options.getOrDefault(Options::COMPUTE_WITNESS, "") == "true";
    }

    using TransitionSystemEngine::solve;
    VerificationResult solve(ChcDirectedGraph const & graph) override;

    static const std::string TPA;
    static const std::string SPLIT_TPA;

    [[nodiscard]] bool shouldComputeWitness() const { return computeWitness; }

private:
    std::unique_ptr<TPABase> mkSolver();

    VerificationResult solveTransitionSystemGraph(ChcDirectedGraph const & graph);

    ValidityWitness computeValidityWitness(ChcDirectedGraph const & graph, TransitionSystem const & ts,
                                           PTRef inductiveInvariant) const;

    InvalidityWitness computeInvalidityWitness(ChcDirectedGraph const & graph, unsigned steps) const;
};

} // namespace golem

#endif // GOLEM_TPA_H
