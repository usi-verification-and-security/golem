/*
 * Copyright (c) 2025, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef GOLEM_SYMBOLICEXECUTION_H
#define GOLEM_SYMBOLICEXECUTION_H

#include "Engine.h"
#include "Options.h"

namespace golem {
class SymbolicExecution : public Engine {
    Options const & options;

public:
    SymbolicExecution(Logic &, Options const & options) : options(options) {}

    VerificationResult solve(ChcDirectedHyperGraph const & graph) override;
};
} // namespace golem


#endif // GOLEM_SYMBOLICEXECUTION_H
