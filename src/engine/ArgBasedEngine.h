/*
 * Copyright (c) 2024, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef GOLEM_ARGBASEDENGINE_H
#define GOLEM_ARGBASEDENGINE_H

#include "Engine.h"

#include "Witnesses.h"
#include "graph/ChcGraph.h"

#include "osmt_terms.h"

class ARGBasedEngine : public Engine {
    Options const & options;

public:
    ARGBasedEngine(Logic &, Options const & options) : options(options) {}

    VerificationResult solve(ChcDirectedHyperGraph const & graph) override;
};

#endif // GOLEM_ARGBASEDENGINE_H
