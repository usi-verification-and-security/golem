/*
* Copyright (c) 2020-2025, Martin Blicha <martin.blicha@gmail.com>
*
* SPDX-License-Identifier: MIT
*/

#ifndef GOLEM_ENGINE_H
#define GOLEM_ENGINE_H

#include "Options.h"
#include "Witnesses.h"
#include "graph/ChcGraph.h"


class Engine {
public:
    virtual VerificationResult solve(ChcDirectedHyperGraph const &) {
        return VerificationResult(VerificationAnswer::UNKNOWN);
    }

    virtual ~Engine() = default;
};

#endif //GOLEM_ENGINE_H
