/*
* Copyright (c) 2020-2023, Martin Blicha <martin.blicha@gmail.com>
*
* SPDX-License-Identifier: MIT
*/

#ifndef OPENSMT_ENGINE_H
#define OPENSMT_ENGINE_H

#include "Witnesses.h"
#include "Options.h"
#include "graph/ChcGraph.h"

#include "osmt_terms.h"

#include <memory>

class Engine {
public:
    virtual VerificationResult solve(ChcDirectedHyperGraph const &) {
        return VerificationResult(VerificationAnswer::UNKNOWN);
    }

    virtual ~Engine() = default;
};

#endif //OPENSMT_ENGINE_H
