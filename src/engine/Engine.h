//
// Created by Martin Blicha on 17.07.20.
//

#ifndef OPENSMT_ENGINE_H
#define OPENSMT_ENGINE_H

#include "Witnesses.h"
#include "Options.h"
#include "graph/ChcGraph.h"

#include "osmt_solver.h"
#include "osmt_terms.h"

#include <memory>

class Engine {
public:
    virtual VerificationResult solve(ChcDirectedHyperGraph &) {
        return VerificationResult(VerificationAnswer::UNKNOWN);
    }

    virtual ~Engine() = default;
};

#endif //OPENSMT_ENGINE_H
