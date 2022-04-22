//
// Created by Martin Blicha on 17.07.20.
//

#ifndef OPENSMT_ENGINE_H
#define OPENSMT_ENGINE_H

#include "Witnesses.h"
#include "ChcGraph.h"
#include "Options.h"

#include "osmt_solver.h"
#include "osmt_terms.h"

#include <memory>

class Engine {
public:
    virtual GraphVerificationResult solve(ChcDirectedHyperGraph &) {
        throw std::logic_error("Not implemented yet!");
    }

    virtual GraphVerificationResult solve(ChcDirectedGraph const &) {
        throw std::logic_error("Not implemented yet!");
    }

    virtual ~Engine() = default;
};

#endif //OPENSMT_ENGINE_H
