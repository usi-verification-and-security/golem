/*
 * Copyright (c) 2023, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef GOLEM_SMTSOLVER_H
#define GOLEM_SMTSOLVER_H

#include "include/osmt_solver.h"

/**
 * Simple wrapper around OpenSMT's MainSolver and SMTConfig
 */
class SMTSolver {
    std::unique_ptr<MainSolver> solver;
    SMTConfig config;

public:
    enum class WitnessProduction { NONE, ONLY_MODEL, ONLY_INTERPOLANTS, MODEL_AND_INTERPOLANTS };

    // Default setup in OpenSMT is currently to produce models, but not interpolants
    explicit SMTSolver(Logic & logic, WitnessProduction setup = WitnessProduction::ONLY_MODEL);

    MainSolver & getCoreSolver() { return *solver; }

    SMTConfig & getConfig() { return config; }

    void resetSolver();
};

#endif // GOLEM_SMTSOLVER_H
