/*
 * Copyright (c) 2025, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef STEPCOUNTER_H
#define STEPCOUNTER_H

#include "Options.h"
#include "TransitionSystem.h"

namespace golem::vmt {

class StepCounter {
public:
    explicit StepCounter(Options const & options) : options(options) {}

    enum struct Answer { YES, UNKNOWN, ERROR };

    Answer checkLiveness(TransitionSystem const & ts);

private:
    Options const & options;
};
} // namespace golem::vmt

#endif //STEPCOUNTER_H
