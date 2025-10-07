/*
 * Copyright (c) 2025, Konstantin Britikov <konstantin.britikov@usi.ch>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef REACHABILITYTERM_H
#define REACHABILITYTERM_H

#include "Options.h"
#include "TransitionSystem.h"

namespace golem::termination {

class ReachabilityTerm {
public:
    explicit ReachabilityTerm(Options const & options) : options(options) {}

    enum struct Answer { YES, UNKNOWN, ERROR };

    Answer termination(TransitionSystem const & graph);

private:
    Options const & options;
};
} // namespace golem::termination

#endif // REACHABILITYTERM_H
