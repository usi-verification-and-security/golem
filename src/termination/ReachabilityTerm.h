/*
 * Copyright (c) 2025, Konstantin Britikov <konstantin.britikov@usi.ch>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef REACHABILITYTERM_H
#define REACHABILITYTERM_H

#include "osmt_terms.h"

#include "Options.h"
#include "graph/ChcGraphBuilder.h"

namespace golem::termination {

class ReachabilityTerm {
public:
    explicit ReachabilityTerm(Options const & options) : options(options) {}

    enum struct Answer { NO, UNKNOWN, ERROR };

    Answer nontermination(ChcDirectedHyperGraph const & system);

private:
    Options const & options;
};
} // namespace golem::termination

#endif //REACHABILITYTERM_H
