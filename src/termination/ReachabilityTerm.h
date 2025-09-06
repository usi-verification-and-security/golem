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
#include "utils/SmtSolver.h"

namespace golem::termination {

class ReachabilityTerm {
public:
    explicit ReachabilityTerm(Options const & options) : options(options) {}

    enum struct Answer { YES, NO, UNKNOWN, ERROR };

    Answer nontermination(ChcDirectedHyperGraph const & system);

private:
    Options const & options;
    PTRef eliminateVars(PTRef fla, const vec<PTRef> & vars, Model & model, bool useQE, Logic logic);
};
} // namespace golem::termination

#endif //REACHABILITYTERM_H
