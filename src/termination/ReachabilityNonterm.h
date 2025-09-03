/*
 * Copyright (c) 2025, Konstantin Britikov <konstantin.britikov@usi.ch>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef REACHABILITYNONTERM_H
#define REACHABILITYNONTERM_H

#include "osmt_terms.h"

#include "Options.h"
#include "graph/ChcGraphBuilder.h"
#include "utils/SmtSolver.h"

namespace golem::termination {

class ReachabilityNonterm {
public:
    explicit ReachabilityNonterm(Options const & options) : options(options) {}

    enum struct Answer { YES, NO, UNKNOWN, ERROR };

    Answer nontermination(ChcDirectedGraph const & graph);

private:
    Options const & options;
    PTRef eliminateVars(PTRef fla, const vec<PTRef> & vars, Model & model, bool useQE, Logic logic);
};
} // namespace golem::termination

#endif //REACHABILITYNONTERM_H
