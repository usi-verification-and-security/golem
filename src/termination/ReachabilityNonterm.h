/*
 * Copyright (c) 2025, Konstantin Britikov <konstantin.britikov@usi.ch>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef REACHABILITYNONTERM_H
#define REACHABILITYNONTERM_H

#include "osmt_terms.h"

#include "Options.h"
#include "TransitionSystem.h"

namespace golem::termination {
    class ReachabilityNonterm {
    public:
        explicit ReachabilityNonterm(Options const & options) : options(options) {}

        enum struct Answer { YES, NO, UNKNOWN, ERROR };

        Answer run(TransitionSystem const & ts);

    private:
        Options const & options;

        void houdiniCheck(PTRef invCandidates, PTRef transition, Logic & logic, const std::vector<PTRef> & vars);

        vec<PTRef> leftInvariants;
        vec<PTRef> rightInvariants;

    };
} // namespace golem::termination

#endif // REACHABILITYNONTERM_H