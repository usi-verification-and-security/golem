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
    explicit ReachabilityNonterm(Options const & givenOptions) : options(givenOptions) {
        options.addOption(options.COMPUTE_WITNESS, "true");
    }

    enum struct Answer { YES, NO, UNKNOWN, ERROR };

    Answer run(TransitionSystem const & ts);

private:
    bool DETERMINISTIC_TRANSITION;
    std::vector<PTRef> vars;
    Options options;
    PTRef covered;

    std::tuple<Answer, PTRef> analyzeTS(PTRef init, PTRef transition, PTRef sink, ArithLogic & logic);

    std::tuple<PTRef, PTRef> blockDeterministicPrefix(PTRef init, PTRef transition, PTRef sink, PTRef trace, uint num,
                                                      ArithLogic & logic);

    std::tuple<Answer, PTRef> tryTransitionInvariant(PTRef transition, PTRef sink, PTRef trace, uint num,
                                                     ArithLogic & logic, vec<PTRef> & strictCandidates);

    std::tuple<Answer, PTRef> refineTransitionInvariant(PTRef init, PTRef transition, PTRef originalTransition,
                                                        PTRef & sink, ArithLogic & logic, vec<PTRef> & strictCandidates);
};
} // namespace golem::termination

#endif // REACHABILITYNONTERM_H