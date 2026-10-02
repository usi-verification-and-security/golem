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

#include <set>

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
    // Well-founded disjuncts of the transition invariant candidate, shared across all (recursive) analyzeTS invocations
    vec<PTRef> strictCandidates;
    // Number of candidate generations that extended strictCandidates since the last shrinking
    uint strictCandidatesUpdates = 0;

    std::tuple<Answer, PTRef> analyzeTS(PTRef init, PTRef transition, PTRef sink, ArithLogic & logic);

    std::tuple<PTRef, PTRef> blockDeterministicPrefix(PTRef init, PTRef transition, PTRef sink, PTRef trace, uint num,
                                                      ArithLogic & logic);

    bool generateWellfoundedDisjuncts(PTRef transition, PTRef sink, PTRef trace, uint num, ArithLogic & logic,
                                      std::set<PTRef> & checkedCandidates);

    void shrinkStrictCandidates(PTRef transition, ArithLogic & logic);

    std::tuple<Answer, PTRef> checkTermination(PTRef init, PTRef transition, PTRef & sink, ArithLogic & logic);
};
} // namespace golem::termination

#endif // REACHABILITYNONTERM_H