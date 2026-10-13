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

#include <map>
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
    // Pool of well-founded candidates, shared between recursive analyzeTS invocations
    vec<PTRef> strictCandidates;
    // Verdict of every checked candidate (is it satisfiable and well-founded). Well-foundedness does not depend on
    // the analyzed state-space, so the cache is shared between recursive analyzeTS invocations as well.
    std::map<PTRef, bool> checkedCandidates;

    void synthesizeInvariant(PTRef inv, PTRef transition, ArithLogic & logic);

    std::tuple<Answer, PTRef> analyzeTS(PTRef init, PTRef transition, PTRef sink, ArithLogic & logic);

    std::tuple<PTRef, PTRef> blockDeterministicPrefix(PTRef init, PTRef transition, PTRef sink, PTRef trace, uint num,
                                                      ArithLogic & logic);

    bool generateWellfoundedDisjuncts(PTRef inv, PTRef transition, PTRef sink, PTRef trace, uint num, ArithLogic & logic);

    std::tuple<Answer, PTRef> checkTermination(PTRef init, PTRef transition, PTRef & sink, ArithLogic & logic, PTRef inv);

    void extractWellFoundedCandidates(PTRef itp, PTRef sink, ArithLogic & logic, const std::vector<PTRef> & vars);
};
} // namespace golem::termination

#endif // REACHABILITYNONTERM_H