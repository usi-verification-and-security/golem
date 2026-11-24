/*
 * Copyright (c) 2025, Konstantin Britikov <konstantin.britikov@usi.ch>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef REACHABILITYNONTERM_H
#define REACHABILITYNONTERM_H

#include "osmt_terms.h"

#include "Options.h"
#include "QuantifierElimination.h"
#include "TransitionSystem.h"

#include <map>
#include <set>

namespace golem::termination {

class ReachabilityNonterm {
public:
    explicit ReachabilityNonterm(Options const & givenOptions) : options(givenOptions) {
        options.addOption(options.COMPUTE_WITNESS, "true");
        qeOptions = parseQEOptions(options);
        sinkPostDepth = std::stoul(options.getOrDefault(Options::NONTERM_SINK_POST_DEPTH, "0"));
    }

    enum struct Answer { YES, NO, UNKNOWN, ERROR };

    Answer run(TransitionSystem const & ts);

private:
    bool DETERMINISTIC_TRANSITION;
    std::vector<PTRef> vars;
    Options options;
    // Configuration of the QE computing the states that may avoid termination (see generateWellfoundedDisjuncts).
    // With compute_overapproximation == false (the default) the precise QE is used.
    QEOptions qeOptions;
    // Number of forward-image steps of the proven terminating states added to the sink states (see forwardCone).
    // 0 (the default) adds only the proven terminating states themselves.
    uint sinkPostDepth = 0;
    PTRef covered;
    // Pool of well-founded candidates, shared between recursive analyzeTS invocations
    vec<PTRef> strictCandidates;
    // Verdict of every checked candidate (is it satisfiable and well-founded). Well-foundedness does not depend on
    // the analyzed state-space, so the cache is shared between recursive analyzeTS invocations as well.
    std::map<PTRef, bool> checkedCandidates;

    static QEOptions parseQEOptions(Options const & options);

    void synthesizeInvariant(PTRef inv, PTRef transition, ArithLogic & logic);

    std::tuple<Answer, PTRef> analyzeTS(PTRef init, PTRef transition, PTRef sink, ArithLogic & logic);

    std::tuple<PTRef, PTRef> blockDeterministicPrefix(PTRef init, PTRef transition, PTRef sink, PTRef trace, uint num,
                                                      ArithLogic & logic);

    bool generateWellfoundedDisjuncts(PTRef inv, PTRef transition, PTRef sink, PTRef trace, uint num, ArithLogic & logic);

    std::tuple<Answer, PTRef> checkTermination(PTRef init, PTRef transition, PTRef & sink, ArithLogic & logic, PTRef inv,
                                               uint originalSize);

    bool coverState(PTRef state, PTRef inv, PTRef terminating, PTRef transition, ArithLogic & logic);

    PTRef forwardCone(PTRef reached, PTRef transition, PTRef sink, ArithLogic & logic);

    void extractWellFoundedCandidates(PTRef itp, PTRef sink, ArithLogic & logic, const std::vector<PTRef> & vars);
};
} // namespace golem::termination

#endif // REACHABILITYNONTERM_H