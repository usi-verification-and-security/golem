/*
 * Copyright (c) 2020-2023, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "Bmc.h"

#include "Common.h"

#include "TermUtils.h"
#include "TransformationUtils.h"
#include "transformers/SingleLoopTransformation.h"
#include "utils/SmtSolver.h"

VerificationResult BMC::solve(ChcDirectedGraph const & graph) {
    if (isTrivial(graph)) {
        return solveTrivial(graph);
    }
    if (isTransitionSystem(graph)) {
        return solveTransitionSystem(graph);
    }

    SingleLoopTransformation transformation;
    auto[ts, backtranslator] = transformation.transform(graph);
    assert(ts);
    auto res = solveTransitionSystemInternal(*ts);
    return backtranslator->translate(res);
}

VerificationResult BMC::solveTransitionSystem(ChcDirectedGraph const & graph) {
    auto ts = toTransitionSystem(graph);
    auto res = solveTransitionSystemInternal(*ts);
    return translateTransitionSystemResult(res, graph, *ts);
}

TransitionSystemVerificationResult BMC::solveTransitionSystemInternal(TransitionSystem const & system) {
    std::size_t maxLoopUnrollings = std::numeric_limits<std::size_t>::max();
    PTRef init = system.getInit();
    PTRef query = system.getQuery();
    PTRef transition = system.getTransition();

    SMTSolver solverWrapper(logic, SMTSolver::WitnessProduction::NONE);
    auto & solver = solverWrapper.getCoreSolver();
//    std::cout << "Adding initial states: " << logic.pp(init) << std::endl;
    solver.insertFormula(init);
    { // Check for system with empty initial states
        auto res = solver.check();
        if (res == s_False) {
            return TransitionSystemVerificationResult{VerificationAnswer::SAFE, logic.getTerm_false()};
        }
    }

    TimeMachine tm{logic};
    for (std::size_t currentUnrolling = 0; currentUnrolling < maxLoopUnrollings; ++currentUnrolling) {
        PTRef versionedQuery = tm.sendFlaThroughTime(query, currentUnrolling);
//        std::cout << "Adding query: " << logic.pp(versionedQuery) << std::endl;
        solver.push();
        solver.insertFormula(versionedQuery);
        auto res = solver.check();
        if (res == s_True) {
            if (verbosity > 0) {
                std::cout << "; BMC: Bug found in depth: " << currentUnrolling << std::endl;
            }
            return TransitionSystemVerificationResult{.answer = VerificationAnswer::UNSAFE, .witness = static_cast<std::size_t>(currentUnrolling)};
        }
        if (verbosity > 1) {
            std::cout << "; BMC: No path of length " << currentUnrolling << " found!" << std::endl;
        }
        solver.pop();
        PTRef versionedTransition = tm.sendFlaThroughTime(transition, currentUnrolling);
//        std::cout << "Adding transition: " << logic.pp(versionedTransition) << std::endl;
        solver.insertFormula(versionedTransition);
    }
    return TransitionSystemVerificationResult{VerificationAnswer::UNKNOWN, 0u};
}
