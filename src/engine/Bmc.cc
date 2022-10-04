/*
 * Copyright (c) 2020-2022, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "Bmc.h"
#include "TermUtils.h"
#include "TransformationUtils.h"

GraphVerificationResult BMC::solve(ChcDirectedGraph const & system) {
    if (isTransitionSystem(system)) {
        auto ts = toTransitionSystem(system, logic);
        return solveTransitionSystem(*ts);
    }
    return GraphVerificationResult(VerificationResult::UNKNOWN);
}

GraphVerificationResult BMC::solveTransitionSystem(TransitionSystem & system) {
    std::size_t maxLoopUnrollings = std::numeric_limits<std::size_t>::max();
    PTRef init = system.getInit();
    PTRef query = system.getQuery();
    PTRef transition = system.getTransition();

    SMTConfig config;
    MainSolver solver(logic, config, "BMC");
//    std::cout << "Adding initial states: " << logic.pp(init) << std::endl;
    solver.insertFormula(init);
    { // Check for system with empty initial states
        auto res = solver.check();
        if (res == s_False) {
            return GraphVerificationResult{VerificationResult::SAFE};
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
            // std::cout << "Bug found in depth: " << currentUnrolling << std::endl;
            return GraphVerificationResult(VerificationResult::UNSAFE, InvalidityWitness{});
        }
//        std::cout << "No path of length " << currentUnrolling << " found!\n";
        solver.pop();
        PTRef versionedTransition = tm.sendFlaThroughTime(transition, currentUnrolling);
//        std::cout << "Adding transition: " << logic.pp(versionedTransition) << std::endl;
        solver.insertFormula(versionedTransition);
    }
    return GraphVerificationResult(VerificationResult::UNKNOWN);
}
