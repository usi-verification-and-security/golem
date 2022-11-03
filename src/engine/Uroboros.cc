/*
 * Copyright (c) 2022, Konstantin Britikov <britikovki@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "Uroboros.h"
#include "TermUtils.h"
#include "TransformationUtils.h"

GraphVerificationResult Uroboros::solve(ChcDirectedGraph const & system) {
    if (isTransitionSystem(system)) {
        auto ts = toTransitionSystem(system, logic);
        return solveTransitionSystem(*ts, system);
    }
    return GraphVerificationResult(VerificationResult::UNKNOWN);
}

GraphVerificationResult Uroboros::solveTransitionSystem(TransitionSystem const & system, ChcDirectedGraph const & graph) {
    std::size_t maxLoopUnrollings = std::numeric_limits<std::size_t>::max();
    PTRef init = system.getInit();
    PTRef query = system.getQuery();
    PTRef transition = system.getTransition();
    vec<PTRef> itps;

    SMTConfig config;
    SMTConfig itp_config;
    const char * msg = "ok";
    config.setOption(SMTConfig::o_produce_inter, SMTOption(true), msg);
    config.setSimplifyInterpolant(4);
    MainSolver solver(logic, config, "Uroboros");
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
            if (verbosity > 0) {
                std::cout << "; Uroboros: Bug found in depth: " << currentUnrolling << std::endl;
            }
            return GraphVerificationResult(VerificationResult::UNSAFE, InvalidityWitness::fromTransitionSystem(graph, currentUnrolling));
        }
        PTRef itp = lastIterationInterpolant(solver);
        PTRef itpsOld = logic.mkOr(itps);
        auto resItp = checkItp(itp, itpsOld, logic);
        if (resItp == s_False){
            return GraphVerificationResult(VerificationResult::SAFE);
        } else {
            itps.push(itp);
        }
        if (verbosity > 1) {
            std::cout << "; Uroboros: No path of length " << currentUnrolling << " found!" << std::endl;
        }
        solver.pop();
        PTRef versionedTransition = tm.sendFlaThroughTime(transition, currentUnrolling);
//        std::cout << "Adding transition: " << logic.pp(versionedTransition) << std::endl;
        solver.insertFormula(versionedTransition);
    }
    return GraphVerificationResult(VerificationResult::UNKNOWN);
}

PTRef Uroboros::lastIterationInterpolant(MainSolver& solver) {
    auto itpContext = solver.getInterpolationContext();
    vec<PTRef> itps;
    ipartitions_t mask = 1;
    itpContext->getSingleInterpolant(itps, mask);
    return itps[0];
}

sstat Uroboros::checkItp(PTRef & itp, PTRef & itpsOld, Logic & logic){
    SMTConfig itp_config;
    PTRef cmp = logic.mkAnd(itp, logic.mkNot(itpsOld));
    MainSolver itpSolver(logic, itp_config, "Interpolant");
    itpSolver.insertFormula(cmp);
    return itpSolver.check();
}
