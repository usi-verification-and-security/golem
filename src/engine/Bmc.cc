//
// Created by Martin Blicha on 17.07.20.
//

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
    // non-incremental solving
//    std::size_t maxLoopUnrollings = std::numeric_limits<std::size_t>::max();
    std::size_t maxLoopUnrollings = 100;
    std::size_t currentUnrolling = 0;
    SMTConfig config;
    while (currentUnrolling < maxLoopUnrollings) {
        auto fla = system.getPathFormula(currentUnrolling);
        MainSolver solver(logic, config, "BMC" + std::to_string(currentUnrolling));
        solver.insertFormula(fla);
        auto res = solver.check();
        if (res == s_True) {
            std::cout << "Bug found in depth: " << currentUnrolling << std::endl;
            return GraphVerificationResult(VerificationResult::UNSAFE, InvalidityWitness{});
        }
        ++currentUnrolling;
    }
    return GraphVerificationResult(VerificationResult::UNKNOWN);
}
