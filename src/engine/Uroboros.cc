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

    SMTConfig config;
    const char * msg = "ok";
    config.setOption(SMTConfig::o_produce_inter, SMTOption(true), msg);
    config.setSimplifyInterpolant(4);
    MainSolver solver(logic, config, "Uroboros");
    Logic & initLogic = logic;
//    std::cout << "Adding initial states: " << logic.pp(init) << std::endl;
//    solver.insertFormula(init);
    { // Check for system with empty initial states
        auto res = solver.check();
        if (res == s_False) {
            return GraphVerificationResult{VerificationResult::SAFE};
        }
    }
    TimeMachine tm{logic};
    for (int k = 1; k < maxLoopUnrollings; ++k) {
        InterpolantResult res = finiteRun(init, transition, query, k);
        if(res.result == l_True){
            return GraphVerificationResult{VerificationResult::UNSAFE,  InvalidityWitness::fromTransitionSystem(graph, res.depth)};
        } if (res.result == l_False){
            return GraphVerificationResult{VerificationResult::SAFE, ValidityWitness::fromTransitionSystem(logic, graph, system, res.interpolant)};
        }
    }
    return GraphVerificationResult(VerificationResult::UNKNOWN);
}

//procedure FiniteRun(M=(I,T,F), k>0)
Uroboros::InterpolantResult Uroboros::finiteRun(PTRef & init, PTRef & transition, PTRef & query, int & k) {
    SMTConfig config;
    const char * msg = "ok";
    config.setOption(SMTConfig::o_produce_inter, SMTOption(true), msg);
    config.setSimplifyInterpolant(4);
    TimeMachine tm{logic};
    ipartitions_t mask = 0;

    MainSolver initSolver(logic, config, "Uroboros");
    initSolver.insertFormula(init);
    PTRef versionedQuery = tm.sendFlaThroughTime(query, 0);
    initSolver.insertFormula(versionedQuery);
    //if I /\ F is Satisfiable, return true
    if(initSolver.check() == s_True){
        return InterpolantResult{l_True, 0, init};
    }
    PTRef movingInit = init;
    printf("init: %s\n", logic.pp(init).c_str());
    int iter = 0;
    // while true
    while(true){
        MainSolver solver(logic, config, "Uroboros");
        //A = CNF(PREF1(M'), U1)
        solver.insertFormula(init);
        PTRef A = logic.mkAnd(movingInit, tm.sendFlaThroughTime(transition, iter));
        printf("A: %s\n", logic.pp(A).c_str());
        solver.insertFormula(A);
        //B = CNF(SUFFk(M'), U2)
        solver.push();
        PTRef B = tm.sendFlaThroughTime(query, iter + k);
//        logic.pp();
        for(int i = iter + 1; i < iter + k; i++){
            B = logic.mkAnd(B, tm.sendFlaThroughTime(transition, i));
        }
        printf("B: %s\n", logic.pp(B).c_str());
        solver.insertFormula(B);
        // Run SAT on A U B.
        auto res = solver.check();
        // if A U B is satisfiable
        if(res == s_True){
            if(movingInit == init){
                // if R=I return True
                return InterpolantResult{l_True, iter+k, init};
            } else{
                // else Abort
                return InterpolantResult{l_Undef, iter+k, init};
            }
            // else if A U B is unsat
        } else {
            opensmt::setbit(mask, 0);
            //opensmt::setbit(mask, 1);
            //let P = Itp(P, A, B)
            //let R' = P(W/W0)
            PTRef itp = lastIterationInterpolant(solver, mask);
            printf("Itp: %s\n", logic.pp(itp).c_str());
            movingInit = tm.sendFlaThroughTime(movingInit, iter+1);
            printf("New init: %s\n", logic.pp(init).c_str());
            //if R' => R return False(if R' /\ not R returns True)
            if(checkItp(itp, movingInit) == s_True){
                return InterpolantResult{l_False, iter+k, itp};
            }
            // let R = R\/R'
            movingInit = logic.mkOr(movingInit, itp);
            printf("Moving init: %s\n", logic.pp(init).c_str());
        }
        iter++;
    }
}

PTRef Uroboros::lastIterationInterpolant(MainSolver& solver, ipartitions_t mask) {
    auto itpContext = solver.getInterpolationContext();
    vec<PTRef> itps;
    itpContext->getSingleInterpolant(itps, mask);
    assert(itps.size() == 1);
    return itps[0];
}

sstat Uroboros::checkItp(PTRef itp, PTRef itpsOld){
    SMTConfig itp_config;
    PTRef cmp = logic.mkAnd(itp, logic.mkNot(itpsOld));
    MainSolver itpSolver(logic, itp_config, "Interpolant");
    itpSolver.insertFormula(cmp);
    return itpSolver.check();
}
