/*
 * Copyright (c) 2022, Konstantin Britikov <britikovki@gmail.com>
 * Copyright (c) 2023, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "IMC.h"

#include "Common.h"
#include "TermUtils.h"
#include "TransformationUtils.h"
#include "transformers/SingleLoopTransformation.h"

VerificationResult IMC::solve(ChcDirectedGraph const & graph) {
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

VerificationResult IMC::solveTransitionSystem(ChcDirectedGraph const & graph) {
    auto ts = toTransitionSystem(graph);
    auto res = solveTransitionSystemInternal(*ts);
    return translateTransitionSystemResult(res, graph, *ts);
}

TransitionSystemVerificationResult IMC::solveTransitionSystemInternal(TransitionSystem const & system) {
    std::size_t maxLoopUnrollings = std::numeric_limits<std::size_t>::max();

    SMTConfig config;
    const char * msg = "ok";
    config.setOption(SMTConfig::o_produce_inter, SMTOption(true), msg);
    config.setSimplifyInterpolant(4);
    TimeMachine tm{logic};
    MainSolver initSolver(logic, config, "IMC");
    initSolver.insertFormula(system.getInit());
    initSolver.insertFormula(system.getQuery());
    //if I /\ F is Satisfiable, return true
    if (initSolver.check() == s_True) {
        return TransitionSystemVerificationResult{VerificationAnswer::UNSAFE, 0u};
    }
    for (uint32_t k = 1; k < maxLoopUnrollings; ++k) {
        InterpolantResult res = finiteRun(system, k);
        if (res.result == l_True) {
            return TransitionSystemVerificationResult{VerificationAnswer::UNSAFE, static_cast<std::size_t>(res.depth)};
        }
        if (res.result == l_False) {
            return TransitionSystemVerificationResult{VerificationAnswer::SAFE, res.interpolant};
        }
    }
    return TransitionSystemVerificationResult{VerificationAnswer::UNKNOWN, 0u};
}

//procedure FiniteRun(M=(I,T,F), k>0)
IMC::InterpolantResult IMC::finiteRun(TransitionSystem const & ts, unsigned k) {
    assert(k > 0);
    SMTConfig config;
    const char * msg = "ok";
    config.setOption(SMTConfig::o_produce_inter, SMTOption(true), msg);
    config.setSimplifyInterpolant(4);
    TimeMachine tm{logic};
    PTRef movingInit = ts.getInit();
    unsigned iter = 0;
    // while true
    while (true) {
        MainSolver solver(logic, config, "IMC");
        //A = CNF(PREF1(M'), U1)
        PTRef A = logic.mkAnd(movingInit, tm.sendFlaThroughTime(ts.getTransition(), iter));
        solver.insertFormula(A);
        //B = CNF(SUFFk(M'), U2)
        PTRef B = tm.sendFlaThroughTime(ts.getQuery(), iter + k);
        for (unsigned i = iter + 1; i < iter + k; ++i) {
            B = logic.mkAnd(B, tm.sendFlaThroughTime(ts.getTransition(), i));
        }
        solver.insertFormula(B);
        // Run SAT on A U B.
        auto res = solver.check();
        // if A U B is satisfiable
        if (res == s_True) {
            if (movingInit == ts.getInit()) {
                // if R=I return True
                return InterpolantResult{l_True, iter + k, PTRef_Undef};
            } else {
                // else Abort
                return InterpolantResult{l_Undef, iter + k, PTRef_Undef};
            }
            // else if A U B is unsat
        } else {
            ipartitions_t mask = 0;
            opensmt::setbit(mask, 0);
            //opensmt::setbit(mask, 1);
            //let P = Itp(P, A, B)
            //let R' = P<W/W0>
            PTRef itp = lastIterationInterpolant(solver, mask);
            movingInit = tm.sendFlaThroughTime(movingInit, 1);
            //if R' => R return False(if R' /\ not R returns True)
            if (checkItp(itp, movingInit) == s_False) {
                PTRef inductiveInvariant = tm.sendFlaThroughTime(movingInit, -iter - 1);
                PTRef finalInductiveInvariant = computeFinalInductiveInvariant(inductiveInvariant, k, ts);
                return InterpolantResult{l_False, iter + k, finalInductiveInvariant};
            }
            // let R = R\/R'
            movingInit = logic.mkOr(movingInit, itp);
        }
        iter++;
    }
}

PTRef IMC::lastIterationInterpolant(MainSolver & solver, ipartitions_t const & mask) {
    auto itpContext = solver.getInterpolationContext();
    vec<PTRef> itps;
    itpContext->getSingleInterpolant(itps, mask);
    assert(itps.size() == 1);
    return itps[0];
}

sstat IMC::checkItp(PTRef itp, PTRef itpsOld) {
    SMTConfig itp_config;
    PTRef cmp = logic.mkAnd(itp, logic.mkNot(itpsOld));
    MainSolver itpSolver(logic, itp_config, "Interpolant");
    itpSolver.insertFormula(cmp);
    return itpSolver.check();
}

/**
 * In our current implementation, we find an inductive invariant that is not necessarily safe, we only know that it
 * cannot reach Bad in k steps. However, we also know that Bad cannot be truly reachable, otherwise the path would have
 * been discovered earlier.
 * What we definitely know is that Inv and ~Bad is safe k-inductive invariant. Since Inv is inductive, it follows that
 * after k steps, we stay in Inv, but we also know we cannot reach Bad, thus we reach Inv and ~Bad again.
 *
 * @param inductiveInvariant an inductive invariant of the system
 * @param k number of steps for which Bad in not reachable from the invariant
 * @param ts transition system
 * @return safe inductive invariant of the system
 */
PTRef IMC::computeFinalInductiveInvariant(PTRef inductiveInvariant, unsigned k, TransitionSystem const & ts) {
    SMTConfig config;
    MainSolver solver(logic, config, "");
    solver.insertFormula(inductiveInvariant);
    solver.insertFormula(ts.getQuery());
    auto res = solver.check();
    if (res == s_False) { return inductiveInvariant; }
    // Otherwise compute safe inductive invariant from k-inductive invariant
    PTRef kinductive = logic.mkAnd(inductiveInvariant, logic.mkNot(ts.getQuery()));
    return kinductiveToInductive(kinductive, k, ts);
}
