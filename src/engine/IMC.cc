/*
 * Copyright (c) 2022, Konstantin Britikov <britikovki@gmail.com>
 * Copyright (c) 2023-2024, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "IMC.h"

#include "Common.h"
#include "TermUtils.h"
#include "TransformationUtils.h"
#include "transformers/SingleLoopTransformation.h"
#include "utils/SmtSolver.h"

TransitionSystemVerificationResult IMC::solve(TransitionSystem const & system) {
    { // if I /\ F is Satisfiable, return true
        SMTSolver solver(logic, SMTSolver::WitnessProduction::NONE);
        solver.assertProp(system.getInit());
        solver.assertProp(system.getQuery());
        if (solver.check() == SMTSolver::Answer::SAT) {
            return TransitionSystemVerificationResult{VerificationAnswer::UNSAFE, 0u};
        }
    }
    std::size_t maxLoopUnrollings = std::numeric_limits<std::size_t>::max();
    for (uint32_t k = 1; k < maxLoopUnrollings; ++k) {
        auto res = finiteRun(system, k);
        if (res.answer != VerificationAnswer::UNKNOWN) { return res; }
    }
    return TransitionSystemVerificationResult{VerificationAnswer::UNKNOWN, 0u};
}

namespace { // Helper method for IMC::finiteRun
PTRef getInterpolant(SMTSolver & solver, ipartitions_t const & mask) {
    auto itpContext = solver.getInterpolationContext();
    vec<PTRef> itps;
    itpContext->getSingleInterpolant(itps, mask);
    assert(itps.size() == 1);
    return itps[0];
}
} // namespace

// procedure FiniteRun(M=(I,T,F), k>0)
TransitionSystemVerificationResult IMC::finiteRun(TransitionSystem const & ts, unsigned k) {
    if (verbosity > 0) { std::cout << "[IMC] Checking with lookahead length " << k << '\n'; }
    assert(k > 0);
    SMTSolver solver(logic, SMTSolver::WitnessProduction::ONLY_INTERPOLANTS);
    solver.getConfig().setSimplifyInterpolant(4);
    TimeMachine tm{logic};
    PTRef suffix = [&]() {
        int lookahead = static_cast<int>(k);
        vec<PTRef> suffixTransitions;
        for (auto i = 1; i < lookahead; ++i) {
            suffixTransitions.push(tm.sendFlaThroughTime(ts.getTransition(), i));
        }
        suffixTransitions.push(tm.sendFlaThroughTime(ts.getQuery(), lookahead));
        return logic.mkAnd(std::move(suffixTransitions));
    }();
    solver.assertProp(suffix);
    solver.assertProp(ts.getTransition()); // first step, part of prefix
    PTRef movingInit = ts.getInit();
    PTRef reachedStates = ts.getInit();
    unsigned iter = 0;
    while (true) {
        solver.push();
        solver.assertProp(movingInit); // new initial states
        auto res = solver.check();
        // if prefix + suffix is satisfiable
        if (res == SMTSolver::Answer::SAT) {
            if (movingInit == ts.getInit()) {
                // Real counterexample
                return {VerificationAnswer::UNSAFE, iter + k};
            } else {
                // Possibly spurious counterexample => Abort and continue with larger k
                return {VerificationAnswer::UNKNOWN, PTRef_Undef};
            }
        } else { // if prefix + suffix is unsatisfiable
            ipartitions_t mask = 0;
            opensmt::setbit(mask, 1);        // for the prefix part of the TR
            opensmt::setbit(mask, iter + 2); // there are two formulas inserted at the base level: suffix + TR of prefix
            // let P = Itp(P, A, B)
            // let R' = P<W/W0>
            PTRef itp = getInterpolant(solver, mask);
            itp = tm.sendFlaThroughTime(itp, -1);
            // if R' => R return False(if R' /\ not R returns True)
            if (implies(itp, reachedStates)) {
                if (not computeWitness) { return {VerificationAnswer::SAFE, PTRef_Undef}; }
                PTRef inductiveInvariant = reachedStates;
                PTRef finalInductiveInvariant = computeFinalInductiveInvariant(inductiveInvariant, k, ts);
                return {VerificationAnswer::SAFE, finalInductiveInvariant};
            }
            movingInit = itp;
            reachedStates = logic.mkOr(reachedStates, itp);
        }
        iter++;
        solver.pop();
    }
}

bool IMC::implies(PTRef antecedent, PTRef consequent) const {
    SMTSolver solver(logic, SMTSolver::WitnessProduction::NONE);
    PTRef negated = logic.mkAnd(antecedent, logic.mkNot(consequent));
    solver.assertProp(negated);
    auto res = solver.check();
    return res == SMTSolver::Answer::UNSAT;
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
    SMTSolver solver(logic, SMTSolver::WitnessProduction::NONE);
    solver.assertProp(inductiveInvariant);
    solver.assertProp(ts.getQuery());
    auto res = solver.check();
    if (res == SMTSolver::Answer::UNSAT) { return inductiveInvariant; }
    // Otherwise compute safe inductive invariant from k-inductive invariant
    PTRef kinductive = logic.mkAnd(inductiveInvariant, logic.mkNot(ts.getQuery()));
    return kinductiveToInductive(kinductive, k, ts);
}
