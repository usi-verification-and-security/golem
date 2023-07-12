/*
* Copyright (c) 2023-2024, Stepan Henrych <stepan.henrych@gmail.com>
*
* SPDX-License-Identifier: MIT
*/

#include "PDKind.h"

#include "Common.h"
#include "MainSolver.h"
#include "ModelBasedProjection.h"
#include "PTRef.h"
#include "QuantifierElimination.h"
#include "TermUtils.h"
#include "TransformationUtils.h"
#include "transformers/BasicTransformationPipelines.h"
#include "transformers/SingleLoopTransformation.h"
#include <memory>
#include <queue>
#include <set>
#include <tuple>

VerificationResult PDKind::solve(ChcDirectedHyperGraph const & graph) {
    auto pipeline = Transformations::towardsTransitionSystems();
    auto transformationResult = pipeline.transform(std::make_unique<ChcDirectedHyperGraph>(graph));
    auto transformedGraph = std::move(transformationResult.first);
    auto translator = std::move(transformationResult.second);
    if (transformedGraph->isNormalGraph()) {
        auto normalGraph = transformedGraph->toNormalGraph();
        auto res = solve(*normalGraph);
        return computeWitness ? translator->translate(std::move(res)) : std::move(res);
    }
    return VerificationResult(VerificationAnswer::UNKNOWN);
}

VerificationResult PDKind::solve(ChcDirectedGraph const & system) {
    if (isTrivial(system)) {
        return solveTrivial(system);
    }
    if (isTransitionSystem(system)) {
        auto ts = toTransitionSystem(system);
        return solveTransitionSystem(*ts);
    }
    SingleLoopTransformation transformation;
    auto[ts, backtranslator] = transformation.transform(system);
    assert(ts);
    auto res = solveTransitionSystem(*ts);
    return res;
}

/**
 * Solve system with PDKIND algorithm.
 * @param system
 * @return
 */
VerificationResult PDKind::solveTransitionSystem (TransitionSystem const & system) {
    PTRef init = system.getInit();
    PTRef query = system.getQuery();

    ReachabilityChecker reachability_checker(logic, system);

    { // Check for system with empty initial states
        SMTConfig config;
        TimeMachine tm{logic};
        MainSolver init_solver(logic, config, "Empty initial states");
        init_solver.insertFormula(init);
        auto res = init_solver.check();
        if (res == s_False) { return VerificationResult{VerificationAnswer::SAFE}; }

        init_solver.insertFormula(query);
        res = init_solver.check();
        if (res == s_True) { return VerificationResult{VerificationAnswer::UNSAFE}; }
    }
    
    int n = 0;
    PTRef p = logic.mkNot(query);
    InductionFrame inductionFrame;
    inductionFrame.insert(IFrameElement(p, logic.mkNot(p)));

    // Solve the system by iteratively trying to construct an inductive strengthening of (p, not p) induction frame.
    while (true) {
        int k = n + 1; /* Pick k such that 1 <= k <= n + 1 */
        auto res = push(system, inductionFrame, n, k, reachability_checker);

        if (res.is_invalid) {
            return VerificationResult(VerificationAnswer::UNSAFE, InvalidityWitness{});
        }
        if (res.i_frame == res.new_i_frame) {
            return VerificationResult(VerificationAnswer::SAFE);
        }
        n = res.n;
        inductionFrame = res.new_i_frame;
    }
}

/**
 * Check if p is invariant by iteratively constructing k-inductive strengthening of p.
 * @param system
 * @param iframe
 * @param n
 * @param k
 * @param reachability_checker
 * @return
 */
PushResult PDKind::push(TransitionSystem const & system, InductionFrame & iframe, int n, int k, ReachabilityChecker & reachability_checker) {
    // Prepare config and tm for solver initialization.
    SMTConfig config;
    TimeMachine tm{logic};

    // Create a queue q and initialize it with iframe.
    std::queue<IFrameElement> q;
    for (auto e : iframe) {
        q.push(e);
    }
    
    // Initialize used variables.
    std::size_t maxUnrollings = k;
    PTRef transition = system.getTransition();
    InductionFrame newIframe = {};
    int np = n + k;
    bool invalid = false;
    int steps_to_ctx = 0;
    
    while (not invalid && not q.empty()) {
        IFrameElement obligation = q.front();
        q.pop();
        
        // Initialize iframe_abs, which is a conjunction of lemmas from iframe.
        std::vector<PTRef> iframe_abs_vec  = {};
        for (auto e : iframe) {
            iframe_abs_vec.push_back(e.lemma);
        }
        PTRef iframe_abs = logic.mkAnd(iframe_abs_vec);

        // Create transition T[F_ABS]^k by definition.
        PTRef t_k = transition;
        PTRef f_abs_conj = logic.getTerm_true();
        std::size_t currentUnrolling;
        for (currentUnrolling = 1; currentUnrolling < maxUnrollings; ++currentUnrolling) {
            PTRef versionedFla = tm.sendFlaThroughTime(iframe_abs, currentUnrolling);
            PTRef versionedTransition = tm.sendFlaThroughTime(transition, currentUnrolling);
            t_k = logic.mkAnd(t_k, versionedTransition);
            f_abs_conj = logic.mkAnd(f_abs_conj, versionedFla);
        }

        PTRef not_fabs = logic.mkNot(obligation.lemma);
        PTRef versioned_not_fabs = tm.sendFlaThroughTime(not_fabs, currentUnrolling);
        PTRef t_k_constr = logic.mkAnd(t_k, f_abs_conj);

        // Check if iframe_abs is k-inductive?
        MainSolver solver1(logic, config, "iframe_abs k-inductivity");
        solver1.insertFormula(iframe_abs);
        solver1.insertFormula(t_k_constr);
        solver1.insertFormula(versioned_not_fabs);
        auto res1 = solver1.check();

        if (res1 == s_False) {
            newIframe.insert(obligation);
            continue;
        }

        auto model1 = solver1.getModel();

        // Check if f_cex is reachable.
        PTRef f_cex = tm.sendFlaThroughTime(obligation.counter_example.ctx, currentUnrolling);
        MainSolver solver2(logic, config, "f_cex reachability");
        solver2.insertFormula(iframe_abs);
        solver2.insertFormula(t_k_constr);
        solver2.insertFormula(f_cex);
        auto res2 = solver2.check();

        if (res2 == s_True) {
            auto model2 = solver2.getModel();
            CounterExample g_cex (reachability_checker.generalize(*model2, t_k, f_cex), obligation.counter_example.num_of_steps + k);
            auto reach_res = reachability_checker.checkReachability(n - k + 1, n, g_cex.ctx);
            if (std::get<0>(reach_res)) {
                // g_cex is reachable, return invalid.
                invalid = true;
                steps_to_ctx = g_cex.num_of_steps + std::get<1>(reach_res); // This is needed for invalidity proof
                continue;
            } else {
                // Eliminate g_cex.
                PTRef g_abs = std::get<2>(reach_res);
                IFrameElement newObligation = IFrameElement(g_abs, g_cex);
                iframe.insert(newObligation);
                q.push(newObligation);
                q.push(obligation);
                continue;
            }
        }

        // Analyze the induction failure.
        PTRef g_cti = reachability_checker.generalize(*model1, t_k, versioned_not_fabs);
        auto reach_res = reachability_checker.checkReachability(n - k + 1, n, g_cti);
        if (std::get<0>(reach_res)) {
            // Insert weaker obligation : (not f_cex, f_cex).
            reach_res = reachability_checker.checkReachability(n + 1, std::get<1>(reach_res) + k, not_fabs);
            np = std::min(np, std::get<1>(reach_res));
            IFrameElement newObligation = IFrameElement(logic.mkNot(obligation.counter_example.ctx), obligation.counter_example);
            iframe.insert(newObligation);
            newIframe.insert(newObligation);
        } else {
            // Strengthen f_abs by g_abs.
            PTRef g_abs = std::get<2>(reach_res);
            g_abs = logic.mkAnd(obligation.lemma, g_abs);
            IFrameElement newObligation = IFrameElement(g_abs, obligation.counter_example);
            iframe.insert(newObligation);
            iframe.erase(obligation);
            q.push(newObligation);
        }
    }
    PushResult res(iframe, newIframe, np, invalid, steps_to_ctx);
    return res;
}

/**
 * Recursively checks if formula is reachable in k steps from initial states by updating and using the reachability frame.
 * @param k number of steps
 * @param formula
 * @return true if is reachable, false and interpolant if isn't
 */
std::tuple<bool, PTRef> ReachabilityChecker::reachable(unsigned k, PTRef formula) {
    SMTConfig config;
    const char * msg = "ok";
    config.setOption(SMTConfig::o_produce_inter, SMTOption(true), msg);
    config.setSimplifyInterpolant(4);
    TimeMachine tm{logic};

    // Check reachability from initial states in 0 steps.
    if (k == 0) {
        MainSolver init_solver(logic, config, "Init state reachability");
        init_solver.insertFormula(system.getInit());
        init_solver.insertFormula(formula);
        auto res = init_solver.check();
        if (res == s_False) {
            auto itpContext = init_solver.getInterpolationContext();
            vec<PTRef> itps;
            int mask = 1;
            itpContext->getSingleInterpolant(itps, mask);
            assert(itps.size() == 1);
            return std::make_tuple(false, itps[0]);
        }
        return std::make_tuple(true, logic.getTerm_false());
    }
    PTRef versioned_formula = tm.sendFlaThroughTime(formula, 1); // Send the formula through time by one, so it matches the pattern init_0 transition_0-1 formula_1.
    while (true) {
        // Check if formula is reachable from r_frame[k-1] in 1 step.
        MainSolver solver(logic, config, "Transitioned states rechability");
        solver.insertFormula(r_frame[k-1]);
        solver.insertFormula(system.getTransition());
        solver.insertFormula(versioned_formula);
        auto res = solver.check();

        // If is reachable, create a generalization of such states and check if they are reachable in k-1 steps.
        if (res == s_True) {
            auto model = solver.getModel();
            PTRef g = generalize(*model,system.getTransition(), versioned_formula);
            auto reach_res = reachable(k-1, g);
            // If is reachable return true, else update the reachability frame.
            if (std::get<0>(reach_res)) {
                return std::make_tuple(true, logic.getTerm_false());
            } else {
                r_frame.insert(std::get<1>(reach_res), k-1);
            }
        } else {
            /*
             *  Get interpolant
             */
            auto itpContext = solver.getInterpolationContext();
            vec<PTRef> itps;
            int mask = 3; // A ^ B => C
            itpContext->getSingleInterpolant(itps, mask);
            assert(itps.size() == 1);
            PTRef interpolant = tm.sendFlaThroughTime(itps[0], -1);

            /*
             *  Get interpolant for initial states. If it exists, return disjunction of both interpolants.
             */
            MainSolver init_solver(logic, config, "Initial states interpolant");
            init_solver.insertFormula(system.getInit());
            init_solver.insertFormula(formula);

            auto res = init_solver.check();
            if (res == s_False) {
                auto itpContext = init_solver.getInterpolationContext();
                vec<PTRef> itps;
                int mask = 1;
                itpContext->getSingleInterpolant(itps, mask);
                assert(itps.size() == 1);
                PTRef init_interpolant = itps[0];

                return std::make_tuple(false, logic.mkOr(interpolant, init_interpolant));
            }

            return std::make_tuple(false, interpolant);
        }
    }
}

/**
 * Checks if formula is reachable in k_from to k_to steps.
 * @param k_from    least number of steps
 * @param k_to      max number of steps
 * @param formula   tested formula
 * @return is reachable, number of steps, interpolant of the formula if not reachable
 */
std::tuple<bool, int, PTRef> ReachabilityChecker::checkReachability (int k_from, int k_to, PTRef formula) {
    for (int i = k_from; i <= k_to; i++) {
        auto reach_res = reachable(i, formula);
        if (std::get<0>(reach_res)) {
            return std::make_tuple(true, i, logic.getTerm_false());
        }
        if (i == k_to) {
            return std::make_tuple(false, i, std::get<1>(reach_res));
        }
    }
    return std::make_tuple(false, 0, logic.getTerm_false());
}

/**
 * Creates a generalization of a formula by removing non-state variables.
 * @param model
 * @param transition
 * @param formula
 * @return
 */
PTRef ReachabilityChecker::generalize(Model & model, PTRef transition, PTRef formula) {
    auto xvars = system.getStateVars();

    PTRef conj = logic.mkAnd(transition, formula);
    ModelBasedProjection mbp(logic);
    PTRef g = mbp.keepOnly(conj, xvars, model);

    return g;
}