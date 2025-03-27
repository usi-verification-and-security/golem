/*
* Copyright (c) 2023-2024, Stepan Henrych <stepan.henrych@gmail.com>
*
* SPDX-License-Identifier: MIT
*/

#include "PDKind.h"

#include "Common.h"
#include "ModelBasedProjection.h"
#include "TermUtils.h"
#include "TransformationUtils.h"
#include "transformers/BasicTransformationPipelines.h"
#include "transformers/SingleLoopTransformation.h"
#include "utils/ScopeGuard.h"
#include "utils/SmtSolver.h"

#include <memory>
#include <queue>
#include <set>
#include <tuple>


/**
 * Counter example formula in addition with number of steps needed to reach the counter example.
 */
struct CounterExample {
    PTRef ctx;
    unsigned num_of_steps;
    CounterExample(PTRef ctx, unsigned num_of_steps) : ctx(ctx), num_of_steps(num_of_steps) {}
};

/**
 * Tuple containing lemma and counter example.
 */
struct IFrameElement {
        PTRef lemma;
        CounterExample counter_example;

        IFrameElement(PTRef lemma, CounterExample counter_example) : lemma(lemma), counter_example(counter_example) {}

        bool operator==(IFrameElement const & other) const {
            return this->lemma == other.lemma && this->counter_example.ctx == other.counter_example.ctx;
        }

        bool operator<(IFrameElement const & other) const {
            if (this->lemma == other.lemma) {
                return this->counter_example.ctx < other.counter_example.ctx;
            } else {
                return this->lemma < other.lemma;
            }
        }
};

/**
 * Wrapper for Induction Frame set.
 */
using InductionFrame = std::set<IFrameElement>;

/**
 * Wrapper for return value of the Push function.
 */
struct PushResult {
    InductionFrame i_frame;
    InductionFrame new_i_frame;
    unsigned n;
    bool is_invalid;
    unsigned steps_to_ctx;
    PushResult(InductionFrame i_frame,
               InductionFrame new_i_frame,
               unsigned n,
               bool is_invalid,
               unsigned steps_to_ctx) : i_frame(std::move(i_frame)), new_i_frame(std::move(new_i_frame)), n(n), is_invalid(is_invalid), steps_to_ctx(steps_to_ctx) {}
};

struct Reachable {
    std::size_t steps{};
};

struct Unreachable {
    PTRef explanation{PTRef_Undef};
};

using ReachabilityResult = std::variant<Reachable, Unreachable>;

namespace SolverAnswer {
struct Feasible {
    std::unique_ptr<Model> model;
};
struct Infeasible {
    PTRef interpolant;
};
using Answer = std::variant<Feasible, Infeasible>;
}

class FrameSolver {
public:
    explicit FrameSolver(Logic & logic, PTRef transition) : logic(logic), transition(transition) {
        solver = std::make_unique<SMTSolver>(logic, SMTSolver::WitnessProduction::MODEL_AND_INTERPOLANTS);
        solver->getConfig().setSimplifyInterpolant(4);
    }
    SolverAnswer::Answer checkFeasibility(PTRef state);
    void addLemma(PTRef lemma);
private:
    Logic & logic;
    PTRef transition;
    vec<PTRef> lemmas;
    std::unique_ptr<SMTSolver> solver;
    // std::size_t queryRestartLimit = 100;
};

/**
 * A data structure where r[i] represents the states that are reachable in i steps from some initial states, i.e., r[0].
 */
class RFrames {
public:
    explicit RFrames(Logic & logic, PTRef transition) : logic(logic), transition(transition) {
        ensureReadyFor(0);
    }

    SolverAnswer::Answer queryWithTransitionAt(std::size_t k, PTRef state);
    void addLemma(std::size_t k, PTRef lemma) {
        ensureReadyFor(k);
        solvers[k].addLemma(lemma);
    }

private:
    std::vector<FrameSolver> solvers;

    Logic & logic;
    PTRef transition;

    void ensureReadyFor(size_t k) {
        while (k >= solvers.size()) {
            solvers.emplace_back(logic, transition);
        }
    }
};

/**
 * Each instance builds its own reachability frame and uses it to check if other states are reachable in k steps.
 */
class ReachabilityChecker {
private:
    RFrames r_frames;
    Logic & logic;
    TransitionSystem const & system;
    std::unique_ptr<SMTSolver> zeroStepSolver;

    ReachabilityResult reachable(unsigned k, PTRef formula);
    [[nodiscard]] ReachabilityResult zeroStepReachability(PTRef state);
public:
    ReachabilityChecker(Logic & logic, TransitionSystem const & system) : r_frames(logic, system.getTransition()), logic(logic), system(system) {
        zeroStepSolver = std::make_unique<SMTSolver>(logic, SMTSolver::WitnessProduction::ONLY_INTERPOLANTS);
        zeroStepSolver->getConfig().setSimplifyInterpolant(4);
        zeroStepSolver->assertProp(system.getInit());
    }
    ReachabilityResult checkReachability(unsigned from, unsigned to, PTRef formula);
};

class Context {
public:
    Context(Logic & logic, bool computeWitness) : logic(logic), computeWitness(computeWitness) {}

    TransitionSystemVerificationResult solve(TransitionSystem const & system);
private:
    Logic & logic;
    bool computeWitness;

    [[nodiscard]]
    PushResult push(TransitionSystem const & system, InductionFrame & iframe, unsigned n, unsigned k, ReachabilityChecker & reachability_checker) const;

    [[nodiscard]]
    PTRef getInvariant(InductionFrame const & iframe, unsigned int k, TransitionSystem const & system) const;
};

TransitionSystemVerificationResult PDKind::solve(TransitionSystem const & system) {
    return Context(logic, computeWitness).solve(system);
}

TransitionSystemVerificationResult Context::solve(TransitionSystem const & system) {
    PTRef init = system.getInit();
    PTRef query = system.getQuery();

    { // Check for system with empty initial states and system where initial and bad states intersect.
        SMTSolver solver(logic, SMTSolver::WitnessProduction::NONE);
        solver.assertProp(init);
        auto res = solver.check();
        if (res == SMTSolver::Answer::UNSAT) {
            return TransitionSystemVerificationResult{VerificationAnswer::SAFE, logic.getTerm_false()};
        }
        solver.assertProp(query);
        res = solver.check();
        if (res == SMTSolver::Answer::SAT) {
            return TransitionSystemVerificationResult{.answer = VerificationAnswer::UNSAFE, .witness = static_cast<std::size_t>(0)};
        }
    }
    
    unsigned n = 0;
    PTRef p = logic.mkNot(query);
    InductionFrame inductionFrame;
    inductionFrame.insert(IFrameElement(p, CounterExample(query, 0u)));

    ReachabilityChecker reachability_checker(logic, system);
    // Solve the system by iteratively trying to construct an inductive strengthening of (p, not p) induction frame.
    while (true) {
        unsigned k = n + 1; /* Pick k such that 1 <= k <= n + 1 */
        auto res = push(system, inductionFrame, n, k, reachability_checker);

        if (res.is_invalid) {
            auto steps_to_ctx = res.steps_to_ctx;
            return TransitionSystemVerificationResult{.answer = VerificationAnswer::UNSAFE, .witness = static_cast<std::size_t>(steps_to_ctx)};
        }
        if (res.i_frame == res.new_i_frame) {
            if (computeWitness) {
                auto invariant = getInvariant(res.i_frame, res.n, system);
                return TransitionSystemVerificationResult{VerificationAnswer::SAFE, invariant};
            }
            return TransitionSystemVerificationResult{VerificationAnswer::SAFE, logic.getTerm_false()};
        }
        n = res.n;
        inductionFrame = res.new_i_frame;
    }
}

/**
 * Creates a generalization of a formula by removing non-state variables.
 */
PTRef generalize(Logic & logic, Model & model, std::vector<PTRef> const & stateVars, PTRef transition, PTRef formula) {
    PTRef conj = logic.mkAnd(transition, formula);
    ModelBasedProjection mbp(logic);
    PTRef g = mbp.keepOnly(conj, stateVars, model);
    return g;
}

/**
 * Check if p is invariant by iteratively constructing k-inductive strengthening of p.
 */
PushResult Context::push(TransitionSystem const & system, InductionFrame & iframe, unsigned const n, unsigned const k, ReachabilityChecker & reachability_checker) const {
    // Create a queue q and initialize it with iframe.
    std::queue<IFrameElement> q;
    for (auto e : iframe) {
        q.push(e);
    }
    
    // Initialize used variables.
    TimeMachine tm{logic};
    PTRef transition = system.getTransition();
    InductionFrame newIframe = {};
    unsigned np = n + k;
    bool invalid = false;
    int steps_to_ctx = 0;

    PTRef kTransition = [&]() {
        vec<PTRef> transitions {transition};
        for (unsigned currentUnrolling = 1; currentUnrolling < k; ++currentUnrolling) {
            transitions.push(tm.sendFlaThroughTime(transition, static_cast<int>(currentUnrolling)));
        }
        return logic.mkAnd(std::move(transitions));
    }();

    SMTSolver kinductionChecker(logic, SMTSolver::WitnessProduction::ONLY_MODEL);
    kinductionChecker.assertProp(kTransition);
    
    while (not invalid && not q.empty()) {
        IFrameElement obligation = q.front();
        q.pop();
        
        PTRef iframe_abs = [&]() {
            vec<PTRef> iframe_abs_vec;
            for (auto e : iframe) {
                iframe_abs_vec.push(e.lemma);
            }
            return logic.mkAnd(std::move(iframe_abs_vec));
        }();

        // Create transition T[F_ABS]^k by definition.
        PTRef transitionRestriction = [&]() -> PTRef {
            vec<PTRef> frameComponents {iframe_abs};
            for (unsigned currentUnrolling = 1; currentUnrolling < k; ++currentUnrolling) {
                frameComponents.push(tm.sendFlaThroughTime(iframe_abs, static_cast<int>(currentUnrolling)));
            }
            return logic.mkAnd(std::move(frameComponents));
        }();

        PTRef not_fabs = logic.mkNot(obligation.lemma);
        PTRef versioned_not_fabs = tm.sendFlaThroughTime(not_fabs, static_cast<int>(k));

        // Check if iframe_abs is k-inductive?
        ScopeGuard popGuard = ScopeGuard{[&kinductionChecker] {
            kinductionChecker.pop();
            kinductionChecker.pop();
        }};
        kinductionChecker.push();
        kinductionChecker.assertProp(transitionRestriction);
        kinductionChecker.push();
        kinductionChecker.assertProp(versioned_not_fabs);
        auto res1 = kinductionChecker.check();
        if (res1 == SMTSolver::Answer::UNSAT) {
            newIframe.insert(obligation);
            continue;
        }
        auto inductionFailureWitness = kinductionChecker.getModel();


        // Check if f_cex is reachable.
        kinductionChecker.pop();
        kinductionChecker.push();
        PTRef f_cex = tm.sendFlaThroughTime(obligation.counter_example.ctx, static_cast<int>(k));
        kinductionChecker.assertProp(f_cex);
        auto res2 = kinductionChecker.check();

        if (res2 == SMTSolver::Answer::SAT) {
            CounterExample g_cex(generalize(logic, *kinductionChecker.getModel(), system.getStateVars(), kTransition, f_cex), obligation.counter_example.num_of_steps + k);
            // Remember num of steps for each cex, g_cex is f_cex + k
            auto reach_res = reachability_checker.checkReachability(n - k + 1, n, g_cex.ctx);
            if (std::holds_alternative<Reachable>(reach_res)) {
                // g_cex is reachable, return invalid.
                invalid = true;
                steps_to_ctx = g_cex.num_of_steps + std::get<Reachable>(reach_res).steps; // This is needed for invalidity proof
                continue;
            } else {
                // Eliminate g_cex.
                assert(std::holds_alternative<Unreachable>(reach_res));
                PTRef g_abs = std::get<Unreachable>(reach_res).explanation;
                IFrameElement newObligation = IFrameElement(g_abs, g_cex);
                iframe.insert(newObligation);
                q.push(newObligation);
                q.push(obligation);
                continue;
            }
        }

        // Analyze the induction failure.
        PTRef g_cti = generalize(logic, *inductionFailureWitness, system.getStateVars(), kTransition, versioned_not_fabs);
        auto reach_res = reachability_checker.checkReachability(n - k + 1, n, g_cti);
        if (std::holds_alternative<Reachable>(reach_res)) {
            // Insert weaker obligation : (not f_cex, f_cex).
            reach_res = reachability_checker.checkReachability(n + 1, std::get<Reachable>(reach_res).steps + k, not_fabs);
            assert(std::holds_alternative<Reachable>(reach_res));
            np = std::min<std::size_t>(np, std::get<Reachable>(reach_res).steps);
            IFrameElement newObligation = IFrameElement(logic.mkNot(obligation.counter_example.ctx), obligation.counter_example);
            iframe.insert(newObligation);
            newIframe.insert(newObligation);
        } else {
            // Strengthen f_abs by g_abs.
            assert(std::holds_alternative<Unreachable>(reach_res));
            PTRef g_abs = std::get<Unreachable>(reach_res).explanation;
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
 * Make k-inductive invariant as a conjunction of formulas in frame and transofmr it to inductive invariant.
 * @return inductive invariant
 */
PTRef Context::getInvariant(const InductionFrame & iframe, unsigned int k, TransitionSystem const & system) const {
    std::vector<PTRef> lemmas;
    for(auto o : iframe) {
        lemmas.push_back(o.lemma);
    }
    PTRef kinvariant = logic.mkAnd(lemmas);
    return kinductiveToInductive(kinvariant, k, system);
}

ReachabilityResult ReachabilityChecker::zeroStepReachability(PTRef state) {
    auto & solver = *this->zeroStepSolver;
    ScopeGuard guard{[&](){ solver.pop(); }};
    solver.push();
    solver.assertProp(state);
    auto res = solver.check();
    if (res == SMTSolver::Answer::UNSAT) {
        auto itpContext = solver.getInterpolationContext();
        vec<PTRef> itps;
        int mask = 1;
        itpContext->getSingleInterpolant(itps, mask);
        assert(itps.size() == 1);
        return Unreachable{itps[0]};
    } else if (res == SMTSolver::Answer::SAT) {
        return Reachable{};
    }
    throw std::logic_error{"Unexpected result from SMT solver"};
}

SolverAnswer::Answer RFrames::queryWithTransitionAt(std::size_t k, PTRef state) {
    ensureReadyFor(k);
    return solvers[k].checkFeasibility(state);
}

SolverAnswer::Answer FrameSolver::checkFeasibility(PTRef state) {
    solver->resetSolver();
    solver->assertProp(logic.mkAnd(lemmas));
    solver->assertProp(transition);
    solver->assertProp(state);
    auto res = solver->check();
    if (res == SMTSolver::Answer::SAT) {
        return SolverAnswer::Feasible{solver->getModel()};
    } else if (res == SMTSolver::Answer::UNSAT) {
        auto itpContext = solver->getInterpolationContext();
        vec<PTRef> itps;
        int mask = 3;
        itpContext->getSingleInterpolant(itps, mask);
        assert(itps.size() == 1);
        return SolverAnswer::Infeasible{itps[0]};
    }
    throw std::logic_error{"Unexpected result from SMT solver"};

}

void FrameSolver::addLemma(PTRef lemma) {
    lemmas.push(lemma);
}




/**
 * Recursively checks if formula is reachable in k steps from initial states by updating and using the reachability frame.
 * @param k number of steps
 * @return true if is reachable, false and interpolant if isn't
 */
ReachabilityResult ReachabilityChecker::reachable(unsigned k, PTRef formula) {
    // Check reachability from initial states in 0 steps.
    if (k == 0) {
        return zeroStepReachability(formula);
    }

    TimeMachine tm{logic};
    PTRef versioned_formula = tm.sendFlaThroughTime(formula, 1); // Send the formula through time by one, so it matches the pattern init_0 transition_0-1 formula_1.
    while (true) {
        // Check if formula is reachable from r_frames[k-1] in 1 step.
        auto answer = r_frames.queryWithTransitionAt(k-1, versioned_formula);

        // If is reachable, create a generalization of such states and check if they are reachable in k-1 steps.
        if (std::holds_alternative<SolverAnswer::Feasible>(answer)) {
            PTRef g = generalize(logic, *std::get<SolverAnswer::Feasible>(answer).model, system.getStateVars(),system.getTransition(), versioned_formula);
            auto reach_res = reachable(k-1, g);
            // If is reachable return true, else update the reachability frame.
            if (std::holds_alternative<Reachable>(reach_res)) {
                return reach_res;
            } else {
                PTRef explanation = std::get<Unreachable>(reach_res).explanation;
                r_frames.addLemma(k-1, explanation);
            }
        } else {
            assert(std::holds_alternative<SolverAnswer::Infeasible>(answer));
            PTRef interpolant = std::get<SolverAnswer::Infeasible>(answer).interpolant;
            PTRef lemma = tm.sendFlaThroughTime(interpolant, -1);

            auto zeroStepRes = zeroStepReachability(formula);
            assert(std::holds_alternative<Unreachable>(zeroStepRes));
            return Unreachable{logic.mkOr(lemma, std::get<Unreachable>(zeroStepRes).explanation)};
        }
    }
}

/**
 * Checks if formula is reachable in k_from to k_to steps.
 * @param from    least number of steps
 * @param to      max number of steps
 * @param formula   tested formula
 * @return number of steps if reachable, explanation if unreachable
 */
ReachabilityResult ReachabilityChecker::checkReachability(unsigned const from, unsigned const to, PTRef formula) {
    assert(from <= to);
    for (unsigned i = from; i <= to; i++) {
        auto reach_res = reachable(i, formula);
        if (std::holds_alternative<Reachable>(reach_res)) {
            return Reachable{i};
        }
        if (i == to) {
            assert(std::holds_alternative<Unreachable>(reach_res));
            return reach_res;
        }
    }
    assert(false);
    throw std::logic_error("Unreachable!");
}