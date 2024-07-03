/*
* Copyright (c) 2023-2024, Stepan Henrych <stepan.henrych@gmail.com>
*
* SPDX-License-Identifier: MIT
*/

#ifndef GOLEM_PDKIND_H
#define GOLEM_PDKIND_H

#include "Engine.h"
#include "MainSolver.h"
#include "PTRef.h"
#include "TransitionSystem.h"
#include <memory>
#include <set>
#include <tuple>

/**
 * Counter example formula in addition with number of steps needed to reach the counter example.
 */
struct CounterExample {
    PTRef ctx;
    int num_of_steps;
    CounterExample(PTRef ctx) : ctx(ctx), num_of_steps(0) {}
    CounterExample(PTRef ctx, int num_of_steps) : ctx(ctx), num_of_steps(num_of_steps) {}
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
 * Comparator for Induction Frame elemtents.
 */
struct IFrameElementCompare {
        bool operator()(const IFrameElement &a, const IFrameElement &b) const {
            return a < b;
        }
};

/**
 * Wrapper for Induction Frame set.
 */
using InductionFrame = std::set<IFrameElement, IFrameElementCompare>;

/**
 * Wrapper for return value of the Push function.
 */
struct PushResult {
    InductionFrame i_frame;
    InductionFrame new_i_frame;
    int n;
    bool is_invalid;
    int steps_to_ctx;
    PushResult(InductionFrame i_frame,
               InductionFrame new_i_frame,
               int n,
               bool is_invalid,
               int steps_to_ctx) : i_frame(std::move(i_frame)), new_i_frame(std::move(new_i_frame)), n(n), is_invalid(is_invalid), steps_to_ctx(steps_to_ctx) {}
};

/**
 * A data structure where r[i] represents the states that are reachable in i steps from some initial states, i.e., r[0].
 */
class RFrames {
    std::vector<PTRef> r;
    Logic & logic;
public:
    RFrames(Logic & logic) : logic(logic) {}

    const PTRef & operator[] (size_t i) {
        if (i >= r.size()) {
            while (r.size() <= i) {
                r.push_back(logic.getTerm_true());
            }
        }
        return r[i];
    }

    void insert(PTRef fla, size_t k) {
        if (k >= r.size()) {
            while (r.size() <= k) {
                r.push_back(logic.getTerm_true());
            }
        }
        PTRef new_fla = logic.mkAnd(r[k], fla);
        r[k] = new_fla;
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
    std::tuple<bool, PTRef> reachable(unsigned k, PTRef formula);
public:
    ReachabilityChecker(Logic & logic, TransitionSystem const & system) : r_frames(logic), logic(logic), system(system) {}
    std::tuple<bool, int, PTRef> checkReachability(int from, int to, PTRef formula);
    PTRef generalize(Model & model, PTRef transition, PTRef formula);
};

/**
 * Uses PDKind algorithm [1] to solve a transition system.
 *
 * [1] https://ieeexplore.ieee.org/document/7886665
 */
class PDKind : public Engine {
        Logic & logic;
        bool computeWitness {false};
    public:

        PDKind (Logic & logic, Options const & options) : logic(logic) {
            if (options.hasOption(Options::COMPUTE_WITNESS)) {
                computeWitness = options.getOption(Options::COMPUTE_WITNESS) == "true";
            }
        }

        virtual VerificationResult solve(ChcDirectedHyperGraph const & graph) override;

        VerificationResult solve(ChcDirectedGraph const & system);

    private:
        PushResult push(TransitionSystem const & system, InductionFrame & iframe, int n, int k, ReachabilityChecker & reachability_checker);
        TransitionSystemVerificationResult solveTransitionSystem(TransitionSystem const & system);
        PTRef getInvariant(InductionFrame const & iframe, unsigned int k, TransitionSystem const & system);
};

#endif // GOLEM_PDKIND_H