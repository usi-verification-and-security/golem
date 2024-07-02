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
            return this -> lemma == other.lemma && this -> counter_example.ctx == other.counter_example.ctx;
        }

        bool operator<(IFrameElement const & other) const {
            if (this -> lemma == other.lemma) {
                return this -> counter_example.ctx < other.counter_example.ctx;
            } else {
                return this -> lemma < other.lemma;
            }
        }
};

/**
 * Comparator for Induction Frame elemtents.
 */
struct IFrameElementCompare {
        bool operator()(const IFrameElement &a, const IFrameElement &b) const {
            if (a.lemma == b.lemma) {
                return a.counter_example.ctx < b.counter_example.ctx;
            } else {
                return a.lemma < b.lemma;
            }
        }
};

/**
 * Wrapper for Induction Frame set.
 */
struct InductionFrame {
private:
    std::set<IFrameElement, IFrameElementCompare> elements;

public:
    InductionFrame() = default;

    InductionFrame(const InductionFrame& other) : elements(other.elements) {}

    InductionFrame(InductionFrame&& other) noexcept : elements(std::move(other.elements)) {}

    InductionFrame& operator=(const InductionFrame& other) {
        if (this != &other) {
            elements = other.elements;
        }
        return *this;
    }

    InductionFrame& operator=(InductionFrame&& other) noexcept {
        if (this != &other) {
            elements = std::move(other.elements);
        }
        return *this;
    }

    bool operator==(const InductionFrame& other) {
        return elements == other.elements;
    }

    ~InductionFrame() = default;

    using iterator = std::set<IFrameElement, IFrameElementCompare>::iterator;
    using const_iterator = std::set<IFrameElement, IFrameElementCompare>::const_iterator;

    iterator begin() { return elements.begin(); }
    const_iterator begin() const { return elements.begin(); }
    const_iterator cbegin() const { return elements.cbegin(); }

    iterator end() { return elements.end(); }
    const_iterator end() const { return elements.end(); }
    const_iterator cend() const { return elements.cend(); }

    std::pair<iterator, bool> insert(const IFrameElement& element) {
        return elements.insert(element);
    }

    size_t erase(const IFrameElement& element) {
        return elements.erase(element);
    }

    iterator find(const IFrameElement& element) {
        return elements.find(element);
    }
    const_iterator find(const IFrameElement& element) const {
        return elements.find(element);
    }

    void clear() {
        elements.clear();
    }

    size_t size() const {
        return elements.size();
    }

    bool empty() const {
        return elements.empty();
    }
};

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
class RFrame {
    std::vector<PTRef> r;
    Logic & logic;
public:
    RFrame(Logic & logic) : logic(logic) {}

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
    RFrame r_frame;
    Logic & logic;
    TransitionSystem const & system;
    std::tuple<bool, PTRef> reachable (unsigned k, PTRef formula);
public:
    ReachabilityChecker(Logic & logic, TransitionSystem const & system) : r_frame(logic), logic(logic), system(system) {}
    std::tuple<bool, int, PTRef> checkReachability (int from, int to, PTRef formula);
    PTRef generalize(Model & model, PTRef transition, PTRef formula);
};

/**
 * Uses PDKind algorithm to solve a transition system.
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
        VerificationResult solveTransitionSystem(TransitionSystem const & system);
};

#endif // GOLEM_PDKIND_H