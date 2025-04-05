/*
 * Copyright (c) 2024-2025, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "DAR.h"

#include "Common.h"
#include "TransformationUtils.h"

#include "utils/SmtSolver.h"

namespace golem {
class DualApproximatedReachability {
public:
    explicit DualApproximatedReachability(TransitionSystem const & ts)
        : ts(ts), forward{ts.getInit()}, backward{ts.getQuery()} {}

    TransitionSystemVerificationResult run();

private:
    using Sequence = std::vector<PTRef>;

    bool localStrengthen();

    bool globalStrengthen();

    std::optional<PTRef> fixpoint() const;

    void iterativeLocalStrengthening(std::size_t forwardIndex);

    PTRef interpolateForward(std::size_t forwardIndex);

    PTRef interpolateBackward(std::size_t backwardIndex);

    SMTSolver::Answer checkSat(PTRef fla) const;

    [[nodiscard]] Logic & logic() const { return ts.getLogic(); }

    TransitionSystem const & ts;
    Sequence forward{};
    Sequence backward{};
    std::size_t n{0};

    void showSequences() const;
};

TransitionSystemVerificationResult DAR::solve(TransitionSystem const & system) {
    { // Check satisfiability of Init /\ Query
        SMTSolver solver(logic, SMTSolver::WitnessProduction::NONE);
        solver.assertProp(system.getInit());
        solver.assertProp(system.getQuery());
        if (solver.check() == SMTSolver::Answer::SAT) {
            return TransitionSystemVerificationResult{VerificationAnswer::UNSAFE, 0u};
        }
    }
    return DualApproximatedReachability(system).run();
}

TransitionSystemVerificationResult DualApproximatedReachability::run() {
    assert(n == 0 and forward.size() == 1 and backward.size() == 1);
    // Handle first iteration specially
    {
        TimeMachine tm(logic());
        SMTSolver solver(logic(), SMTSolver::WitnessProduction::ONLY_INTERPOLANTS);
        solver.assertProp(ts.getInit());
        solver.assertProp(ts.getTransition());
        solver.assertProp(tm.sendFlaThroughTime(ts.getQuery(), 1));
        auto res = solver.check();
        if (res == SMTSolver::Answer::SAT) {
            return TransitionSystemVerificationResult{VerificationAnswer::UNSAFE, 1u};
        }
        if (res != SMTSolver::Answer::UNSAT) {
            return TransitionSystemVerificationResult{VerificationAnswer::UNKNOWN, 0u};
        }
        vec<PTRef> itps;
        auto itpContext = solver.getInterpolationContext();
        itpContext->getSingleInterpolant(itps, 3);
        itpContext->getSingleInterpolant(itps, 6);
        assert(itps.size() == 2);
        forward.push_back(tm.sendFlaThroughTime(itps[0], -1));
        backward.push_back(itps[1]);
        ++n;
    }
    while (true) {
        // std:: cout << "Step " << n << std::endl;
        // showSequences();
        if (localStrengthen() == false) {
            if (globalStrengthen() == false) {
                return TransitionSystemVerificationResult{VerificationAnswer::UNSAFE, n + 1};
            }
        }
        ++n;
        auto maybeInvariant = fixpoint();
        if (maybeInvariant) {
            return TransitionSystemVerificationResult{VerificationAnswer::SAFE, maybeInvariant.value()};
        }
    }
}

bool DualApproximatedReachability::localStrengthen() {
    assert(forward.size() == backward.size());
    assert(forward.size() == n + 1);
    Logic & logic = ts.getLogic();
    // Find a pair F_i, B_j (j = n - i) are not connected by one step, iterate backwards
    auto maybeIndex = [&]() -> std::optional<std::size_t> {
        for (std::size_t j = 0; j < n; ++j) {
            auto i = n - j;
            auto res = checkSat(
                logic.mkAnd({forward[i], ts.getTransition(), TimeMachine(logic).sendFlaThroughTime(backward[j], 1)}));
            if (res == SMTSolver::Answer::UNSAT) { return i; }
        }
        return std::nullopt;
    }();
    if (not maybeIndex) { return false; }
    iterativeLocalStrengthening(maybeIndex.value());
    return true;
}

void DualApproximatedReachability::iterativeLocalStrengthening(std::size_t forwardIndex) {
    std::size_t backwardIndex = n - forwardIndex;
    TimeMachine tm(logic());
    while (forwardIndex < n) {
        PTRef itp = interpolateForward(forwardIndex);
        itp = tm.sendFlaThroughTime(itp, -1);
        forward[forwardIndex + 1] = logic().mkAnd(forward[forwardIndex + 1], itp);
        ++forwardIndex;
    }
    PTRef newStep = interpolateForward(n);
    forward.push_back(tm.sendFlaThroughTime(newStep, -1));
    while (backwardIndex < n) {
        PTRef itp = interpolateBackward(backwardIndex);
        backward[backwardIndex + 1] = logic().mkAnd(backward[backwardIndex + 1], itp);
        ++backwardIndex;
    }
    backward.push_back(interpolateBackward(n));
}

bool DualApproximatedReachability::globalStrengthen() {
    if (n == 0) return false;
    TimeMachine tm(logic());
    SMTSolver solver(logic(), SMTSolver::WitnessProduction::ONLY_INTERPOLANTS);
    solver.assertProp(ts.getInit());
    solver.assertProp(ts.getTransition());
    solver.assertProp(tm.sendFlaThroughTime(ts.getTransition(), 1));
    for (std::size_t i = 2; i <= n + 1; ++i) {
        solver.push();
        auto j = (n - i) + 1;
        assert(backward.size() > j);
        solver.assertProp(tm.sendFlaThroughTime(backward[j], i));
        auto res = solver.check();
        if (res == SMTSolver::Answer::UNSAT) {
            // Compute interpolation sequence and strengthen Forward
            auto itpContext = solver.getInterpolationContext();
            std::vector<ipartitions_t> partitions;
            ipartitions_t mask = 3; // First two formulas
            partitions.push_back(mask);
            for (std::size_t idx = 1; idx < i; ++idx) {
                auto bitIndex = idx * 2;
                opensmt::setbit(mask, bitIndex);
                partitions.push_back(mask);
            }
            if (i == n + 1) { partitions.pop_back(); }
            vec<PTRef> itps;
            itpContext->getPathInterpolants(itps, partitions);
            for (int idx = 0; idx < itps.size(); ++idx) {
                auto forwardIndex = idx + 1;
                assert(static_cast<std::size_t>(forwardIndex) < forward.size());
                forward[forwardIndex] = logic().mkAnd(
                    forward[forwardIndex], TimeMachine(logic()).sendFlaThroughTime(itps[idx], -forwardIndex));
            }
            iterativeLocalStrengthening(i - 1);
            return true;
        }
        solver.pop();
        solver.assertProp(tm.sendFlaThroughTime(ts.getTransition(), i));
    }
    return false;
}

PTRef DualApproximatedReachability::interpolateForward(std::size_t forwardIndex) {
    TimeMachine tm(logic());
    SMTSolver solver(logic(), SMTSolver::WitnessProduction::ONLY_INTERPOLANTS);
    auto backwardIndex = n - forwardIndex;
    assert(forwardIndex < forward.size());
    assert(backwardIndex < backward.size());
    solver.assertProp(forward[forwardIndex]);
    solver.assertProp(ts.getTransition());
    solver.assertProp(tm.sendFlaThroughTime(backward[backwardIndex], 1));
    auto res = solver.check();
    if (res != SMTSolver::Answer::UNSAT) { throw std::logic_error("DAR: Cannot interpolate if query is not UNSAT!"); }
    auto itpContex = solver.getInterpolationContext();
    ipartitions_t mask = 3; // F + Tr
    vec<PTRef> itps;
    itpContex->getSingleInterpolant(itps, mask);
    assert(itps.size() == 1);
    return itps[0];
}

PTRef DualApproximatedReachability::interpolateBackward(std::size_t backwardIndex) {
    TimeMachine tm(logic());
    SMTSolver solver(logic(), SMTSolver::WitnessProduction::ONLY_INTERPOLANTS);
    auto forwardIndex = n - backwardIndex;
    assert(forwardIndex < forward.size());
    assert(backwardIndex < backward.size());
    solver.assertProp(forward[forwardIndex]);
    solver.assertProp(ts.getTransition());
    solver.assertProp(tm.sendFlaThroughTime(backward[backwardIndex], 1));
    auto res = solver.check();
    if (res != SMTSolver::Answer::UNSAT) { throw std::logic_error("DAR: Cannot interpolate if query is not UNSAT!"); }
    auto itpContex = solver.getInterpolationContext();
    ipartitions_t mask = 6; // Tr + B
    vec<PTRef> itps;
    itpContex->getSingleInterpolant(itps, mask);
    assert(itps.size() == 1);
    return itps[0];
}

SMTSolver::Answer DualApproximatedReachability::checkSat(PTRef fla) const {
    SMTSolver solver(logic(), SMTSolver::WitnessProduction::NONE);
    solver.assertProp(fla);
    return solver.check();
}

std::optional<PTRef> DualApproximatedReachability::fixpoint() const {
    auto checkSequence = [&](Sequence const & seq) -> std::optional<std::size_t> {
        for (std::size_t i = 1; i < seq.size(); ++i) {
            auto candidate = seq[i];
            vec<PTRef> previous;
            for (std::size_t j = 0; j < i; ++j) {
                previous.push(seq[j]);
            }
            PTRef disj = logic().mkOr(std::move(previous));
            auto res = checkSat(logic().mkAnd(candidate, logic().mkNot(disj)));
            if (res == SMTSolver::Answer::UNSAT) { return i; }
        }
        return std::nullopt;
    };
    auto maybeForwardFixpointIndex = checkSequence(forward);
    if (maybeForwardFixpointIndex) {
        vec<PTRef> previous;
        for (std::size_t j = 0; j < maybeForwardFixpointIndex.value(); ++j) {
            previous.push(forward[j]);
        }
        PTRef disj = logic().mkOr(std::move(previous));
        // std::cout << "Invariant from forward sequence " << logic().pp(disj) << std::endl;
        return disj;
    }
    auto maybeBackwardFixpointIndex = checkSequence(backward);
    if (maybeBackwardFixpointIndex) {
        vec<PTRef> previous;
        for (std::size_t j = 0; j < maybeBackwardFixpointIndex.value(); ++j) {
            previous.push(backward[j]);
        }
        PTRef disj = logic().mkOr(std::move(previous));
        // std::cout << "Invariant from bacward sequence " << logic().pp(logic().mkNot(disj)) << std::endl;
        return logic().mkNot(disj);
    }
    return std::nullopt;
}

[[maybe_unused]] void DualApproximatedReachability::showSequences() const {
    std::cout << "Forward sequence has " << forward.size() << " elements\n";
    for (PTRef el : forward) {
        std::cout << logic().pp(el) << '\n';
    }
    std::cout << '\n';
    std::cout << "Backward sequence has " << backward.size() << " elements\n";
    for (PTRef el : backward) {
        std::cout << logic().pp(el) << '\n';
    }
}
} // namespace golem
