/*
 * Copyright (c) 2021-2023, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "TPABase.hh"

#include "Common.h"
#include "ModelBasedProjection.h"
#include "QuantifierElimination.h"
#include "TermUtils.h"
#include "TransformationUtils.h"
#include "TransitionSystem.h"
#include "Witnesses.h"
#include "common/TreeOps.h"
#include "pterms/PTRef.h"
#include "unsatcores/UnsatCore.h"
#include "utils/SmtSolver.h"

#include "utils/ConvexClosure.h"

#include <algorithm>
#include <chrono>
#include <limits>
#include <optional>
#include <queue>
#include <vector>

namespace golem {

namespace {
/// Can `target` be reached from `source` (state formulas) in <=2^{level+1} steps?
/// A first half remembers in `next` the target of the pob it splits: once its own target is reached,
/// it is replaced by the second half, from the reached states to `next`.
/// A may-POB is a first half without `next`: once reachable it is simply removed; once blocked, its lemma
/// is learnt as usual.
/// A relational may-POB (CC-lemma) has `relation` instead of `source` and `target`: a transition formula over
/// (x, x'), the pairs to block from being connected in <=2^{level+1} steps. It is not split: once blocked,
/// its lemma is learnt; otherwise it is removed, and nothing is cached, as its pairs need not start in
/// reachable states.
struct ProofObligation {
    PTRef source;
    PTRef target;
    unsigned short level;
    PTRef next = PTRef_Undef;   ///< PTRef_Undef: not a first half
    unsigned sourceSteps = 0;   ///< steps from the initial states to `source`
    bool isMayPO = false;
    /// may-POBs only: the family, i.e. a may-POB built by a must pob and every pob below it, may-POBs built
    /// by its may-POBs included. The family shares one gas counter and is closed as a whole
    /// (TPABasic::reachabilityQuery). 0 for must pobs.
    std::size_t family = 0;
    PTRef relation = PTRef_Undef; ///< relational may-POBs only; then `source` and `target` are undefined
    PTRef parentTarget = PTRef_Undef; ///< target of the pob that created this one; its lemma goes there (CC-lemma)
    /// For a CC root only: the target and level whose midpoints (CC-pob) or blocking lemmas (CC-lemma) its
    /// hull was built from (cc-update). Keys, not a reference: the per-level vectors of TPAPobInfo may grow.
    struct CcOrigin {
        PTRef creatorTarget;
        unsigned short creatorLevel;
        bool fromLemmas;
    };
    std::optional<CcOrigin> ccOrigin;
    std::size_t id = 0;         ///< creation order, set by PriorityQueue::push
};

bool operator>(ProofObligation const & pob1, ProofObligation const & pob2) {
    // lower levels first; at the same level may-POBs first, as in Spacer; then the newest pob first
    if (pob1.level != pob2.level) { return pob1.level > pob2.level; }
    if (pob1.isMayPO != pob2.isMayPO) { return pob2.isMayPO; }
    return pob1.id < pob2.id;
}

struct PriorityQueue {

    void push(ProofObligation pob) {
        pob.id = counter++;
        pqueue.push(pob);
    }
    ProofObligation const & peek() const { return pqueue.top(); }
    void pop() { pqueue.pop(); }
    [[nodiscard]] bool empty() const { return pqueue.empty(); }

private:
    std::size_t counter = 0;
    std::priority_queue<ProofObligation, std::vector<ProofObligation>, std::greater<>> pqueue;
};
} // namespace

bool TPABasic::checkLemma(unsigned short power, PTRef lemma01, bool inductive) const {
    SMTSolver solver(logic, SMTSolver::WitnessProduction::NONE);
    PTRef AT01 = getLevelTransition(power);
    PTRef AT12 = getNextVersion(AT01);
    PTRef lemma12 = getNextVersion(lemma01);
    PTRef lemma02 = shiftOnlyNextVars(lemma01);

    bool ok = true;

    // Check: T -> AT
    solver.push();
    solver.assertProp(logic.mkOr(transition, identity));
    solver.assertProp(logic.mkNot(AT01));
    if (solver.check() != SMTSolver::Answer::UNSAT) {
        std::cerr << "AT is not implied by T!" << std::endl;
        ok = false;
    }
    solver.pop();

    // Check: T -> lemma
    solver.push();
    solver.assertProp(logic.mkOr(transition, identity));
    solver.assertProp(logic.mkNot(lemma01));
    if (solver.check() != SMTSolver::Answer::UNSAT) {
        std::cerr << "Lemma is not implied by T!" << std::endl;
        ok = false;
    }
    solver.pop();

    if (not inductive) {
        // Check (A01 & A12) -> lemma02 
        solver.push();
        solver.assertProp(AT01);
        solver.assertProp(AT12);
        solver.assertProp(logic.mkNot(lemma02));
        if (solver.check() != SMTSolver::Answer::UNSAT) {
            std::cerr << "Lemma is not implied by previous frames" << std::endl;
            ok = false;
        }
        solver.pop();
    } else {
        // Check (A01 & lemma01 & A12 & lemma12) -> lemma02 
        solver.push();
        solver.assertProp(AT01);
        solver.assertProp(AT12);
        solver.assertProp(lemma01);
        solver.assertProp(lemma12);
        solver.assertProp(logic.mkNot(lemma02));
        if (solver.check() != SMTSolver::Answer::UNSAT) {
            std::cerr << "Lemma is not inductive from by previous frames" << std::endl;
            ok = false;
        }
        solver.pop();
    }

    return ok;
}

/// tau(x, x''): the identity or one step of the exact transition relation, from x to x''.
/// Unlike shiftOnlyNextVars, which requires a pure transition formula, this leaves the auxiliary
/// variables of the transition in place: they are existentially quantified within this disjunct.
PTRef TPABasic::generalizationBase() const {
    auto nextVars = getStateVars(1);
    auto nextnextVars = getStateVars(2);
    TermUtils::substitutions_map subst;
    for (int i = 0; i < nextVars.size(); ++i) {
        subst.insert({nextVars[i], nextnextVars[i]});
    }
    return TermUtils(logic).varSubstitute(logic.mkOr(identity, transition), subst);
}

PTRef TPABasic::generalize(unsigned short power, PTRef lemma) const {
    const auto& candidates = TermUtils(logic).getTopLevelDisjuncts(lemma);
    // The core is never empty, so a single disjunct is its own generalization
    if (candidates.size() < 2) { return lemma; }

    SMTSolver solver(logic, SMTSolver::WitnessProduction::ONLY_UNSAT_CORE);
    vec<PTRef> assumedSources1, assumedSources2, assumedTargets;
    std::map<PTRef, PTRef> mapping;
    assumedSources1.capacity(candidates.size());
    assumedSources2.capacity(candidates.size());
    assumedTargets.capacity(candidates.size());

    /*
      bigand_i a_i     // named assumptions
      & (
         T(x, x'')     // base
         or
         (             // inductive step
           TA^n(x, x') & TA^n(x', x'')
           & bigor_i(a_i & l_i(x, x')) & // assumed sources 1
           & bigor_i(a_i & l_i(x', x'')) // assumed sources 2
         )
        )
      & bigand_i (a_i -> not l_i(x, x''))
                      // assumed targets
     */
    static std::size_t i = 0;
    for (const auto candidate : candidates) {
        std::string name = "_assume#indgen#" + std::to_string(i++);
        PTRef assumption = logic.mkBoolVar(name.c_str());
        mapping[assumption] = candidate;
        PTRef source1 = logic.mkAnd(assumption, candidate);
        PTRef source2 = logic.mkAnd(assumption, getNextVersion(candidate));
        assumedSources1.push(source1);
        assumedSources2.push(source2);
        PTRef notTarget = logic.mkNot(shiftOnlyNextVars(candidate));
        assumedTargets.push(logic.mkImpl(assumption, notTarget));

        // assert assumptions
        bool added = solver.tryAssertNamedProp(assumption, name);
        assert(added);
    }

    PTRef absTrans = getLevelTransition(power);
    PTRef twoSteps = logic.mkAnd(absTrans, getNextVersion(absTrans));
    PTRef inductiveStep = \
        logic.mkAnd({
                twoSteps,
                logic.mkOr(assumedSources1),
                logic.mkOr(assumedSources2)
            });
    PTRef baseOrindStep = \
        logic.mkOr(generalizationBase(), inductiveStep);
    solver.assertProp(baseOrindStep);

    PTRef target = logic.mkAnd(assumedTargets);
    solver.assertProp(target);

    auto res = solver.check();
    if (res != SMTSolver::Answer::UNSAT) {
        throw std::logic_error("Error in Generalize: formula is not unsatisfiable!");
    }

    auto core = solver.getUnsatCore();
    vec<PTRef> inductiveDisjs;
    const auto& coreAssumptions = core->getTerms();
    for (auto term : coreAssumptions) { inductiveDisjs.push(mapping[term]); }
    assert(inductiveDisjs.size() > 0);
    auto newLemma = logic.mkOr(inductiveDisjs);

    TRACE(3, "==== [GENERALIZE] Old Lemma: " << logic.pp(lemma));
    TRACE(3, "==== [GENERALIZE] New Lemma: " << logic.pp(newLemma));

    if (cfg.debug) { checkGeneralization(power, lemma, newLemma, "generalize"); }

    return newLemma;
}

PTRef TPABasic::generalize_down(unsigned short power, PTRef lemma) const {
    const auto& candidates = TermUtils(logic).getTopLevelDisjuncts(lemma);
    if (candidates.size() < 2) { return lemma; }
    const int n = candidates.size();

    // Declare assumptions. do not assert them yet.
    static std::size_t freshId = 0;
    std::vector<PTRef> selectors;
    selectors.reserve(n);
    for (int i = 0; i < n; ++i) {
        std::string name = "_assume#gdown#" + std::to_string(freshId++);
        selectors.push_back(logic.mkBoolVar(name.c_str()));
    }

    vec<PTRef> assumedSources1, assumedSources2, assumedTargets;
    assumedSources1.capacity(n);
    assumedSources2.capacity(n);
    assumedTargets.capacity(n);
    for (int i = 0; i < n; ++i) {
        assumedSources1.push(logic.mkAnd(selectors[i], candidates[i]));
        assumedSources2.push(logic.mkAnd(selectors[i], getNextVersion(candidates[i])));
        assumedTargets.push(logic.mkImpl(selectors[i], logic.mkNot(shiftOnlyNextVars(candidates[i]))));
    }
    PTRef base = generalizationBase();
    PTRef hypothesis = logic.mkAnd(logic.mkOr(assumedSources1), logic.mkOr(assumedSources2));
    PTRef target = logic.mkAnd(assumedTargets);
    PTRef absTrans = getLevelTransition(power);
    PTRef twoSteps = logic.mkAnd(absTrans, getNextVersion(absTrans));

    // baseline, without asserting assumption literals:
    // tau(x, x'') or (T(x, x') and T(x', x'') and lemma(x, x') and lemma(x', x'')), not lemma(x, x'')
    SMTSolver solver(logic, SMTSolver::WitnessProduction::NONE);
    solver.assertProp(logic.mkOr(base, logic.mkAnd(twoSteps, hypothesis)));
    solver.assertProp(target);

    // Is the lemma restricted to `keep` unreachable in `s`, i.e. inductive?
    auto inductiveFor = [&](SMTSolver & s, std::vector<bool> const & keep) {
        s.push();
        for (int i = 0; i < n; ++i) {
            s.assertProp(keep[i] ? selectors[i] : logic.mkNot(selectors[i]));
        }
        auto res = s.check();
        s.pop();
        return res == SMTSolver::Answer::UNSAT;
    };
    auto singleton = [n](int lit) {
        std::vector<bool> keep(n, false);
        keep[lit] = true;
        return keep;
    };

    // Check which literals are inductive on their own.
    std::vector<bool> preserved(n, false);
    for (int i = 0; i < n; ++i) {
        preserved[i] = inductiveFor(solver, singleton(i));
    }

    // A literal that is inductive on its own is already the best the down pass can reach: dropping
    // disjuncts only strengthens the clause. The greedy pass below can miss it, so keep it directly.
    // Among several, prefer one inductive without the level transition: tau(x, x'') implies it and
    // it is transitive, so it holds at every level, e.g. x' >= x rather than the level-local x' <= x + 3.
    // (Replacing T by tau(x, x') and tau(x', x'') would not discriminate: tau implies T, so every
    // literal inductive on its own passes.)
    std::optional<SMTSolver> frameless;
    int alone = -1;
    bool aloneTransitive = false;
    for (int i = 0; i < n and not aloneTransitive; ++i) {
        if (not preserved[i]) { continue; }
        if (alone < 0) {
            alone = i;
            continue;
        }
        // A tie: check whether this literal or the current one is transitive
        if (not frameless) {
            frameless.emplace(logic, SMTSolver::WitnessProduction::NONE);
            frameless->assertProp(logic.mkOr(base, hypothesis));
            frameless->assertProp(target);
            if (inductiveFor(*frameless, singleton(alone))) {
                aloneTransitive = true;
                break;
            }
        }
        if (inductiveFor(*frameless, singleton(i))) {
            alone = i;
            aloneTransitive = true;
        }
    }

    std::vector<bool> keep(n, true);
    int kept = n;
    if (alone >= 0) {
        std::fill(keep.begin(), keep.end(), false);
        keep[alone] = true;
        kept = 1;
        TRACE(2, "---- [GDW] Kept the literal inductive on its own" << (aloneTransitive ? " (transitive)" : ""));
    } else {
        // Sort the literals prioritizing the ones that are *not* inductive
        std::vector<int> order(n);
        for (int i = 0; i < n; ++i) { order[i] = i; }
        std::stable_sort(order.begin(), order.end(),
                         [&](int a, int b) { return not preserved[a] and preserved[b]; });

        // Down pass, with `order` sorting
        for (int i : order) {
            // try to delete `i`
            keep[i] = false;
            if (inductiveFor(solver, keep)) {
                --kept;
            } else {
                // if `i` cannot be removed without breaking induction, then restore it
                keep[i] = true;
            }
        }
    }
    // tau(x, x'') is satisfiable, so the empty clause is never inductive
    assert(kept > 0);

    vec<PTRef> inductiveDisjs;
    inductiveDisjs.capacity(kept);
    for (int i = 0; i < n; ++i) {
        if (keep[i]) { inductiveDisjs.push(candidates[i]); }
    }
    PTRef newLemma = logic.mkOr(inductiveDisjs);

    TRACE(3, "==== [GDW] Old Lemma: " << logic.pp(lemma));
    TRACE(3, "==== [GDW] New Lemma: " << logic.pp(newLemma));

    if (cfg.debug) { checkGeneralization(power, lemma, newLemma, "generalize_down"); }

    return newLemma;
}

void TPABasic::checkGeneralization(unsigned short power, PTRef lemma, PTRef newLemma, std::string const & where) const {
    SMTSolver debugSolver(logic, SMTSolver::WitnessProduction::NONE);
    debugSolver.assertProp(logic.mkNot(shiftOnlyNextVars(newLemma)));

    // newLemma keeps a subset of the disjuncts, so it implies lemma: is it strictly stronger?
    debugSolver.push();
    debugSolver.assertProp(shiftOnlyNextVars(lemma));
    if (debugSolver.check() != SMTSolver::Answer::UNSAT) {
        TRACE(2, "Generalization applied: newLemma is stronger!");
    }
    debugSolver.pop();

    if (not checkLemma(power, newLemma, true)) {
        throw std::logic_error("Error in " + where + ": newLemma is not inductive!");
    }

    // Is newLemma implied by two steps of the level transition alone, or did it need induction?
    PTRef absTrans = getLevelTransition(power);
    debugSolver.assertProp(logic.mkAnd(absTrans, getNextVersion(absTrans)));
    if (debugSolver.check() != SMTSolver::Answer::UNSAT) {
        TRACE(2, "Inductive-generalization applied: newLemma is stronger than min-gen!");
    }
}

// Single hierarchy version:
TPABasic::~TPABasic() {
    clearReachabilitySolvers();
}

void TPABasic::clearReachabilitySolvers() {
    for (SolverWrapper * solver : reachabilitySolvers) {
        delete solver;
    }
    reachabilitySolvers.clear(true);
}

PTRef TPABasic::getLevelTransition(unsigned short power) const {
    assert(power < transitionHierarchy.size());
    return logic.mkAnd(transitionHierarchy[power]);
}

void TPABasic::storeLevelTransition(unsigned short power, PTRef tr) {
    TRACE(3, "Strengthening level " << power << " with " << logic.printTerm(tr));
    if (power != 0 and not isPureTransitionFormula(tr)) {
        throw std::logic_error("Transition relation has some auxiliary variables!");
    }
    for (auto i = transitionHierarchy.size(); i <= power; ++i) {
        transitionHierarchy.push_back({});
    }

    vec<PTRef> allTr = TermUtils(logic).getTopLevelConjuncts(tr);

    for (auto i = 0; i <= power; ++i) {
        auto& level = transitionHierarchy[i];
        for (auto t : allTr) {
            if (std::find(level.begin(), level.end(), t) == level.end()) {
                TRACE(2, "[+] Adding " << t.x << " in TA " << i);
                transitionHierarchy[i].push(t);
            } else {
                TRACE(4, "   Trying to add the same lemma again. Skipping...");
                // TODO: skip also asserting in the solver.
            }
        }
    }

    reachabilitySolvers.growTo(power + 2, nullptr);
    PTRef nextLevelTransitionStrengthening = logic.mkAnd(tr, getNextVersion(tr));
    for (auto i = 1; i <= power + 1; ++i) {
        if (not reachabilitySolvers[i]) {
            reachabilitySolvers[i] =
                new SolverWrapperIncrementalWithRestarts(logic, nextLevelTransitionStrengthening);
            //        reachabilitySolvers[power + 1] = new SolverWrapperIncremental(logic,
            //        nextLevelTransitionStrengthening); reachabilitySolvers[power + 1] = new SolverWrapperSingleUse(logic,
            //        nextLevelTransitionStrengthening);
        } else {
            reachabilitySolvers[i]->strengthenTransition(nextLevelTransitionStrengthening);
        }
    }
}

SolverWrapper * TPABasic::getReachabilitySolver(unsigned short power) const {
    assert(reachabilitySolvers.size() > power);
    return reachabilitySolvers[power];
}

VerificationAnswer TPABasic::checkPower(unsigned short power) {
    TRACE(1, "\n----------\nChecking power " << power)
    auto res = reachabilityQuery(init, query, power);
    if (isReachable(res)) {
        reachedStates = ReachedStates{res.refinedTarget, res.steps};
        return VerificationAnswer::UNSAFE;
    } else if (isUnreachable(res)) {
        if (verbose() > 0) { std::cout << "; System is safe up to <=2^" << power + 1 << " steps" << std::endl; }
        TRACE(1, "System is safe up to <=2^" << power + 1 << "steps.");
        // Check if we have not reached fixed point.
        bool fixpoint = propagateTransitions(power + 1);
        if (fixpoint) { return VerificationAnswer::SAFE; }
        bool fixedPointReached = checkLessThanFixedPoint(power + 1);
        if (fixedPointReached) { return VerificationAnswer::SAFE; }
    }
    return VerificationAnswer::UNKNOWN;
}

/*
 * Check if 'to' is reachable from 'from' (these are state formulas) in  <=2^{n+1} steps (n is 'power').
 * A proof obligation asks the same for its source and target at its level, using the level-th abstraction
 * of the transition relation for two steps.
 * If the target is unreachable, we interpolate over the 2 step transition to obtain 1-step transition of
 * level+1, and the pob is removed. If it is reachable at level 0, the truly reachable part of the target is
 * cached; otherwise the model gives a midpoint, and the first half is queued above the pob.
 * A pob whose target is cached is removed; if it is a first half, its second half takes its place.
 * With may-POBs on, the midpoints of a target and their over-approximations are collected per level in the
 * pob database; once the target was examined triggerMayPo times at a level, may-POBs from the source to their
 * conjunction (BMBP) and to their convex closure (CC-pob) are queued one level below. The lemmas that blocked
 * the children of a target are collected too; their negations are pairs, and the convex closure of them is
 * queued, kept together, as a relational may-POB (CC-lemma).
 */
TPABasic::QueryResult TPABasic::reachabilityQuery(PTRef from, PTRef to, unsigned short power) {
    TRACE(2, "[RQ] Checking LEQ reachability on level " << power << " from " << from.x << " to " << to.x)
    PriorityQueue pqueue;
    pqueue.push(ProofObligation{from, to, power});
    // The may-POB families of this query, by ProofObligation::family; 0 is the must pobs' and unused.
    // Gas is what the family may still push: every pob a may-POB pushes costs one, its first and second
    // halves and the may-POBs it builds alike. Once a visit needs a pob the family cannot pay for, the family
    // is closed, and its pobs still in the queue are dropped.
    struct MayFamily {
        std::size_t gas;
        bool closed = false;
        // For the [FAMILY] line, printed once the family's last pob has left the queue.
        char const * source = "";                   ///< of the root: BMBP, CC or CCPOB
        unsigned short rootLevel = 0;               ///< the only pob of the family at this level is the root
        std::size_t queued = 0;                     ///< pobs of the family in the queue
        std::size_t firstHalves = 0;                ///< pushed by its pobs
        std::size_t secondHalves = 0;               ///< pushed by its pobs
        std::size_t hulls = 0;                      ///< may-POBs its pobs built
        std::size_t depth = 0;                      ///< levels between the root and its deepest pob
        std::size_t visits = 0;                     ///< examinations of its pobs
        std::size_t blocked = 0;
        std::size_t reachable = 0;                  ///< a first half replaced by its second half included
        std::size_t dropped = 0;                    ///< popped unexamined because the family was closed
        char const * rootFate = "OPEN";
        std::chrono::steady_clock::duration time{}; ///< spent examining its pobs
    };
    std::vector<MayFamily> families(1, MayFamily{0});
    auto isRelational = [](ProofObligation const & p) { return p.relation != PTRef_Undef; };
    auto pobId = [&](ProofObligation const & p) { return isRelational(p) ? p.relation.x : p.target.x; };
    // One line per may-pob exit, so the fate of every may-pob is greppable.
    auto traceMayFate = [&](ProofObligation const & p, char const * fate) {
        if (not p.isMayPO) { return; }
        TRACE(1, "[MAYPO] id=" << pobId(p) << (isRelational(p) ? " rel" : "") << " family=" << p.family
              << " lvl=" << p.level << " gas=" << families[p.family].gas << " fate=" << fate);
    };
    // One line per family, the unit gas is charged to, in the format of Spacer's (with `power` for `bound`),
    // not indented. Its size counts the root: 1 + preds + hulls, where preds are the first and second halves.
    auto traceFamily = [&](std::size_t id, char const * end) {
        MayFamily const & fam = families[id];
        int const indent = TPA_INDENT;
        TPA_INDENT = 0;
        TRACE(1, "[FAMILY] power=" << power << " id=" << id << " src=" << fam.source << " lvl=" << fam.rootLevel
              << " size=" << 1 + fam.firstHalves + fam.secondHalves + fam.hulls
              << " preds=" << fam.firstHalves + fam.secondHalves << " firsts=" << fam.firstHalves
              << " seconds=" << fam.secondHalves << " hulls=" << fam.hulls << " left=" << fam.gas
              << " depth=" << fam.depth << " visits=" << fam.visits << " blocked=" << fam.blocked
              << " reachable=" << fam.reachable << " dropped=" << fam.dropped << " level0=0"
              << " root=" << fam.rootFate << " end=" << end
              << " ms=" << std::chrono::duration_cast<std::chrono::milliseconds>(fam.time).count());
        TPA_INDENT = indent;
    };
    std::chrono::steady_clock::time_point visitStart;
    // `p` has left the queue with `fate`, and whatever it pushed is queued: account for it in its family
    // (`counter`, if any, is the family's count of that fate), and trace the family once its last pob has left.
    auto leftQueue = [&](ProofObligation const & p, char const * fate, std::size_t MayFamily::* counter) {
        if (not p.isMayPO) { return; }
        MayFamily & fam = families[p.family];
        fam.time += std::chrono::steady_clock::now() - visitStart;
        if (counter) { ++(fam.*counter); }
        if (p.level == fam.rootLevel) { fam.rootFate = fate; }
        assert(fam.queued > 0);
        if (--fam.queued == 0) { traceFamily(p.family, fam.closed ? "CLOSED" : "DONE"); }
    };
    // Push a pob `creator` created: a may-POB pays one unit of its family's gas for it, counted as `kind`.
    auto pushChild = [&](ProofObligation const & creator, ProofObligation const & child,
                         std::size_t MayFamily::* kind) {
        if (child.isMayPO) {
            MayFamily & fam = families[child.family];
            if (creator.isMayPO) {
                assert(fam.gas > 0);
                --fam.gas;
                ++(fam.*kind);
            }
            ++fam.queued;
            fam.depth = std::max<std::size_t>(fam.depth, fam.rootLevel - child.level);
        }
        pqueue.push(child);
    };
    // May-POBs one level below `pob`, from what the database collected for its target: from its source to the
    // conjunction (BMBP) or the convex closure (CC-pob) of the midpoints at its level, once the target was
    // examined `triggerMayPo` times at that level; and the convex closure of the negated lemmas that blocked
    // its children (CC-lemma), once it was examined `triggerMayPo` times at any level.
    // A may-POB builds at most as many as its family's gas pays for (after its first half, pushed already); they
    // join its family. A must pob opens a new family for each may-POB it builds.
    auto buildMayPobs = [&](ProofObligation const & pob) {
        std::vector<ProofObligation> mayPobs;
        if (not cfg.maypo or isRelational(pob) or pob.level == 0) { return mayPobs; }
        std::size_t const budget = pob.isMayPO ? families[pob.family].gas : std::numeric_limits<std::size_t>::max();
        auto affordable = [&]() { return mayPobs.size() < budget; };
        TPAPobInfo & info = pobDb[pob.target];
        bool const predsReady = TPAPobInfo::atLevel(info.localCounter, pob.level) >= cfg.triggerMayPo;
        bool const lemmasReady = info.globalCounter >= cfg.triggerMayPo;
        auto mayPob = [&](PTRef mayTarget, char const * source) {
            ProofObligation mayPred{pob.source, mayTarget, static_cast<unsigned short>(pob.level - 1),
                                    PTRef_Undef, pob.sourceSteps};
            mayPred.isMayPO = true;
            if (pob.isMayPO) {
                mayPred.family = pob.family;
            } else {
                mayPred.family = families.size();
                families.push_back(MayFamily{cfg.mayPoGas});
                families.back().source = source;
                families.back().rootLevel = mayPred.level;
            }
            mayPred.parentTarget = pob.target;
            return mayPred;
        };
        if (cfg.bmbp and predsReady and affordable()) {
            // Bidirectional Model based projection
            OrderedFormulas const & overs = TPAPobInfo::atLevel(info.overPredCache, pob.level);
            if (overs.size() > 0 and overs.size() >= cfg.minBmbpOverLits) {
                vec<PTRef> approx;
                for (PTRef over : overs) { approx.push(over); }
                PTRef mayTarget = logic.mkAnd(std::move(approx));
                TRACE(1, "[BMBP] Adding the conjunction of " << overs.size() << " over-approximations: " << mayTarget.x);
                mayPobs.push_back(mayPob(mayTarget, "BMBP"));
            }
        }
        if (cfg.ccLemma and lemmasReady and affordable()) {
            // Convex Closure of the negated blocking lemmas: pairs (x, x'), kept together
            OrderedFormulas const & lemmas = info.blockingLemmas;
            if (lemmas.size() >= cfg.minLemmasForCc) {
                vec<PTRef> negatedLemmas;
                for (PTRef lemma : lemmas) { negatedLemmas.push(logic.mkNot(lemma)); }
                ConvexClosure convexClosure(logic, QEOptions(1, cfg.ccMbpBudget, true));
                PTRef hull = convexClosure.getConvexClosure(negatedLemmas);
                if (not logic.isTrue(hull) and not logic.isFalse(hull)) {
                    TRACE(1, "[CC] Adding a ConvexClosure of " << lemmas.size() << " lemmas -> atoms: "
                          << TermUtils(logic).getTopLevelConjuncts(hull).size()
                          << " vars: " << TermUtils(logic).getVars(hull).size());
                    TRACE(3, "[CC] Added " << logic.pp(hull));
                    ProofObligation mayPred = mayPob(PTRef_Undef, "CC");
                    mayPred.source = PTRef_Undef;
                    mayPred.relation = hull;
                    mayPred.ccOrigin = ProofObligation::CcOrigin{pob.target, pob.level, true};
                    mayPobs.push_back(mayPred);
                }
            }
        }
        if (cfg.ccPob and predsReady and affordable()) {
            // Convex Closure of the midpoints
            OrderedFormulas const & unders = TPAPobInfo::atLevel(info.underPredCache, pob.level);
            if (unders.size() >= cfg.minPobsForCc) {
                vec<PTRef> midPoints;
                for (PTRef under : unders) { midPoints.push(under); }
                ConvexClosure convexClosure(logic, QEOptions(1, cfg.ccMbpBudget, true));
                PTRef mayTarget = convexClosure.getConvexClosure(midPoints);
                if (not logic.isTrue(mayTarget) and not logic.isFalse(mayTarget)) {
                    TRACE(1, "[CC-POB] Adding a ConvexClosure of " << unders.size() << " midpoints -> atoms: "
                          << TermUtils(logic).getTopLevelConjuncts(mayTarget).size()
                          << " vars: " << TermUtils(logic).getVars(mayTarget).size());
                    TRACE(3, "[CC-POB] Added " << logic.pp(mayTarget));
                    mayPobs.push_back(mayPob(mayTarget, "CCPOB"));
                    mayPobs.back().ccOrigin = ProofObligation::CcOrigin{pob.target, pob.level, false};
                }
            }
        }
        return mayPobs;
    };
    // A CC root was found reachable or ran out of gas: every hull of a superset of its inputs contains this
    // one, so keep only the newest input and let the list grow again. One input is left, and both CC sources
    // need at least two, so an unchanged list stops re-creating the root.
    auto updateCcInputs = [&](ProofObligation const & root, char const * fate) {
        if (not cfg.ccUpdate or not root.ccOrigin) { return; }
        TPAPobInfo & creator = pobDb[root.ccOrigin->creatorTarget];
        OrderedFormulas & inputs = root.ccOrigin->fromLemmas
                                       ? creator.blockingLemmas
                                       : TPAPobInfo::atLevel(creator.underPredCache, root.ccOrigin->creatorLevel);
        TRACE(1, (root.ccOrigin->fromLemmas ? "[CC]" : "[CC-POB]") << " Root " << pobId(root) << " " << fate
              << ": kept the newest of " << inputs.size() << " inputs");
        inputs.keepOnlyNewest();
    };
    auto pushMayPobs = [&](ProofObligation const & creator, std::vector<ProofObligation> mayPobs) {
        for (auto & mayPred : mayPobs) {
            TRACE(1, "[+] MAY PRED: Adding new " << (isRelational(mayPred) ? "relational " : "") << "MAY PO "
                  << pobId(mayPred) << " at level " << mayPred.level << " in family " << mayPred.family);
            pushChild(creator, mayPred, &MayFamily::hulls);
        }
    };

    while (not pqueue.empty()) {
        ProofObligation const pob = pqueue.peek();
        TPA_INDENT = power - pob.level;
        visitStart = std::chrono::steady_clock::now();

        if (pob.isMayPO and families[pob.family].closed) {
            traceMayFate(pob, "CLOSED");
            updateCcInputs(pob, "EOL");
            pqueue.pop();
            leftQueue(pob, "CLOSED", &MayFamily::dropped);
            continue;
        }

        auto known = isRelational(pob) ? pobDb.end() : pobDb.find(pob.target);
        if (known != pobDb.end() and known->second.reached) {
            ReachedStates const reached = *known->second.reached;
            TRACE(2, "[C] Target " << pob.target.x << " is reachable: " << reached.reachedStates.x);
            pqueue.pop();
            if (pob.next != PTRef_Undef and pob.isMayPO and families[pob.family].gas == 0) {
                // the first half is reachable, but its family cannot pay for the second half: close it
                TRACE(1, "    Removing MayPO family " << pob.family << " due to EOL");
                traceMayFate(pob, "EOL");
                families[pob.family].closed = true;
                leftQueue(pob, "EOL", nullptr);
            } else if (pob.next != PTRef_Undef) {
                // the first half is reachable, substitute the pob with its second half
                TRACE(2, "[Q] Considering MidPoint query as source: " << reached.reachedStates.x);
                ProofObligation secondHalf = pob; // same level, kind and family
                secondHalf.source = reached.reachedStates;
                secondHalf.target = pob.next;
                secondHalf.next = PTRef_Undef;
                secondHalf.sourceSteps = reached.steps;
                pushChild(pob, secondHalf, &MayFamily::secondHalves);
                leftQueue(pob, "REACHABLE", &MayFamily::reachable);
            } else if (pob.isMayPO) {
                traceMayFate(pob, "REACHABLE"); // nothing else to do for a reachable may-POB
                updateCcInputs(pob, "reachable");
                leftQueue(pob, "REACHABLE", &MayFamily::reachable);
            } else if (pob.level == power) {
                TRACE(2, "[R] Query " << to.x << " was reachable");
                // Families with pobs still queued (none expected: may-POBs sit below the goal's level)
                for (std::size_t id = 1; id < families.size(); ++id) {
                    if (families[id].queued > 0) { traceFamily(id, "OPEN"); }
                }
                TPA_INDENT = -1;
                QueryResult result;
                result.result = ReachabilityResult::REACHABLE;
                result.refinedTarget = reached.reachedStates;
                result.steps = reached.steps;
                return result;
            }
            continue;
        }

        // a relational may-POB has no entry in the database
        TPAPobInfo * info = isRelational(pob) ? nullptr : &pobDb[pob.target];
        if (info) {
            ++info->globalCounter;
            ++TPAPobInfo::atLevel(info->localCounter, pob.level);
        }
        if (pob.isMayPO) { ++families[pob.family].visits; }
        if (isRelational(pob)) {
            TRACE(2, "[?] (may) Can the pairs of " << pob.relation.x << " be connected in <=2^" << pob.level + 1
                  << " steps?")
        } else {
            TRACE(2, "[?] " << (pob.isMayPO ? "(may) " : "") << "Can " << pob.source.x << " reach " << pob.target.x
                  << " in <=2^" << pob.level + 1 << " steps?")
        }
        auto solver = getReachabilitySolver(pob.level + 1);
        assert(solver);
        PTRef goal = isRelational(pob) ? PTRef_Undef : getNextVersion(pob.target, 2);
        // the relation is over (x, x'), the query over (x, x'')
        PTRef query = isRelational(pob) ? shiftOnlyNextVars(pob.relation) : logic.mkAnd(pob.source, goal);
        auto res = solver->checkConsistent(query);
        switch (res) {
            case ReachabilityResult::REACHABLE: {
                if (isRelational(pob)) {
                    // not blocked: nothing to learn, and nothing to cache
                    TRACE(2, "[y] Some pair of " << pob.relation.x << " is connected in <=2^" << pob.level + 1
                          << " steps.");
                    traceMayFate(pob, "REACHABLE");
                    updateCcInputs(pob, "reachable");
                    pqueue.pop();
                    leftQueue(pob, "REACHABLE", &MayFamily::reachable);
                    continue;
                }
                TRACE(2, "[y] " << pob.source.x << " reaches " << pob.target.x << " in <=2^" << pob.level + 1 << " steps.");
                PTRef previousTransition = getLevelTransition(pob.level);
                PTRef translatedPreviousTransition = getNextVersion(previousTransition);
                auto model = solver->lastQueryModel();
                if (pob.level == 0) { // Base case, <=2 steps of the exact transition relation have been used
                    bool firstStepTaken = model->evaluate(identity) == logic.getTerm_false();
                    bool secondStepTaken = model->evaluate(getNextVersion(identity)) == logic.getTerm_false();
                    assert(
                        (not firstStepTaken or model->evaluate(transition) == logic.getTerm_true()) and
                        (not secondStepTaken or model->evaluate(getNextVersion(transition)) == logic.getTerm_true()));
                    PTRef refinedTarget = refineTwoStepTarget(
                           pob.source, logic.mkAnd(previousTransition, translatedPreviousTransition), goal, *model);
                    assert(refinedTarget != logic.getTerm_false());
                    // MB: Refined steps are computed from the whole formula representing 0-2 steps.
                    //     It might be possible that the step count is not correct ?!
                    unsigned steps = pob.sourceSteps + firstStepTaken + secondStepTaken;
                    TRACE(2, "[!] Exact: Truly reachable states are " << refinedTarget.x);
                    // The pob stays in the queue: its next examination finds its target in the cache
                    info->reached = ReachedStates{refinedTarget, steps};
                    if (pob.isMayPO) { families[pob.family].time += std::chrono::steady_clock::now() - visitStart; }
                    continue;
                }
                if (pob.isMayPO and families[pob.family].gas == 0) {
                    // the family cannot pay for the first half: close it
                    TRACE(1, "    Removing MayPO family " << pob.family << " due to EOL");
                    traceMayFate(pob, "EOL");
                    updateCcInputs(pob, "EOL");
                    families[pob.family].closed = true;
                    pqueue.pop();
                    leftQueue(pob, "EOL", nullptr);
                    continue;
                }
                // Create the three states corresponding to current, next and next-next variables from the query
                PTRef overMidPoint = PTRef_Undef;
                PTRef nextState = cfg.maypo and cfg.bmbp
                    ? extractMidPoint(pob.source, previousTransition, translatedPreviousTransition, goal, *model,
                                      overMidPoint)
                    : extractMidPoint(pob.source, previousTransition, translatedPreviousTransition, goal, *model);
                TRACE(2, "[Q] Considering MidPoint query as target: " << nextState.x)
                if (cfg.maypo) {
                    if (cfg.bmbp and overMidPoint != PTRef_Undef and overMidPoint != nextState and
                        overMidPoint != logic.getTerm_true()) {
                        TPAPobInfo::atLevel(info->overPredCache, pob.level).insert(overMidPoint, 0);
                    }
                    if (cfg.ccPob and nextState != logic.getTerm_true()) {
                        TPAPobInfo::atLevel(info->underPredCache, pob.level).insert(nextState, cfg.maxPobsForCc);
                    }
                }
                // need to find a midpoint: the pob stays in the queue, remember its target for the second half
                ProofObligation firstHalf{pob.source, nextState, static_cast<unsigned short>(pob.level - 1),
                                          pob.target, pob.sourceSteps};
                firstHalf.isMayPO = pob.isMayPO;
                firstHalf.family = pob.family;
                firstHalf.parentTarget = pob.target;
                pushChild(pob, firstHalf, &MayFamily::firstHalves);
                traceMayFate(pob, "SPAWNED");
                pushMayPobs(pob, buildMayPobs(pob));
                if (pob.isMayPO) { families[pob.family].time += std::chrono::steady_clock::now() - visitStart; }
                continue;
            }
            case ReachabilityResult::UNREACHABLE: {
                if (isRelational(pob)) {
                    TRACE(2, "[x] No pair of " << pob.relation.x << " is connected in <=2^" << pob.level + 1 << " steps.");
                } else {
                    TRACE(2, "[x] " << pob.source.x << " cannot reach " << pob.target.x << " in <=2^" << pob.level + 1
                          << " steps.");
                }

                PTRef itp = PTRef_Undef;
                if (pob.ccOrigin and cfg.generalize) {
                    // do not interpolate something that is already generalized: the negated query is itself an
                    // interpolant, the weakest one; let inductive generalization handle it. It is built facet by
                    // facet over (x, x'), as integer literals where possible, so its disjuncts are the facets:
                    // not(H(x, x')) for CC-lemma, not(source(x)) \/ not(hull(x')) for CC-pob.
                    LATermUtils latUtils(dynamic_cast<ArithLogic &>(logic));
                    vec<PTRef> facets = isRelational(pob)
                        ? TermUtils(logic).getTopLevelConjuncts(pob.relation)
                        : TermUtils(logic).getTopLevelConjuncts(logic.mkAnd(pob.source, getNextVersion(pob.target)));
                    vec<PTRef> negatedFacets;
                    for (PTRef facet : facets) { negatedFacets.push(latUtils.negateIntLiteral(facet)); }
                    itp = logic.mkOr(std::move(negatedFacets));
                    TRACE(2,
                          "---- [NEG] Negated CC query: " << itp.x
                          << " nr disj: " << TermUtils(logic).getTopLevelDisjuncts(itp).size()
                          << " nr vars: " << TermUtils(logic).getVars(itp).size());
                } else {
                    itp = solver->lastQueryTransitionInterpolant();
                    itp = simplifyInterpolant(itp);
                    itp = cleanInterpolant(itp);
                    TRACE(2,
                          "---- [ITP] Learnt lemma: " << itp.x
                          << " nr disj: " << TermUtils(logic).getTopLevelDisjuncts(itp).size()
                          << " nr vars: " << TermUtils(logic).getVars(itp).size());
                }
                if (cfg.debug and not checkLemma(pob.level, itp, false)) {
                    throw std::logic_error("Error in reachabilityQuery: the learnt lemma is not valid!");
                }

                if (cfg.generalize) {
                    itp = cfg.gdown ? generalize_down(pob.level, itp) : generalize(pob.level, itp);
                    TRACE(2,
                          "---- [ITP] Generalization: " << itp.x
                          << " nr disj: " << TermUtils(logic).getTopLevelDisjuncts(itp).size()
                          << " nr vars: " << TermUtils(logic).getVars(itp).size());
                }

                TRACE(2, "[+] Learning " << itp.x << " in power: " << pob.level + 1);
                TRACE(4, "Learning " << logic.pp(itp));
                TRACE(2, "[U] Query " << pobId(pob) << " is NOT reachable");
                // If itp == logic.getTerm_true, then the error states were trivially unreachable
                if (itp == logic.getTerm_true()) { assert(pob.level == 0); }
                storeLevelTransition(pob.level + 1, itp);
                if (cfg.maypo and cfg.ccLemma and pob.parentTarget != PTRef_Undef) {
                    pobDb[pob.parentTarget].blockingLemmas.insert(itp, cfg.maxLemmasForCc);
                }
                if (pob.isMayPO) {
                    TRACE(1, "    $$$$$$$$$$$$ MAY PO WAS BLOCKED $$$$$$$$$$$$");
                }
                traceMayFate(pob, "BLOCKED");
                pqueue.pop();
                pushMayPobs(pob, buildMayPobs(pob));
                leftQueue(pob, "BLOCKED", &MayFamily::blocked);
                continue;
            }
        }
    }
    TPA_INDENT = -1;
    QueryResult result;
    result.result = ReachabilityResult::UNREACHABLE;
    return result;
}

bool TPABasic::propagateTransitions(unsigned short power) {
    TRACE(2, "[->] Trying to propagate lemmas...")
    SMTSolver solver(logic, SMTSolver::WitnessProduction::NONE);
    for (auto i = 0; i < transitionHierarchy.size() - 1; ++i) {
        solver.push();
        auto currentLevel = getLevelTransition(i);
        solver.assertProp(currentLevel);
        solver.assertProp(getNextVersion(currentLevel));

        vec<PTRef> propagated;
        bool allPropagated = true;
        const auto& candidates = transitionHierarchy[i];
        const auto& nextLemmas = transitionHierarchy[i + 1];
        for (PTRef candidate : candidates) {
            // ANNA: todo: we can skip rightinvariant lemmas which are automatically pushed
            bool duplicate = \
                std::find(nextLemmas.begin(), nextLemmas.end(), candidate) != nextLemmas.end();
            if (duplicate) {
                continue;
            }
            // The exact transition in level 0 has auxiliary variables: it is not a lemma that can move up
            if (not isPureTransitionFormula(candidate)) {
                allPropagated = false;
                continue;
            }
            // Check if AT^i(x,x') & AT^i(x', x'') -> candidate(x, x'')
            solver.push();
            auto shiftedCandidate = shiftOnlyNextVars(candidate);
            solver.assertProp(logic.mkNot(shiftedCandidate));
            if (solver.check() == SMTSolver::Answer::UNSAT) {
                TRACE(1, "[push] Propagate " << candidate.x << " to " << i + 1);
                propagated.push(candidate);
            } else {
                allPropagated = false;
            }
            solver.pop();
        }
        for (PTRef lemma : propagated) {
            // ANNA: TODO: add a flag to avoid searching it in previous levels
            storeLevelTransition(i + 1, lemma);
        }
        if (i < power and allPropagated) {
            explanation.invariantType = SafetyExplanation::TransitionInvariantType::UNRESTRICTED;
            explanation.relationType = TPAType::LESS_THAN;
            explanation.fixedPointType = SafetyExplanation::FixedPointType::RIGHT;
            explanation.inductivnessPowerExponent = 0;
            explanation.safeTransitionInvariant = getLevelTransition(i);
            return true;
        }
        solver.pop();
    }
    return false;
}

void TPABasic::resetPowers() {
    this->transitionHierarchy.clear();
    this->clearReachabilitySolvers();
    this->pobDb.clear();
    storeLevelTransition(0, logic.mkOr(identity, transition));
}

bool TPABasic::verifyPower(unsigned short power, TPAType relationType) const {
    assert(relationType == TPAType::LESS_THAN);
    (void)relationType;
    return verifyPower(power);
}

bool TPABasic::verifyPower(unsigned short level) const {
    assert(level > 0);
    SMTSolver solver(logic, SMTSolver::WitnessProduction::NONE);
    PTRef current = getLevelTransition(level);
    PTRef previous = getLevelTransition(level - 1);
    solver.assertProp(logic.mkAnd(previous, getNextVersion(previous)));
    solver.assertProp(logic.mkNot(shiftOnlyNextVars(current)));
    solver.assertProp(logic.mkNot(shiftOnlyNextVars(current)));
    auto res = solver.check();
    return res == SMTSolver::Answer::UNSAT;
}

PTRef TPABasic::getPower(unsigned short power, TPAType relationType) const {
    assert(relationType == TPAType::LESS_THAN);
    (void)relationType;
    return getLevelTransition(power);
}

} // namespace golem
