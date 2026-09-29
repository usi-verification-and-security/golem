/*
 * Copyright (c) 2021-2024, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef GOLEM_TPABASE_HH
#define GOLEM_TPABASE_HH

#include "Options.h"
#include "Witnesses.h"

#include "osmt_solver.h"
#include "utils/OrderedFormulas.h"
#include "utils/SmtSolver.h"
#include <algorithm>
#include <cstddef>
#include <iterator>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <unordered_set>
#include <utility>
#include <vector>

namespace golem {

class TransitionSystem;

enum class ReachabilityResult { REACHABLE, UNREACHABLE };

class SolverWrapper {
protected:
    PTRef transition = PTRef_Undef;

public:
    virtual ~SolverWrapper() = default;
    virtual ReachabilityResult checkConsistent(PTRef query) = 0;
    virtual void strengthenTransition(PTRef nTransition) = 0;
    virtual std::unique_ptr<Model> lastQueryModel() = 0;
    virtual PTRef lastQueryTransitionInterpolant() = 0;
};

class SolverWrapperSingleUse : public SolverWrapper {
    Logic & logic;
    SMTSolver solver;
    SMTSolver::Answer lastResult = SMTSolver::Answer::UNKNOWN;

public:
    SolverWrapperSingleUse(Logic & logic, PTRef transition);

    ReachabilityResult checkConsistent(PTRef query) override;

    void strengthenTransition(PTRef nTransition) override;

    std::unique_ptr<Model> lastQueryModel() override;

    PTRef lastQueryTransitionInterpolant() override;
};

class SolverWrapperIncremental : public SolverWrapper {
protected:
    Logic & logic;
    SMTSolver solver;
    SMTSolver::Answer lastResult = SMTSolver::Answer::UNKNOWN;

    unsigned allformulasInserted = 0;
    ipartitions_t mask = 0;
    bool pushed = false;

public:
    SolverWrapperIncremental(Logic & logic, PTRef transition);

    ReachabilityResult checkConsistent(PTRef query) override;

    void strengthenTransition(PTRef nTransition) override;

    std::unique_ptr<Model> lastQueryModel() override;

    PTRef lastQueryTransitionInterpolant() override;
};

class SolverWrapperIncrementalWithRestarts : public SolverWrapperIncremental {
    vec<PTRef> transitionComponents;
    const unsigned limit = 100;
    unsigned levels = 0;

    void rebuildSolver();

public:
    SolverWrapperIncrementalWithRestarts(Logic & logic, PTRef transition);

    ReachabilityResult checkConsistent(PTRef query) override;

    void strengthenTransition(PTRef nTransition) override;
};

enum class TPAType : char { LESS_THAN, EQUALS };

struct SafetyExplanation {
    enum class TransitionInvariantType : char { NONE, UNRESTRICTED, RESTRICTED_TO_INIT, RESTRICTED_TO_QUERY };

    enum class FixedPointType : char { LEFT, RIGHT };

    TransitionInvariantType invariantType{TransitionInvariantType::NONE};
    TPAType relationType{TPAType::LESS_THAN};
    FixedPointType fixedPointType{FixedPointType::LEFT};
    PTRef safeTransitionInvariant{PTRef_Undef};

    /** the transition invariant is k-inductive for k = 2^{inductivnessPowerExponent}*/
    uint32_t inductivnessPowerExponent{0};
};

struct ReachedStates {
    PTRef reachedStates{PTRef_Undef};
    unsigned steps{0};
};

/// TPABasic: what is known about the target of a proof obligation, over every power it is examined at.
/// The per-level fields are indexed by the level of the pob that examined the target, and grow on demand
/// (atLevel). Growing invalidates references to their elements, so index them where they are used.
struct TPAPobInfo {
    /// examinations of this target, summed over every level
    std::size_t globalCounter = 0;
    /// level -> examinations of this target at that level
    std::vector<std::size_t> localCounter;
    /// level -> over-approximations of the midpoints, collected by BMBP
    std::vector<OrderedFormulas> overPredCache;
    /// level -> midpoints, i.e. the targets of the first halves, used by CC-pob
    std::vector<OrderedFormulas> underPredCache;
    /// lemmas that blocked a child of this target, at any level, used by CC-lemma
    OrderedFormulas blockingLemmas;
    /// once found: the reachable part of the target and its distance from the initial states
    std::optional<ReachedStates> reached;

    template<typename T> static T & atLevel(std::vector<T> & perLevel, std::size_t level) {
        if (perLevel.size() <= level) { perLevel.resize(level + 1); }
        return perLevel[level];
    }
};

class TPABase {
protected:
    Logic & logic;
    Options const & options;
    int verbosity = 0;
    bool useQE = false;
    SafetyExplanation explanation;
    ReachedStates reachedStates;

    // Versioned representation of the transition system
    PTRef init;
    PTRef transition;
    PTRef query;
    vec<PTRef> stateVariables;
    vec<PTRef> auxiliaryVariables;
    vec<PTRef> leftInvariants;
    vec<PTRef> rightInvariants;

    PTRef identity{PTRef_Undef};

public:
    TPABase(Logic & logic, Options const & options) : logic(logic), options(options) {
        verbosity = std::stoi(options.getOrDefault(Options::VERBOSE, "0"));
        if (options.hasOption(Options::TPA_USE_QE)) { useQE = true; }
    }

    virtual ~TPABase() = default;

    virtual VerificationAnswer solveTransitionSystem(TransitionSystem & system);

    void resetTransitionSystem(TransitionSystem const & system);

    VerificationAnswer solve();

    void resetInitialStates(PTRef);
    void resetQueryStates(PTRef);

    PTRef getInit() const;
    PTRef getTransitionRelation() const;
    PTRef getQuery() const;

    /**
     * After the current system has been proven safe, this method can be used to extract superset of initial states that
     * are also safe, given the explanation found by the algorithm.
     * @return superset of initial states that are still safe
     */
    PTRef getSafetyExplanation() const;
    PTRef getReachedStates() const;
    unsigned getTransitionStepCount() const;
    PTRef getInductiveInvariant() const;
    vec<PTRef> getStateVars(int version) const;

protected:
    virtual VerificationAnswer checkPower(unsigned short power) = 0;

    virtual void resetPowers() = 0;

    virtual PTRef getPower(unsigned short power, TPAType relationType) const = 0;
    virtual bool verifyPower(unsigned short power, TPAType relationType) const = 0;

    struct QueryResult {
        ReachabilityResult result;
        PTRef refinedTarget{PTRef_Undef};
        unsigned steps{0};
    };

    static bool isReachable(QueryResult res) { return res.result == ReachabilityResult::REACHABLE; };
    static bool isUnreachable(QueryResult res) { return res.result == ReachabilityResult::UNREACHABLE; };
    static PTRef extractReachableTarget(QueryResult res) { return res.refinedTarget; };
    static unsigned extractStepsTaken(QueryResult res) { return res.steps; };

    using CacheType = std::unordered_map<std::pair<PTRef, PTRef>, QueryResult, PTRefPairHash>;
    std::vector<CacheType> queryCache;

    /// TPABasic: proof-obligation database, by target. Reachability does not depend on the levels, so it is
    /// kept across powers; it depends on the initial states, so it is cleared with them.
    std::unordered_map<PTRef, TPAPobInfo, PTRefHash> pobDb;
    /// TPABasic: every reached set of pobDb, in the order they were found. They are truly reachable from the
    /// initial states, so it is cleared with pobDb.
    std::vector<ReachedStates> knownReachable;

    struct VersionHasher {
        std::size_t operator()(std::pair<PTRef, int> val) const {
            return std::hash<uint32_t>()(val.first.x) ^ std::hash<int>()(val.second);
        }
    };
    mutable std::unordered_map<std::pair<PTRef, int>, PTRef, VersionHasher> versioningCache;

    PTRef getNextVersion(PTRef currentVersion, int) const;
    PTRef getNextVersion(PTRef currentVersion) const { return getNextVersion(currentVersion, 1); };

    /* Shifts only next-next vars to next vars */
    PTRef cleanInterpolant(PTRef itp) const;
    /* Shifts only next vars to next-next vars */
    PTRef shiftOnlyNextVars(PTRef transition) const;

    PTRef simplifyInterpolant(PTRef itp);

    int verbose() const { return verbosity; }

    bool isPureStateFormula(PTRef fla) const;
    bool isPureTransitionFormula(PTRef fla) const;

    bool verifyKinductiveInvariant(PTRef invariant, unsigned long k) const;

    PTRef refineTwoStepTarget(PTRef start, PTRef transition, PTRef goal, Model & model);

    PTRef extractMidPoint(PTRef start, PTRef firstTransition, PTRef secondTransition, PTRef goal, Model & model);
    /// As above; also returns in `overMidPoint` the over-approximations of the two projections (BMBP)
    PTRef extractMidPoint(PTRef start, PTRef firstTransition, PTRef secondTransition, PTRef goal, Model & model,
                          PTRef & overMidPoint);

    PTRef eliminateVars(PTRef fla, vec<PTRef> const & vars, Model & model);
    PTRef eliminateVars(PTRef fla, vec<PTRef> const & vars, Model & model, PTRef & overapprox);

    PTRef keepOnlyVars(PTRef fla, vec<PTRef> const & vars, Model & model);

    PTRef safeSupersetOfInitialStates(PTRef start, PTRef transitionInvariant, PTRef target) const;

    void houdiniCheck(PTRef invCandidates, PTRef transition, SafetyExplanation::FixedPointType alignment);

    bool checkLessThanFixedPoint(unsigned short power);

    PTRef computeIdentity() const;

    void resetExplanation();

    void squashInvariants(vec<PTRef> & candidates);

    VerificationAnswer checkTrivialUnreachability();
};

class TPASplit : public TPABase {

    vec<PTRef> exactPowers;
    vec<PTRef> lessThanPowers;

    vec<SolverWrapper *> reachabilitySolvers;

public:
    TPASplit(Logic & logic, Options const & options) : TPABase(logic, options) {}

    ~TPASplit() override;

    PTRef inductiveInvariantFromEqualsTransitionInvariant() const;

private:
    void resetPowers() override;

    VerificationAnswer checkPower(unsigned short power) override;
    PTRef getPower(unsigned short power, TPAType relationType) const override;
    bool verifyPower(unsigned short power, TPAType relationType) const override;

    PTRef getExactPower(unsigned short power) const;
    void storeExactPower(unsigned short power, PTRef tr);

    PTRef getLessThanPower(unsigned short power) const;
    void storeLessThanPower(unsigned short power, PTRef tr);

    SolverWrapper * getExactReachabilitySolver(unsigned short power) const;

    QueryResult reachabilityQueryExact(PTRef from, PTRef to, unsigned short power);
    QueryResult reachabilityQueryLessThan(PTRef from, PTRef to, unsigned short power);

    bool verifyLessThanPower(unsigned short power) const;
    bool verifyExactPower(unsigned short power) const;

    bool checkExactFixedPoint(unsigned short power);

    void clearReachabilitySolvers();
};

struct TPABasicConfig {
    // wired to the command line
    bool generalize = true;      // generalize learnt lemmas (inductively)
    bool maypo = false;          // may-POB main guard
    bool bmbp = true;            // may-POBs from the bidirectional MBP of the midpoints
    bool ccLemma = true;         // relational may-POBs from the convex closure of the negated blocking lemmas
    bool ccPob = true;           // may-POBs from the convex closure of the midpoints
    bool ccUpdate = true;        // a CC root found reachable or out of gas keeps only the newest of the
                                 // inputs its hull came from
    /// Once the target of a pob has been examined `triggerConjecture` times (over every level), a pob that
    /// spawns a midpoint from its source also spawns one from another reached set (not the initial states, not
    /// its source; the furthest from the initial states among those that can reach the target), and examines it
    /// first. Skipped if that gives the same midpoint.
    bool conjecture = false;

    // not wired to cmd line: change the default here
    bool gdown = true;           // generalize by dropping disjuncts (otherwise, use unsatcore)
    bool debug = true;           // run validity checks of learnt and generalized lemmas

    // tuning parameters (wired: --tpa.maypo-gas / --tpa.maypo-trigger / --tpa.max-lemmas-cc
    // / --tpa.min-pobs-cc / --tpa.max-pobs-cc / --tpa.conjecture-trigger)
    std::size_t mayPoGas = 5;             // pobs a may-POB family may push below its root
    std::size_t triggerMayPo = 3;         // visits of a target (at a level, for BMBP and CC-pob; at any
                                          // level, for CC-lemma) before may-POBs are built
    std::size_t minLemmasForCc = 2;       // blocking lemmas needed before CC-lemma fires
    std::size_t maxLemmasForCc = 7;       // blocking lemmas kept per target for CC-lemma, oldest evicted
                                          // first; 0 = no limit
    std::size_t minPobsForCc = 2;         // midpoints needed before CC-pob fires
    std::size_t maxPobsForCc = 7;         // midpoints kept per target and level for CC-pob, oldest
                                          // evicted first; 0 = no limit
    std::size_t triggerConjecture = 10;   // examinations of a target, over every level, before `conjecture` fires
    // not wired to cmd line
    std::size_t minBmbpOverLits = 1;      // over-approximations of the midpoints needed before BMBP fires
    std::size_t ccMbpBudget = 10;         // budget for MBP iterations per implicant in ConvexClosure

    void validate() const {
        if (mayPoGas < 1) { throw std::logic_error("TPA: TPABasicConfig::mayPoGas must be at least 1"); }
        if (triggerMayPo < 1) { throw std::logic_error("TPA: TPABasicConfig::triggerMayPo must be at least 1"); }
        if (triggerConjecture < 1) {
            throw std::logic_error("TPA: TPABasicConfig::triggerConjecture must be at least 1");
        }
        if (maxLemmasForCc != 0 and maxLemmasForCc < minLemmasForCc) {
            throw std::logic_error("TPA: TPABasicConfig::maxLemmasForCc must be 0 (no limit) or at least "
                                   "minLemmasForCc, otherwise CC-lemma never fires");
        }
        if (maxPobsForCc != 0 and maxPobsForCc < minPobsForCc) {
            throw std::logic_error("TPA: TPABasicConfig::maxPobsForCc must be 0 (no limit) or at least "
                                   "minPobsForCc, otherwise CC-pob never fires");
        }
    }

    static TPABasicConfig from(Options const & options) {
        TPABasicConfig cfg;
        // Tri-state: nullopt = not given, so "absent" and "=false" stay distinguishable.
        auto flag = [&options](std::string const & key) -> std::optional<bool> {
            auto value = options.getOption(key);
            if (not value) { return std::nullopt; }
            return *value == "true";
        };
        if (auto const generalize = flag(Options::TPA_GENERALIZE)) { cfg.generalize = *generalize; }
        // --tpa.maypob turns every source on, or the whole mechanism off.
        auto const maypob = flag(Options::TPA_MAYPOB);
        // --tpa.cc names both convex-closure sources; --tpa.cc-lemma / --tpa.cc-pob override it for their own
        // source.
        auto const cc = flag(Options::TPA_CC);
        auto const ccLemma = flag(Options::TPA_CC_LEMMA);
        auto const ccPob = flag(Options::TPA_CC_POB);
        std::pair<std::optional<bool>, bool *> const sources[] = {
            {flag(Options::TPA_BMBP), &cfg.bmbp},
            {ccLemma ? ccLemma : cc, &cfg.ccLemma},
            {ccPob ? ccPob : cc, &cfg.ccPob},
        };
        if (maypob) {
            cfg.maypo = *maypob;
            if (*maypob) {
                for (auto const & [given, source] : sources) { *source = true; }
            }
        }
        // Each source flag selects its own source: asking for some without mentioning the others
        // turns the others off, and asking for any of them implies --tpa.maypob.
        bool const anySelected = std::any_of(std::begin(sources), std::end(sources),
                                             [](auto const & entry) { return entry.first.value_or(false); });
        for (auto const & [given, source] : sources) {
            if (given) {
                *source = *given;
            } else if (anySelected) {
                *source = false;
            }
        }
        if (anySelected) { cfg.maypo = true; }
        if (auto const ccUpdate = flag(Options::TPA_CC_UPDATE)) { cfg.ccUpdate = *ccUpdate; }
        if (auto const conjecture = flag(Options::TPA_CONJECTURE)) { cfg.conjecture = *conjecture; }
        // Numeric knobs: the raw argument is kept by the parser so it can be rejected here
        // with a message naming the flag, rather than silently becoming 0.
        auto positive = [&options](std::string const & key, std::size_t & target) {
            auto const value = options.getOption(key);
            if (not value) { return; }
            std::size_t consumed = 0;
            long long parsed = 0;
            try {
                parsed = std::stoll(*value, &consumed);
            } catch (std::exception const &) { consumed = 0; }
            if (consumed != value->size() or parsed < 1) {
                throw std::logic_error("TPA: --" + key + " expects a positive integer, got '" + *value + "'");
            }
            target = static_cast<std::size_t>(parsed);
        };
        positive(Options::TPA_MAYPO_GAS, cfg.mayPoGas);
        positive(Options::TPA_MAYPO_TRIGGER, cfg.triggerMayPo);
        positive(Options::TPA_MAX_LEMMAS_CC, cfg.maxLemmasForCc);
        positive(Options::TPA_MIN_POBS_CC, cfg.minPobsForCc);
        positive(Options::TPA_MAX_POBS_CC, cfg.maxPobsForCc);
        positive(Options::TPA_CONJECTURE_TRIGGER, cfg.triggerConjecture);

        cfg.validate();
        return cfg;
    }
};

class TPABasic : public TPABase {

    TPABasicConfig cfg;

    std::vector<vec<PTRef>> transitionHierarchy;

    vec<SolverWrapper *> reachabilitySolvers;

public:
    TPABasic(Logic & logic, Options const & options)
        : TPABase(logic, options), cfg(TPABasicConfig::from(options)) {}

    ~TPABasic() override;

private:
    void resetPowers() override;

    VerificationAnswer checkPower(unsigned short power) override;

    PTRef getPower(unsigned short power, TPAType relationType) const override;
    bool verifyPower(unsigned short power, TPAType relationType) const override;

    PTRef getLevelTransition(unsigned short) const;
    void storeLevelTransition(unsigned short, PTRef);

    bool propagateTransitions(unsigned short);

    PTRef generalizationBase() const;
    PTRef generalize(unsigned short power, PTRef lemma) const;
    PTRef generalize_down(unsigned short power, PTRef lemma) const;
    void checkGeneralization(unsigned short power, PTRef lemma, PTRef newLemma, std::string const & where) const;

    bool checkLemma(unsigned short power, PTRef lemma, bool inductive) const;

    SolverWrapper * getReachabilitySolver(unsigned short power) const;

    QueryResult reachabilityQuery(PTRef from, PTRef to, unsigned short power);

    bool verifyPower(unsigned short level) const;

    void clearReachabilitySolvers();
};

// Overridable from the build, e.g. -DCMAKE_CXX_FLAGS=-DGOLEM_TRACE_LEVEL=1 for sweeps (Spacer reads it too).
#ifdef GOLEM_TRACE_LEVEL
#define TRACE_LEVEL GOLEM_TRACE_LEVEL
#else
#define TRACE_LEVEL 2
#endif

extern int TPA_INDENT;

#define INCR_INDENT TPA_INDENT++;
#define DECR_INDENT TPA_INDENT--;

#define TRACE(l, m) \
    if (TRACE_LEVEL >= l) { \
        for (auto _i = 0; _i < TPA_INDENT; ++_i) std::cout << " - "; \
        std::cout << m << std::endl; }

} // namespace golem

#endif // GOLEM_TPABASE_HH
