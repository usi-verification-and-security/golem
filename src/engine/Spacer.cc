/*
 * Copyright (c) 2021-2022, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "Spacer.h"

#include "ModelBasedProjection.h"
#include "TermUtils.h"
#include "api/MainSolver.h"
#include "graph/ChcGraph.h"
#include "proof/PG.h"
#include "pterms/PTRef.h"
#include "symbols/SymRef.h"
#include "utils/SmtSolver.h"
#include "utils/ConvexClosure.h"
#include "utils/InductiveInterpolants.h"

#include <algorithm>
#include <cstddef>
#include <deque>
#include <exception>
#include <iostream>
#include <memory>
#include <optional>
#include <queue>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#define TRACE_LEVEL 2

namespace golem {

struct SpacerConfig {
    // wired to the command line
    bool maypo = false;          // may-POB main guard
    bool bmbp = true;            // may-POBs from bidirectional MBP
    bool ccLemma = true;         // may-POBs from the convex closure of blocking lemmas
    bool ccPob = true;           // may-POBs from the convex closure of predecessor under-approximations
    bool ccUpdate = true;        // a CC root's fate rewrites its inputs: reachable / EOL -> keep the
                                 // newest, blocked -> replace them by the blocking lemma
                                 // (SpacerContext::updateCcInputs)
    bool generalize = true;      // generalize learnt lemmas (inductively if possible)
    bool relind = false;          // try to block with relative induction even when there are predecessors

    // not wired to cmd line: change the default here
    bool gdown = true;           // generalize by dropping disjuncts (otherwise, use unsatcore)
    bool relindGrow = false;     // relative induction: grow-from-init mbp-based variant

    /// How a blocking lemma is derived. At least one must hold; both may, in which case
    /// both learnt lemmas are added
    bool interpolation = true;   // lemma from the interpolant of the blocked query
    bool indConflict = false;    // lemma from the mbp-based inductive conflict

    bool debug = true;           // run validity checks of new lemmas

    bool mayPobOnLastVisit = false; // also build may-POBs on a pob's final visit

    /// What computePredecessor projects on, AFTER taking the model from the full check.
    /// true  = include the may-summary of the refined source: the projection is relative to
    ///         the frame, so under/over are bound-dependent.
    /// false = every other source's summary plus the transition, dropping only the refined
    ///         source's may-summary. See getEdgeMustOnlySummary.
    /// Wired: --spacer.mbp-may-summary.
    bool mbpWithMaySummary = false;

    /// Key the blocking lemmas of a subgoal by (vertex, formula) instead of (vertex, formula,
    /// bound), i.e. accumulate them across bounds, and trigger CC-lemma on the visits over every
    /// bound. The predecessor approximations (BMBP's over, CC-pob's under) are always per bound,
    /// and BMBP / CC-pob always trigger on the visits at their bound.
    /// Off by default and **independent of mbpWithMaySummary**.
    /// Wired: --spacer.global-pob-db.
   bool globalPobDb = false;

    // tuning parameters (wired: --spacer.maypo-gas / --spacer.maypo-trigger / --spacer.max-lemmas-cc
    // / --spacer.min-pobs-cc / --spacer.max-pobs-cc)
    std::size_t mayPoGas = 5;             // predecessor-chain length allowed from a may-POB
    std::size_t triggerMayPo = 3;         // visits before may-POBs are built
    std::size_t minLemmasForCc = 2;       // blocking lemmas needed before CC-lemma fires
    std::size_t maxLemmasForCc = 7;       // blocking lemmas kept per child for CC-lemma, oldest evicted
                                          // first; 0 = no limit
    std::size_t minPobsForCc = 2;         // under-approximations of a predecessor needed before CC-pob
                                          // fires
    std::size_t maxPobsForCc = 7;         // under-approximations kept per edge source for CC-pob,
                                          // oldest evicted first; 0 = no limit
    std::size_t minBmbpOverLits = 1;      // literals needed in a BMBP over-approximation
    std::size_t relindMaxIterations = 20; // budget for the grow-from-init loop

    // Make sure we have a way to produce a lemma
    void validate() const {
        if (mayPoGas < 1) {
            throw std::logic_error("Spacer: SpacerConfig::mayPoGas must be at least 1");
        }
        if (triggerMayPo < 1) {
            throw std::logic_error("Spacer: SpacerConfig::triggerMayPo must be at least 1");
        }
        if (maxLemmasForCc != 0 and maxLemmasForCc < minLemmasForCc) {
            throw std::logic_error("Spacer: SpacerConfig::maxLemmasForCc must be 0 (no limit) or at least "
                                   "minLemmasForCc, otherwise CC-lemma never fires");
        }
        if (maxPobsForCc != 0 and maxPobsForCc < minPobsForCc) {
            throw std::logic_error("Spacer: SpacerConfig::maxPobsForCc must be 0 (no limit) or at least "
                                   "minPobsForCc, otherwise CC-pob never fires");
        }
        if (not interpolation and not indConflict) {
            throw std::logic_error(
                "Spacer: at least one of SpacerConfig::interpolation and ::indConflict must be set, "
                "otherwise blocking a proof obligation derives no lemma");
        }
    }

    static SpacerConfig from(Options const & options) {
        SpacerConfig cfg;
        // Tri-state: nullopt = not given, so "absent" and "=false" stay distinguishable.
        auto flag = [&options](std::string const & key) -> std::optional<bool> {
            auto value = options.getOption(key);
            if (not value) { return std::nullopt; }
            return *value == "true";
        };
        auto const maypob = flag(Options::SPACER_MAYPOB);
        // --spacer.cc names both convex-closure sources; --spacer.cc-lemma / --spacer.cc-pob
        // override it for their own source.
        auto const cc = flag(Options::SPACER_CC);
        auto const ccLemma = flag(Options::SPACER_CC_LEMMA);
        auto const ccPob = flag(Options::SPACER_CC_POB);
        std::pair<std::optional<bool>, bool *> const sources[] = {
            {flag(Options::SPACER_BMBP), &cfg.bmbp},
            {ccLemma ? ccLemma : cc, &cfg.ccLemma},
            {ccPob ? ccPob : cc, &cfg.ccPob},
        };

        // --spacer.maypob turns every source on, or the whole mechanism off.
        if (maypob) {
            cfg.maypo = *maypob;
            if (*maypob) {
                for (auto const & [given, source] : sources) { *source = true; }
            }
        }
        // Each source flag selects its own source: asking for some without mentioning the others
        // turns the others off, and asking for any of them implies --spacer.maypob.
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
        // --spacer.indgen drives relative induction too, unless --spacer.relind names it
        // explicitly -- the same "unless also specified" rule as the may-POB sources.
        auto const indgen = flag(Options::SPACER_INDGEN);
        auto const relind = flag(Options::SPACER_RELIND);
        if (indgen) {
            cfg.generalize = *indgen;
            if (not relind) { cfg.relind = *indgen; }
        }
        if (relind) { cfg.relind = *relind; }
        if (auto const mbpMaySummary = flag(Options::SPACER_MBP_MAY_SUMMARY)) {
            cfg.mbpWithMaySummary = *mbpMaySummary;
        }
        if (auto const globalPobDb = flag(Options::SPACER_GLOBAL_POB_DB)) {
            cfg.globalPobDb = *globalPobDb;
        }
        if (auto const ccUpdate = flag(Options::SPACER_CC_UPDATE)) {
            cfg.ccUpdate = *ccUpdate;
        }
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
                throw std::logic_error("Spacer: --" + key + " expects a positive integer, got '" +
                                       *value + "'");
            }
            target = static_cast<std::size_t>(parsed);
        };
        positive(Options::SPACER_MAYPO_GAS, cfg.mayPoGas);
        positive(Options::SPACER_MAYPO_TRIGGER, cfg.triggerMayPo);
        positive(Options::SPACER_MAX_LEMMAS_CC, cfg.maxLemmasForCc);
        positive(Options::SPACER_MIN_POBS_CC, cfg.minPobsForCc);
        positive(Options::SPACER_MAX_POBS_CC, cfg.maxPobsForCc);

        cfg.validate();
        return cfg;
    }
};
} // namespace golem

#define TRACE(l, m) \
    if (TRACE_LEVEL >= l) { std::cout << m << std::endl; }

namespace golem {

struct SpacerStats {
    std::size_t nr_push = 0;
    std::size_t currentBound = 0;
    void increse_push(std::size_t nr) { nr_push += nr; }
    void setBound(std::size_t nr) { currentBound = nr; }
    void print() { std::cerr << "[STATS] NR PUSHES: " << nr_push << std::endl
                             << "[STATS] BOUND: " << currentBound << std::endl; }
};

struct GuardVar {
    SymRef vertex;
    PTRef baseGuard;
    std::size_t instance;
    PTRef get(Logic& logic) const {
        return VersionManager(logic).baseFormulaToSource(baseGuard, instance);
    }
    PTRef getGuardedVersion(Logic& logic, PTRef phi) const {
        return VersionManager(logic).
            baseFormulaToSource(logic.mkImpl(baseGuard, phi), instance);
    }
};

class ApproxMap {
public:
    vec<PTRef> getComponents(SymRef vid, std::size_t bound, bool all = true) const {
        vec<PTRef> res;
        (const_cast<ApproxMap *>(this))->ensureBound(bound);
        while (bound < innerMap.size()) {
            auto const & boundMap = innerMap[bound];
            auto it = boundMap.find(vid);
            if (it != boundMap.end()) {
                res.capacity(it->second.size());
                for (PTRef component : it->second) {
                    res.push(component);
                }
            }
            if (not all) break;
            ++bound;
        }
        return res;
    }

    void remove(SymRef vid, std::size_t bound, PTRef summary) {
        ensureBound(bound);
        auto & boundMap = innerMap[bound];
        auto & components = boundMap[vid];
        auto it = std::find(components.begin(), components.end(), summary);
        if (it != components.end())
            components.erase(it);
    }

    void insert(SymRef vid, std::size_t bound, PTRef summary, bool all = true) {
        ensureBound(bound);
        auto & boundMap = innerMap[bound];
        auto & components = boundMap[vid];
        if (all) {
            for (auto b = 0; b < bound; ++b) {
                auto& prevMap = innerMap[b];
                auto& prevComponents = prevMap[vid];
                auto it = std::find(prevComponents.begin(), prevComponents.end(), summary);
                if (it != prevComponents.end()) {
                    prevComponents.erase(it);
                }
            }
        }
        components.insert(summary);
    }

    bool has(SymRef vid, std::size_t bound, PTRef summary) {
        ensureBound(bound);
        auto const & boundMap = innerMap[bound];
        auto it = boundMap.find(vid);
        if (it != boundMap.end()) { return it->second.find(summary) != it->second.end(); }
        return false;
    }

private:
    /// bound -> vertex -> elements of approximation
    std::vector<std::unordered_map<SymRef, std::unordered_set<PTRef, PTRefHash>, SymRefHash>> innerMap;

    void ensureBound(std::size_t bound) {
        while (innerMap.size() <= bound) {
            innerMap.emplace_back();
        }
    }
};

class UnderApproxMap : public ApproxMap {};

// How a lemma was derived
using LemmaOriginMask = unsigned short;

namespace LemmaOrigin {
constexpr LemmaOriginMask None = 0;
// how the lemma was derived
constexpr LemmaOriginMask Itp = 1u << 0;        // plain interpolant
constexpr LemmaOriginMask IndItp = 1u << 1;     // inductive interpolant
constexpr LemmaOriginMask RelInd = 1u << 2;     // relative induction, drop-conjuncts variant
constexpr LemmaOriginMask RelIndGrow = 1u << 3; // relative induction, grow-from-init variant
// which kind of proof obligation was being blocked
constexpr LemmaOriginMask Must = 1u << 4;
constexpr LemmaOriginMask May = 1u << 5;
// which mechanism created the ROOT of this may-pob's subtree; inherited by every descendant
constexpr LemmaOriginMask MayCcLemma = 1u << 6;
constexpr LemmaOriginMask MayBmbp = 1u << 7;
constexpr LemmaOriginMask MayCcPob = 1u << 9;
// set only on the pob the CC-lemma / BMBP / CC-pob block created directly, not on its descendants
constexpr LemmaOriginMask MayRoot = 1u << 8;

constexpr LemmaOriginMask MechanismMask = Itp | IndItp | RelInd | RelIndGrow;
constexpr LemmaOriginMask PobMask = Must | May;
constexpr LemmaOriginMask MaySourceMask = MayCcLemma | MayBmbp | MayCcPob;

constexpr LemmaOriginMask ofPob(bool isMayPO) { return isMayPO ? May : Must; }
} // namespace LemmaOrigin

inline std::string lemmaOriginToString(LemmaOriginMask origin) {
    if (origin == LemmaOrigin::None) { return "NONE"; }
    std::string res;
    auto add = [&](LemmaOriginMask bit, char const * name) {
        if ((origin & bit) == 0) { return; }
        if (not res.empty()) { res += '|'; }
        res += name;
    };
    add(LemmaOrigin::Itp, "ITP");
    add(LemmaOrigin::IndItp, "INDITP");
    add(LemmaOrigin::RelInd, "RELIND");
    add(LemmaOrigin::RelIndGrow, "RELINDGROW");
    add(LemmaOrigin::Must, "MUST");
    add(LemmaOrigin::May, "MAY");
    add(LemmaOrigin::MayCcLemma, "CC");
    add(LemmaOrigin::MayBmbp, "BMBP");
    add(LemmaOrigin::MayCcPob, "CCPOB");
    add(LemmaOrigin::MayRoot, "ROOT");
    return res;
}

/// `first` is the authoritative tag: the origin of the first discovery of the lemma.
/// `seen` is the union of every origin the lemma was ever derived with
struct LemmaProvenance {
    LemmaOriginMask first = LemmaOrigin::None;
    LemmaOriginMask seen = LemmaOrigin::None;
};

class OverApproxMap : public ApproxMap {
public:
    /// Records how `lemma` was discovered for `vid`.  The first origin wins and is kept.
    /// Returns the stored first origin when `origin` disagrees with it, None otherwise.
    LemmaOriginMask recordOrigin(SymRef vid, PTRef lemma, LemmaOriginMask origin) {
        if (origin == LemmaOrigin::None) { return LemmaOrigin::None; }
        auto & provenance = origins[vid][lemma];
        if (provenance.first == LemmaOrigin::None) {
            provenance.first = origin;
            provenance.seen = origin;
            return LemmaOrigin::None;
        }
        provenance.seen |= origin;
        return provenance.first == origin ? LemmaOrigin::None : provenance.first;
    }

    LemmaProvenance getProvenance(SymRef vid, PTRef lemma) const {
        auto vit = origins.find(vid);
        if (vit == origins.end()) { return {}; }
        auto it = vit->second.find(lemma);
        return it == vit->second.end() ? LemmaProvenance{} : it->second;
    }

private:
    /// vertex -> lemma -> provenance
    std::unordered_map<SymRef, std::unordered_map<PTRef, LemmaProvenance, PTRefHash>, SymRefHash> origins;
};


/// Formulas collected for one node, without duplicates, in insertion order so the oldest can be
/// evicted first.
class OrderedFormulas {
public:
    std::size_t size() const { return order.size(); }
    auto begin() const { return order.begin(); }
    auto end() const { return order.end(); }
    /// Adds `formula` unless already present (a duplicate keeps its original position); then, if
    /// `maxSize` > 0, evicts the oldest formulas until at most `maxSize` remain.
    void insert(PTRef formula, std::size_t maxSize) {
        if (not members.insert(formula).second) { return; }
        order.push_back(formula);
        while (maxSize > 0 and order.size() > maxSize) {
            members.erase(order.front());
            order.pop_front();
        }
    }
    /// Drops every formula but the most recently added one.
    void keepOnlyNewest() {
        if (order.size() > 1) { replaceWith(order.back()); }
    }
    /// Replaces every formula by `formula`.
    void replaceWith(PTRef formula) {
        order.assign(1, formula);
        members = {formula};
    }

private:
    std::deque<PTRef> order;
    std::unordered_set<PTRef, PTRefHash> members;
};

class EdgeVidPredCache {
public:
    using InnerMap = std::unordered_map<std::size_t, OrderedFormulas>;
    using OuterMap = std::map<EId, InnerMap>;

    // Iterator that flattens the two-level map, yielding (SymRef, set<PTRef>) pairs
    // where the set has at least INSERT_MAY_PO_THRESHOLD elements
    class FilterIterator {
    public:
        using value_type = InnerMap::value_type;
        using reference  = value_type const &;
        using pointer    = value_type const *;

        FilterIterator(OuterMap::const_iterator outer, OuterMap::const_iterator outerEnd,
                       std::size_t minSize = 0)
            : outer(outer), outerEnd(outerEnd), minSize(minSize) {
            if (outer != outerEnd) { inner = outer->second.begin(); }
            advanceToValid();
        }

        reference operator*()  const { return *inner; }
        pointer   operator->() const { return &*inner; }

        FilterIterator & operator++() {
            ++inner;
            advanceToValid();
            return *this;
        }

        bool operator==(FilterIterator const & other) const {
            assert(other.outerEnd == outerEnd);
            if (outer != other.outer) return false;
            if (outer == outerEnd) return true; // outer = other.outer == outerEnd
            return inner == other.inner;
        }
        bool operator!=(FilterIterator const & other) const { return !(*this == other); }

        SymRef getNode(ChcDirectedHyperGraph const & graph) const {
            return graph.getSources(outer->first)[inner->first];
        }
        EId getEdge() const { return outer->first; }
        std::size_t getSourceIndex() const { return inner->first; }
        vec<PTRef> getApprox() const {
            vec<PTRef> approx;
            approx.capacity(inner->second.size());
            for (PTRef con : inner->second) { approx.push(con); }
            return approx;
        }

    private:
        OuterMap::const_iterator outer, outerEnd;
        InnerMap::const_iterator inner;
        std::size_t minSize = 0;

        void advanceToValid() {
            while (outer != outerEnd) {
                while (inner != outer->second.end()) {
                    if (inner->second.size() >= minSize) return;
                    ++inner;
                }
                ++outer;
                if (outer != outerEnd) { inner = outer->second.begin(); }
            }
        }
    };

    /// `minSize` filters out entries with fewer than that many collected formulas.
    FilterIterator begin(std::size_t minSize) const {
        return FilterIterator(cache.begin(), cache.end(), minSize);
    }
    FilterIterator end() const { return {cache.end(), cache.end()}; }

    bool empty() const { return cache.empty(); }
    /// `maxSize` > 0 caps the formulas kept for (`edge`, `node`), first in first out; 0 keeps them all.
    void insert(EId edge, std::size_t node, PTRef cons, std::size_t maxSize) {
        cache[edge][node].insert(cons, maxSize);
    }
    OrderedFormulas & at(EId edge, std::size_t node) { return cache[edge][node]; }

private:
    OuterMap cache;
};

class VidPredCache {
public:
    using InnerMap = std::unordered_map<SymRef, OrderedFormulas, SymRefHash>;

    // Iterator that yields (SymRef, set<PTRef>) pairs
    // where the set has at least INSERT_MAY_PO_THRESHOLD elements
    class FilterIterator {
    public:
        using value_type = InnerMap::value_type;
        using reference  = value_type const &;
        using pointer    = value_type const *;

        FilterIterator(InnerMap::const_iterator inner, InnerMap::const_iterator innerEnd,
                       std::size_t minSize = 0)
            : inner(inner), innerEnd(innerEnd), minSize(minSize) {
            advanceToValid();
        }

        reference operator*()  const { return *inner; }
        pointer   operator->() const { return &*inner; }

        FilterIterator & operator++() {
            ++inner;
            advanceToValid();
            return *this;
        }

        bool operator==(FilterIterator const & other) const {
            return inner == other.inner;
        }
        bool operator!=(FilterIterator const & other) const { return !(*this == other); }

        SymRef getNode() const {
            return inner->first;
        }
        vec<PTRef> getApprox() const {
            vec<PTRef> approx;
            approx.capacity(inner->second.size());
            for (PTRef con : inner->second) { approx.push(con); }
            return approx;
        }

    private:
        InnerMap::const_iterator inner, innerEnd;
        std::size_t minSize = 0;

        void advanceToValid() {
            while (inner != innerEnd) {
                if (inner->second.size() >= minSize) return;
                ++inner;
            }
        }
    };

    /// `minSize` filters out entries with fewer than that many collected lemmas.
    FilterIterator begin(std::size_t minSize) const {
        return FilterIterator(cache.begin(), cache.end(), minSize);
    }
    FilterIterator end() const { return FilterIterator(cache.end(), cache.end()); }

    bool empty() const { return cache.empty(); }
    /// `maxSize` > 0 caps the lemmas kept for `node`, first in first out; 0 keeps them all.
    void insert(SymRef node, PTRef cons, std::size_t maxSize) {
        cache[node].insert(cons, maxSize);
    }
    OrderedFormulas & at(SymRef node) { return cache[node]; }

private:
    InnerMap cache;
};

/// Everything we know about a proof obligation *as a subgoal*, i.e. about the pair
/// (vertex, formula), over every bound it is examined at.
/// A pob object lives only inside one boundSafety() call; this survives the whole run,
/// so the evidence gathered about a subgoal is not thrown away and re-derived each bound.
/// The per-bound fields are indexed by the bound of the pob that OWNS the evidence -- its own
/// bound when it records predecessors, the parent's bound when a child records a blocking lemma
/// -- and grow on demand (atBound). Growing invalidates references to their elements, so index
/// them where they are used instead of holding on to an element across a DB update.
struct PobInfo {
    /// examinations of this (vertex, formula), summed over every bound
    std::size_t globalCounter = 0;
    /// bound -> examinations at that bound, over every pob object and every boundSafety() call
    std::vector<std::size_t> localCounter;
    /// bound -> over-approximations of the predecessors, collected by BMBP
    std::vector<EdgeVidPredCache> overPredCache;
    /// bound -> under-approximations of the predecessors, i.e. the pobs they became, used by CC-pob
    std::vector<EdgeVidPredCache> underPredCache;
    /// bound -> lemmas that blocked a child of this subgoal, used by CC-lemma; with `globalPobDb`
    /// every bound uses index 0 (SpacerContext::blockingLemmas)
    std::vector<VidPredCache> blockingLemmas;

    template<typename T> static T & atBound(std::vector<T> & perBound, std::size_t bound) {
        if (perBound.size() <= bound) { perBound.resize(bound + 1); }
        return perBound[bound];
    }
};

struct ProofObligationCore {
    SymRef vertex;
    std::size_t bound;
    PTRef constraint;
    bool isMayPO = false;
    mutable std::size_t life = 0; ///< set from SpacerConfig::mayPoGas at construction
    mutable const ProofObligationCore* parent = nullptr;
    mutable bool closed = false;
    /// MayCcLemma / MayBmbp / MayCcPob: which mechanism created the root of this pob's may subtree.
    /// Descendants are ordinary MBP predecessors, so they inherit the root's source.
    mutable LemmaOriginMask maySource = LemmaOrigin::None;
    /// true only for the pob a CC-lemma / BMBP / CC-pob block created directly.
    mutable bool mayRoot = false;
    /// For a CC root only: the pob whose CC block created it, and for CC-pob the edge source, i.e.
    /// where the formulas its hull was built from are kept (SpacerContext::updateCcInputs). Keys,
    /// not a reference: the creator may be gone, and the per-bound vectors of PobInfo may grow.
    struct CcOrigin {
        SymRef creatorVertex;
        PTRef creatorFormula;
        std::size_t creatorBound;
        EId edge;
        std::size_t sourceIndex;
    };
    mutable std::optional<CcOrigin> ccOrigin;
};

/// Full provenance of a lemma learnt while blocking `pob`: pob type, may source, root flag.
inline LemmaOriginMask lemmaOriginOfPob(ProofObligationCore const & pob) {
    return LemmaOrigin::ofPob(pob.isMayPO) | pob.maySource |
           (pob.mayRoot ? LemmaOrigin::MayRoot : LemmaOrigin::None);
}

using ProofObligation = std::unique_ptr<ProofObligationCore>;

bool operator<(ProofObligation const & pob1, ProofObligation const & pob2) {
    // TODO: Does it make sense to break ties using vertices?
    return pob1->bound < pob2->bound or \
        (pob1->bound == pob2->bound and pob1->isMayPO > pob2->isMayPO) or \
        (pob1->bound == pob2->bound and pob1->isMayPO == pob2->isMayPO \
         and pob1->vertex.x > pob2->vertex.x);
}

// TODO: why we need both operators??
bool operator>(ProofObligation const & pob1, ProofObligation const & pob2) {
    return pob1->bound > pob2->bound or \
        (pob1->bound == pob2->bound and pob1->isMayPO < pob2->isMayPO) or \
        (pob1->bound == pob2->bound and pob1->isMayPO == pob2->isMayPO \
         and pob1->vertex.x < pob2->vertex.x);
}

struct PriorityQueue {

    void push(ProofObligation&& pob) { pqueue.push(std::move(pob)); }
    ProofObligation const & peek() const { return pqueue.top(); }
    void pop() { pqueue.pop(); }
    [[nodiscard]] bool empty() const { return pqueue.empty(); }

private:
    std::priority_queue<ProofObligation, std::vector<ProofObligation>, std::greater<>> pqueue;
};

class DerivationDatabase {
public:
    using ID = std::size_t;
    struct DerivedFact {
        PTRef fact;
        SymRef node;
    };

    [[nodiscard]] ID getIdFor(DerivedFact fact) const;

    struct Entry {
        DerivedFact derivedFact;
        EId incomingEdge;
        std::vector<ID> premises;
    };

    void newDerivation(DerivedFact fact, EId edge, std::vector<ID> premises);

    Entry const & getEntry(ID index) const {
        assert(index < table.size());
        return table.at(index);
    }

    // DEBUG
    void print(Logic & logic) const {
        for (auto const & entry : *this) {
            std::cout << logic.printSym(entry.derivedFact.node) << " " << logic.pp(entry.derivedFact.fact) << " "
                      << entry.incomingEdge.id << " | ";
            for (auto premise : entry.premises) {
                std::cout << premise << " ";
            }
            std::cout << std::endl;
        }
    }

private:
    std::vector<Entry> table;

public:
    using const_iterator = decltype(table)::const_iterator;

    const_iterator begin() const { return table.begin(); }
    const_iterator end() const { return table.end(); }
};

bool operator==(DerivationDatabase::DerivedFact const & first, DerivationDatabase::DerivedFact const & second) {
    return first.node == second.node and first.fact == second.fact;
}

DerivationDatabase::ID DerivationDatabase::getIdFor(DerivationDatabase::DerivedFact fact) const {
    for (std::size_t i = 0u; i < table.size(); ++i) {
        if (table[i].derivedFact == fact) { return i; }
    }
    throw std::logic_error("Given fact not found in the database of derived facts");
}

void DerivationDatabase::newDerivation(DerivationDatabase::DerivedFact fact, EId edge, std::vector<ID> premises) {
    table.push_back({.derivedFact = fact, .incomingEdge = edge, .premises = std::move(premises)});
}

class SpacerContext {
    Logic & logic;
    ChcDirectedHyperGraph const & graph;
    AdjacencyListsGraphRepresentation adjacencyLists;

    UnderApproxMap under;
    OverApproxMap over;

    DerivationDatabase database;
    bool logProof;
    SpacerConfig cfg;

    SpacerStats stats;

    std::size_t lowestChangedLevel = 0;

    // Helper data structures to get the versioning right
    ChcDirectedHyperGraph::VertexInstances vertexInstances;

    /// vertex -> pob formula -> what we know about that subgoal. Never cleared: the point
    /// is that it outlives the per-bound pob objects.  mutable so that computePredecessor,
    /// which is const, can record over-approximations.
    mutable std::unordered_map<SymRef, std::unordered_map<PTRef, PobInfo, PTRefHash>, SymRefHash> pobDb;

    PobInfo & pobInfo(SymRef vid, PTRef formula) const { return pobDb[vid][formula]; }

    /// The lemmas that blocked a child of (`vid`, `formula`) examined at `bound`; with
    /// `globalPobDb` every bound shares one set.
    VidPredCache & blockingLemmas(SymRef vid, PTRef formula, std::size_t bound) const {
        return PobInfo::atBound(pobInfo(vid, formula).blockingLemmas, cfg.globalPobDb ? 0 : bound);
    }

    /// A CC root was found reachable, ran out of gas, or was blocked: rewrite the formulas its hull
    /// came from. Reachable or EOL (`blockingLemma` undefined): every hull of a superset contains
    /// this one, so keep only the newest formula and let the list grow again. Blocked: replace them
    /// by the lemma that blocked the root, whose negation contains the hull with fewer literals, so
    /// the next hull starts from that region instead of from scratch. Either way one formula is
    /// left, and both CC loops need at least two, so an unchanged list stops re-creating the root.
    void updateCcInputs(ProofObligationCore const & root, PTRef blockingLemma, char const * fate) const {
        if (not cfg.ccUpdate or not root.isMayPO or not root.mayRoot or not root.ccOrigin) { return; }
        auto const & origin = *root.ccOrigin;
        bool const fromLemmas = root.maySource == LemmaOrigin::MayCcLemma;
        OrderedFormulas & inputs =
            fromLemmas ? blockingLemmas(origin.creatorVertex, origin.creatorFormula, origin.creatorBound)
                             .at(root.vertex)
                       : PobInfo::atBound(pobInfo(origin.creatorVertex, origin.creatorFormula).underPredCache,
                                          origin.creatorBound)
                             .at(origin.edge, origin.sourceIndex);
        TRACE(1, (fromLemmas ? "[CC]" : "[CC-POB]") << " Root " << root.constraint.x << " " << fate << ": "
              << (blockingLemma == PTRef_Undef ? "kept the newest of " : "replaced by the blocking lemma ")
              << inputs.size() << " inputs");
        if (blockingLemma == PTRef_Undef) {
            inputs.keepOnlyNewest();
            return;
        }
        // Lemmas are summaries in base form, and CC-lemma hulls their negations; CC-pob hulls pob
        // constraints, i.e. target formulas, so it gets the blocked region not(lemma) as a target.
        inputs.replaceWith(fromLemmas ? blockingLemma
                                      : VersionManager(logic).baseFormulaToTarget(logic.mkNot(blockingLemma)));
    }

    void addMaySummary(SymRef vid, std::size_t bound, PTRef summary,
                       LemmaOriginMask origin = LemmaOrigin::None) {
        over.insert(vid, bound, summary);
        LemmaOriginMask const clash = over.recordOrigin(vid, summary, origin);
        if (clash != LemmaOrigin::None) {
            TRACE(1, "[!] Lemma " << summary.x << " for " << vid.x << " rediscovered as "
                  << lemmaOriginToString(origin) << ", keeping first origin "
                  << lemmaOriginToString(clash));
        }
    }

    bool checkValidityWitness(ValidityWitness::definitions_t const & definitions) const {
        VersionManager versionManager(logic);
        for (auto const & edge : graph.getEdges()) {
            EId eid = edge.id;
            auto const & sources = graph.getSources(eid);
            auto target = graph.getTarget(eid);

            auto getInterpretation = [&](SymRef vid) -> PTRef {
                auto it = definitions.find(vid);
                assert(it != definitions.end());
                return it->second;
            };

            vec<PTRef> bodyComponents;
            bodyComponents.push(graph.getEdgeLabel(eid));
            for (std::size_t i = 0; i < sources.size(); ++i) {
                auto src = sources[i];
                auto instance = vertexInstances.getInstanceNumber(eid, i);
                bodyComponents.push(versionManager.baseFormulaToSource(getInterpretation(src), instance));
            }
            PTRef body = logic.mkAnd(std::move(bodyComponents));
            PTRef versionedTarget = versionManager.baseFormulaToTarget(getInterpretation(target));

            SMTSolver solver(logic);
            solver.assertProp(body);
            solver.assertProp(logic.mkNot(versionedTarget));
            auto res = solver.check();
            if (res != SMTSolver::Answer::UNSAT) {
                std::cerr << "checkValidityWitness failed: edge " << eid.id
                          << " label " << logic.pp(graph.getEdgeLabel(eid))
                          << " from [";
                for (std::size_t i = 0; i < sources.size(); ++i) {
                    if (i > 0) std::cerr << ", ";
                    std::cerr << logic.printSym(sources[i])
                              << " := " << logic.pp(getInterpretation(sources[i]));
                }
                std::cerr << "] to " << logic.printSym(target)
                          << " := " << logic.pp(getInterpretation(target))
                          << " is not satisfied" << std::endl;
                return false;
            }
        }
        return true;
    }

    void addMustSummary(SymRef vid, std::size_t bound, PTRef summary) { under.insert(vid, bound, summary, false); }

    PTRef getMustSummary(SymRef vid, std::size_t bound) const { return logic.mkOr(under.getComponents(vid, bound, false)); }

    PTRef getMaySummary(SymRef vid, std::size_t bound) const { return logic.mkAnd(over.getComponents(vid, bound)); }

    PTRef getEdgeMustSummary(EId eid, std::size_t bound) const;

    PTRef getEdgeTransition(EId eid, std::vector<GuardVar>& guadVars) const;

    PTRef getGuardedMaySummary(const std::vector<GuardVar>& guards, std::size_t bound) const;
    PTRef getGuardedMaySummary(const GuardVar& guard, std::size_t bound) const;

    PTRef getEdgeMaySummary(EId eid, std::size_t bound) const;

    // For debugging
    PTRef getEdgeMaySummaryWithNewLemma(EId eid, std::size_t bound, SymRef v, PTRef lemma) const;

    PTRef getEdgeMixedSummary(EId eid, std::size_t bound, std::size_t lastMayIndex) const;

    PTRef getEdgeMustOnlySummary(EId eid, std::size_t bound, std::size_t lastMayIndex) const;

    bool checkNewLemma(SymRef v, std::size_t bound, PTRef lemma) const;

    std::vector<EId> const & incomingEdges(SymRef v) const;

    enum class BoundedSafetyResult { SAFE, UNSAFE };

    BoundedSafetyResult boundSafety(std::size_t currentBound);

    enum class InductiveCheckAnswer { INDUCTIVE, NOT_INDUCTIVE };

    struct InductiveCheckResult {
        InductiveCheckAnswer answer;
        std::size_t inductiveLevel;
    };

    InductiveCheckResult isInductive(std::size_t);

    bool tryPushComponents(SymRef, std::size_t, PTRef);

    enum class QueryAnswer : char { UNKNOWN, SAT, UNSAT, ERROR };
    struct QueryResult {
        QueryAnswer answer;
        std::unique_ptr<Model> model;
    };
    QueryResult sat(PTRef A, PTRef B) const;


    struct ItpQueryResult {
        QueryAnswer answer;
        PTRef interpolant = PTRef_Undef;
    };
    ItpQueryResult interpolatingSat(PTRef A, PTRef B);
    ItpQueryResult inductiveItp(PTRef maySumm, PTRef trans, const std::vector<GuardVar>& guardVariables, PTRef phi);

    PTRef inductiveConflict(PTRef maySumm, PTRef trans, const std::vector<GuardVar>& guardVariables, PTRef phi);

    PTRef generalize(PTRef lemma, PTRef maySumm, PTRef transitions, const std::vector<GuardVar>& guardVariables);

    PTRef generalize_down(PTRef lemma, PTRef maySumm, PTRef transitions,
                          const std::vector<GuardVar>& guardVariables);

    PTRef tryBlockWithRelativeInductionBool(ProofObligationCore const & pob) const;

    PTRef tryBlockWithRelativeInduction(ProofObligationCore const & pob) const;

    bool checkMustReachability(std::vector<EId> const & edges, ProofObligationCore const & pob);

    bool mayReachable(EId eid, PTRef targetConstraint, std::size_t bound) const;

    ProofObligation computePredecessor(EId eid, ProofObligationCore const & pob) const;

    PTRef projectFormula(PTRef fla, vec<PTRef> const & vars, Model & model) const;

    std::pair<PTRef, PTRef> projectFormulaWithOver(PTRef fla, vec<PTRef> const & vars, Model & model) const;

    void logNewFactIntoDatabase(PTRef fact, SymRef vertex, std::size_t sourceLevel, EId eid, Model & model);

    InvalidityWitness reconstructInvalidityWitness() const;

public:
    SpacerContext(Logic & logic, ChcDirectedHyperGraph const & graph, bool logProof, SpacerConfig cfg);

    VerificationResult run();
};

VerificationResult Spacer::solve(ChcDirectedHyperGraph const & system) {
    if (logic.hasArrays()) { return VerificationResult{VerificationAnswer::UNKNOWN}; }
    bool logProof =
        options.hasOption(Options::COMPUTE_WITNESS) and options.getOption(Options::COMPUTE_WITNESS) == "true";
    return SpacerContext(logic, system, logProof, SpacerConfig::from(options)).run();
}

SpacerContext::SpacerContext(Logic & logic, ChcDirectedHyperGraph const & graph, bool logProof, SpacerConfig cfg)
    : logic(logic),
      graph(graph),
      adjacencyLists(AdjacencyListsGraphRepresentation::from(graph)),
      logProof(logProof),
      cfg(cfg),
      vertexInstances(graph) {
    this->cfg.validate();
    auto vertices = graph.getVertices();
    for (auto vid : vertices) {
        PTRef toInsert = vid == graph.getEntry() ? logic.getTerm_true() : logic.getTerm_false();
        addMaySummary(vid, 0, toInsert);
        addMustSummary(vid, 0, toInsert);
    }
    database.newDerivation({.fact = logic.getTerm_true(), .node = graph.getEntry()}, {static_cast<std::size_t>(-1)},
                           {});
}

VerificationResult SpacerContext::run() {
    std::size_t currentBound = 1;
    while (true) {
        addMaySummary(graph.getEntry(), currentBound, logic.getTerm_true());
        addMustSummary(graph.getEntry(), currentBound, logic.getTerm_true());
        TRACE(1, "Checking bound safety for " << currentBound)
        auto boundedResult = boundSafety(currentBound);
        switch (boundedResult) {
            case BoundedSafetyResult::UNSAFE:
                stats.print();
                return {VerificationAnswer::UNSAFE, reconstructInvalidityWitness()};
            case BoundedSafetyResult::SAFE: {
                auto inductiveResult = isInductive(currentBound);
                if (inductiveResult.answer == InductiveCheckAnswer::INDUCTIVE) {
                    ValidityWitness::definitions_t solution{{graph.getEntry(), logic.getTerm_true()},
                                                            {graph.getExit(), logic.getTerm_false()}};
                    auto inductiveLevel = inductiveResult.inductiveLevel;
                    for (auto vid : graph.getVertices()) {
                        if (vid == graph.getEntry() or vid == graph.getExit()) { continue; }
                        PTRef invariantSummary = logic.mkAnd(over.getComponents(vid, inductiveLevel));
                        if (logic.isOr(invariantSummary) or logic.isAnd(invariantSummary)) {
                            invariantSummary = simplifyUnderAssignment_Aggressive(invariantSummary, logic);
                        }
                        auto insertRes = solution.insert(std::make_pair(vid, invariantSummary));
                        assert(insertRes.second);
                        if (not insertRes.second) {
                            throw std::logic_error("Duplicate definition for a predicate encountered!");
                        }
                    }
                    if (not checkValidityWitness(solution)) {
                        throw std::logic_error("Error: wrong witness!");
                    }
                    stats.print();
                    return {VerificationAnswer::SAFE, ValidityWitness(std::move(solution))};
                }
                ++currentBound;
                stats.setBound(currentBound);
                stats.print();
                break;
            }
            default:
                assert(false);
                throw std::logic_error("Unreachable!");
        }
    }
}

std::vector<EId> const & SpacerContext::incomingEdges(SymRef v) const {
    return adjacencyLists.getIncomingEdgesFor(v);
}

bool SpacerContext::checkNewLemma(SymRef v, std::size_t bound, PTRef lemma) const {
    const auto& edges = incomingEdges(v);
    vec<PTRef> maySummaries;
    for (auto eid : edges) {
        maySummaries.push(getEdgeMaySummaryWithNewLemma(eid, bound, v, lemma));
    }
    PTRef edgeTransitions = logic.mkOr(maySummaries);
    PTRef lemmaPrime = VersionManager(logic).baseFormulaToTarget(lemma);
    SMTSolver debug_solver(logic);
    debug_solver.assertProp(edgeTransitions);
    debug_solver.assertProp(logic.mkNot(lemmaPrime));
    return debug_solver.check() == SMTSolver::Answer::UNSAT;
 }

SpacerContext::BoundedSafetyResult SpacerContext::boundSafety(std::size_t currentBound) {
    TRACE(1, "\n\n++++++++++++++++++++++++++++++++\n\nRunning bounded safety check at level " << currentBound)
    auto query = graph.getExit();
    PriorityQueue pqueue;
    ProofObligation goal = \
        ProofObligation(new ProofObligationCore{query, currentBound, logic.getTerm_true(), false});
    goal->life = cfg.mayPoGas;
    pqueue.push(std::move(goal));
    lowestChangedLevel = currentBound;
    // One line per may-pob exit, so the fate of every may-pob is greppable instead of
    // having to be reconstructed from the surrounding trace.
    auto traceMayFate = [this](ProofObligationCore const & p, char const * fate) {
        if (not p.isMayPO) { return; }
        TRACE(1, "[MAYPO] id=" << p.constraint.x
              << " src=" << lemmaOriginToString(p.maySource)
              << (p.mayRoot ? " root" : " desc")
              << " lvl=" << p.bound << " life=" << p.life
              << " visits=" << PobInfo::atBound(pobInfo(p.vertex, p.constraint).localCounter, p.bound)
              << "/" << pobInfo(p.vertex, p.constraint).globalCounter
              << " atoms=" << TermUtils(logic).getTopLevelConjuncts(p.constraint).size()
              << " fate=" << fate);
    };
    while (not pqueue.empty()) {
        assert(pqueue.peek());
        ProofObligationCore const & pob = *(pqueue.peek());

        if (pob.closed or (pob.isMayPO and pob.bound == 0)) {
            traceMayFate(pob, pob.closed ? "CLOSED" : "LEVEL0");
            pqueue.pop();
            continue;
        }

        PobInfo & info = pobInfo(pob.vertex, pob.constraint);
        ++info.globalCounter;
        std::size_t const visits = ++PobInfo::atBound(info.localCounter, pob.bound);
        TRACE(1, "[?] Examining "
              << ((pob.isMayPO) ? "MAY" : "MUST") << " PO " << pob.constraint.x
              << " at level " << pob.bound
              << " with life " << pob.life);
        TRACE(2, " proof obligation " << logic.printTerm(pob.constraint))

        if (pob.vertex == graph.getEntry() and not pob.isMayPO) {
            assert(false); // With the must summaries, we actually never finish here
            return BoundedSafetyResult::UNSAFE;
        }
        auto const & edges = incomingEdges(pob.vertex);
        bool mustReached = checkMustReachability(edges, pob);
        if (mustReached) {
            if (pob.vertex == query and not pob.isMayPO) {
                return BoundedSafetyResult::UNSAFE; // query is reachable
            }
            traceMayFate(pob, "REACHABLE");
            updateCcInputs(pob, PTRef_Undef, "reachable");
            pqueue.pop();
            continue;
        }
 
        std::vector<ProofObligation> newProofObligations;
        bool has_predecessors = false;
        for (EId edgeId : edges) {
            ProofObligation npob = computePredecessor(edgeId, pob);
            if (npob) {
                has_predecessors = true;
                if (npob->life > 0) {
                    newProofObligations.push_back(std::move(npob));
                }
            }
        }
        if (has_predecessors and newProofObligations.empty()) {
            assert(pob.isMayPO);
            assert(pob.parent != &pob);
            // all predecessors of a may pob had 0 life.
            TRACE(1, "    Removing MayPO branch due to EOL");
            traceMayFate(pob, "EOL");
            // The chain ran out of gas: its CC root, this pob or one of its may ancestors, resets
            // the inputs its hull came from.
            updateCcInputs(pob, PTRef_Undef, "EOL");
            if (pob.parent == nullptr) {
                // Without the pop the same pob stays on top of the queue and is re-examined forever.
                pqueue.pop();
                continue;
            }
            const ProofObligationCore* parentPob = pob.parent;
            // close recursively all parents?
            while (parentPob != nullptr and parentPob->isMayPO) {
                parentPob->closed = true;
                updateCcInputs(*parentPob, PTRef_Undef, "EOL");
                parentPob = parentPob->parent;
            }
            pqueue.pop();
            continue;
        }

        // Relative induction is only worth trying when the pob actually HAS predecessors.
        if (cfg.relind and not newProofObligations.empty()) {
            PTRef relindLemma = cfg.relindGrow ? tryBlockWithRelativeInduction(pob)
                                               : tryBlockWithRelativeInductionBool(pob);
            LemmaOriginMask RelIndVariant =
                cfg.relindGrow ? LemmaOrigin::RelIndGrow : LemmaOrigin::RelInd;
            if (relindLemma != PTRef_Undef) {
                if (not checkNewLemma(pob.vertex, pob.bound - 1, relindLemma)) {
                    throw std::logic_error("After RelInd, newLemma is not consistent with edeges!");
                }
                TRACE(1, "[RELIND] Spared POBS: " << newProofObligations.size());
                TRACE(2, " New lemma : " << logic.pp(relindLemma));
                addMaySummary(pob.vertex, pob.bound, relindLemma,
                              RelIndVariant | lemmaOriginOfPob(pob));
                if (pob.parent != nullptr) {
                    blockingLemmas(pob.parent->vertex, pob.parent->constraint, pob.parent->bound)
                        .insert(pob.vertex, relindLemma, cfg.maxLemmasForCc);
                }
                if (pob.isMayPO) {
                    TRACE(1, "    $$$$$$$$$$$$ MAY PO WAS BLOCKED $$$$$$$$$$$$");
                }
                if (pob.bound < lowestChangedLevel) { lowestChangedLevel = pob.bound; }
                TRACE(1, "[x] Blocked POB with new lemma at level " << pob.bound);
                traceMayFate(pob, "BLOCKED_RELIND");
                updateCcInputs(pob, relindLemma, "blocked");
                pqueue.pop();
                continue;
            }
        }

        // [MayPO] Collect MayPO as a convex over-approximation of the predecessors
        std::vector<ProofObligation> newMayPO;
        ConvexClosure convexClosure(logic);
        // Two triggers, one per kind of evidence. BMBP and CC-pob read the predecessor caches of
        // this bound, so they trigger on the visits at this bound. CC-lemma reads the blocking
        // lemmas, which `globalPobDb` shares across bounds; with it on, it triggers on the visits
        // over every bound.
        bool const lastVisit = cfg.mayPobOnLastVisit and newProofObligations.empty();
        bool const predsReady = lastVisit or visits >= cfg.triggerMayPo;
        bool const lemmasReady =
            lastVisit or (cfg.globalPobDb ? info.globalCounter : visits) >= cfg.triggerMayPo;
        if (cfg.maypo) {

            if (cfg.bmbp and predsReady) {
            // Bidirectional Model based projection
            EdgeVidPredCache const & overPreds = PobInfo::atBound(info.overPredCache, pob.bound);
            for (auto it = overPreds.begin(cfg.minBmbpOverLits); it != overPreds.end(); ++it) {
                ProofObligation mayPred(new ProofObligationCore{it.getNode(graph),
                                                                pob.bound - 1,
                                                                logic.mkAnd(it.getApprox()),
                                                                true});
                // do not remember parent if the parent will be removed from the queue
                // TODO: use shared pointers instead
                mayPred->parent = (newProofObligations.empty()) ? nullptr : &pob;
                mayPred->life = pob.life - 1;
                mayPred->maySource = LemmaOrigin::MayBmbp;
                mayPred->mayRoot = true;
                if (mayPred->life > 0)
                    newMayPO.push_back(std::move(mayPred));
            }
            }

            if (cfg.ccLemma and lemmasReady) {
            // Convex Closure of blocking lemmas
            VidPredCache const & lemmas = blockingLemmas(pob.vertex, pob.constraint, pob.bound);
            for (auto it = lemmas.begin(cfg.minLemmasForCc); it != lemmas.end(); ++it) {
                vec<PTRef> negatedLemmas;
                for (PTRef lemma : it.getApprox()) {
                    negatedLemmas.push(logic.mkNot(lemma));
                }
                PTRef mayConstraint = convexClosure.getConvexClosure(negatedLemmas);
                if (logic.isTrue(mayConstraint) or logic.isFalse(mayConstraint)) {
                    continue;
                }
                // Blocking lemmas are summaries, stored in base form; a pob constraint must be a
                // target formula.
                mayConstraint = VersionManager(logic).baseFormulaToTarget(mayConstraint);
                TRACE(1, "[CC] Adding a ConvexClosure of " << negatedLemmas.size() << " lemmas"
         << " -> atoms: " << TermUtils(logic).getTopLevelConjuncts(mayConstraint).size()
         << " vars: " << TermUtils(logic).getVars(mayConstraint).size());
                TRACE(2, "[CC] Added " << logic.pp(mayConstraint));
                TRACE(2, "[CC] Blocking:" << std::endl;
                      for (auto lemma : negatedLemmas) {
                          std::cout << logic.pp(lemma) << std::endl;}
                      std::cout);
                ProofObligation mayPred(new ProofObligationCore{it.getNode(), pob.bound - 1, mayConstraint, true});
                mayPred->parent = (newProofObligations.empty()) ? nullptr : &pob;
                mayPred->life = pob.life - 1;
                mayPred->maySource = LemmaOrigin::MayCcLemma;
                mayPred->mayRoot = true;
                mayPred->ccOrigin = ProofObligationCore::CcOrigin{pob.vertex, pob.constraint, pob.bound, EId{0}, 0};
                if (mayPred->life > 0)
                    newMayPO.push_back(std::move(mayPred));
            }
            }

            if (cfg.ccPob and predsReady) {
            // Convex Closure of the under-approximations of the predecessors, i.e. of the pobs
            // they became. These are pob constraints already, so they are target formulas.
            EdgeVidPredCache const & underPreds = PobInfo::atBound(info.underPredCache, pob.bound);
            for (auto it = underPreds.begin(cfg.minPobsForCc); it != underPreds.end(); ++it) {
                vec<PTRef> underPobs = it.getApprox();
                PTRef mayConstraint = convexClosure.getConvexClosure(underPobs);
                if (logic.isTrue(mayConstraint) or logic.isFalse(mayConstraint)) {
                    continue;
                }
                TRACE(1, "[CC-POB] Adding a ConvexClosure of " << underPobs.size() << " pobs"
                      << " -> atoms: " << TermUtils(logic).getTopLevelConjuncts(mayConstraint).size()
                      << " vars: " << TermUtils(logic).getVars(mayConstraint).size());
                TRACE(2, "[CC-POB] Added " << logic.pp(mayConstraint));
                TRACE(2, "[CC-POB] Pobs:" << std::endl;
                      for (auto underPob : underPobs) {
                          std::cout << logic.pp(underPob) << std::endl;}
                      std::cout);
                ProofObligation mayPred(new ProofObligationCore{it.getNode(graph), pob.bound - 1, mayConstraint, true});
                mayPred->parent = (newProofObligations.empty()) ? nullptr : &pob;
                mayPred->life = pob.life - 1;
                mayPred->maySource = LemmaOrigin::MayCcPob;
                mayPred->mayRoot = true;
                mayPred->ccOrigin = ProofObligationCore::CcOrigin{pob.vertex, pob.constraint, pob.bound,
                                                                  it.getEdge(), it.getSourceIndex()};
                if (mayPred->life > 0)
                    newMayPO.push_back(std::move(mayPred));
            }
            }
        }

        if (newProofObligations.empty()) {
            // all edges are blocked; compute new lemma blocking the current proof obligation

            vec<PTRef> edgeRepresentations;
            edgeRepresentations.capacity(edges.size());
            std::vector<GuardVar> sourceGuards;
            for (EId eid : edges) {
                edgeRepresentations.push(getEdgeTransition(eid, sourceGuards));
            }
            PTRef transitions = logic.mkOr(std::move(edgeRepresentations));
            PTRef maySummary = getGuardedMaySummary(sourceGuards, pob.bound - 1);

            PTRef edgesMaySummary = logic.mkAnd(maySummary, transitions);

            std::vector<GuardVar> inductiveSources;
            for (const auto& sourceGuard : sourceGuards) {
                if (sourceGuard.vertex == pob.vertex) {
                    inductiveSources.push_back(sourceGuard);
                }
            }

            PTRef newLemma = PTRef_Undef;

            PTRef originalNewLemma = PTRef_Undef;

            bool const ccRoot = pob.isMayPO and pob.mayRoot and
                                (pob.maySource == LemmaOrigin::MayCcLemma or
                                 pob.maySource == LemmaOrigin::MayCcPob);
            if (ccRoot and cfg.generalize) {
                // do not interpolate something that is already generalized
                // let inductive generalization handle it.
                // Only the CC root (CC-lemma or CC-pob) is a convex closure; its descendants are
                // ordinary MBP predecessors (possibly with divisibility constraints) and are
                // interpolated.
                // not(pob) is built facet by facet as plain integer inequalities, the shape of an
                // interpolant's atoms, so e.g. not(1 <= y - 2x) and 0 <= 2x - y are the same lemma.
                LATermUtils latUtils(dynamic_cast<ArithLogic &>(logic));
                vec<PTRef> negatedFacets;
                for (PTRef facet : TermUtils(logic).getTopLevelConjuncts(pob.constraint)) {
                    negatedFacets.push(latUtils.negateIntLiteral(facet));
                }
                newLemma = VersionManager(logic).targetFormulaToBase(logic.mkOr(std::move(negatedFacets)));
                newLemma =
                    cfg.gdown
                    ? generalize_down(newLemma, maySummary, transitions, inductiveSources)
                    : generalize(newLemma, maySummary, transitions, inductiveSources);
                TRACE(1,
                      "---- " << (pob.maySource == LemmaOrigin::MayCcPob ? "[CC-POB]" : "[CC]")
                      << " Generalization: " << newLemma.x
                      << " nr disj: " << TermUtils(logic).getTopLevelDisjuncts(newLemma).size()
                      << " nr vars: " << TermUtils(logic).getVars(newLemma).size());
                TRACE(2,
                      "Lemma for " << pob.vertex.x << " at level " << pob.bound << " - "
                      << logic.pp(newLemma));
                addMaySummary(pob.vertex, pob.bound, newLemma, pob.maySource);

            } else if (cfg.interpolation) {
                auto originalRes = interpolatingSat(edgesMaySummary, pob.constraint);
                originalNewLemma = VersionManager(logic).targetFormulaToBase(originalRes.interpolant);
                assert(originalRes.answer == QueryAnswer::UNSAT);
                if (originalRes.answer != QueryAnswer::UNSAT) {
                    throw std::logic_error("All edges should have been blocked, but they are not!");
                }
                TRACE(1,
                      "---- [ITP] Learnt lemma: " << originalNewLemma.x 
                      << " nr disj: " << TermUtils(logic).getTopLevelDisjuncts(originalNewLemma).size()
                      << " nr vars: " << TermUtils(logic).getVars(originalNewLemma).size());

                if (cfg.generalize) {
                    originalNewLemma =
                        cfg.gdown
                        ? generalize_down(originalNewLemma, maySummary, transitions, inductiveSources)
                        : generalize(originalNewLemma, maySummary, transitions, inductiveSources);
                    TRACE(1,
                          "---- [ITP] Generalization: " << originalNewLemma.x
                          << " nr disj: " << TermUtils(logic).getTopLevelDisjuncts(originalNewLemma).size()
                          << " nr vars: " << TermUtils(logic).getVars(originalNewLemma).size());
                }
                TRACE(2,
                      "Lemma for " << pob.vertex.x << " at level " << pob.bound << " - "
                      << logic.pp(originalNewLemma));

                if (not checkNewLemma(pob.vertex, pob.bound - 1, originalNewLemma)) {
                    throw std::logic_error("After generalization, originalNewLemma is not consistent with edeges!");
                }

                newLemma = originalNewLemma;
                addMaySummary(pob.vertex, pob.bound, newLemma,
                              LemmaOrigin::Itp | lemmaOriginOfPob(pob));
            }

            if (cfg.indConflict) {
                auto indRes = inductiveItp(maySummary, transitions, inductiveSources, pob.constraint);
                assert(indRes.answer == QueryAnswer::UNSAT);
                if (indRes.answer != QueryAnswer::UNSAT) {
                    throw std::logic_error("All edges should have been blocked, but they are not!");
                }
                auto indNewLemma = indRes.interpolant;

                // Add the new ind Lemma
                TRACE(1,
                      "---- [IND] Learnt lemma: " << indNewLemma.x 
                      << " nr disj: " << TermUtils(logic).getTopLevelDisjuncts(indNewLemma).size()
                      << " nr vars: " << TermUtils(logic).getVars(indNewLemma).size());

                if (not checkNewLemma(pob.vertex, pob.bound - 1, indNewLemma)) {
                    throw std::logic_error("indNewLemma is not consistent with edeges!");
                }

                indNewLemma = cfg.gdown
                    ? generalize_down(indNewLemma, maySummary, transitions, inductiveSources)
                    : generalize(indNewLemma, maySummary, transitions, inductiveSources);
                TRACE(1,
                      "---- [IND] Generalization: " << indNewLemma.x
                      << " nr disj: " << TermUtils(logic).getTopLevelDisjuncts(indNewLemma).size()
                      << " nr vars: " << TermUtils(logic).getVars(indNewLemma).size());
                TRACE(2,
                      "Lemma for " << pob.vertex.x << " at level " << pob.bound << " - "
                      << logic.pp(indNewLemma));

                if (not checkNewLemma(pob.vertex, pob.bound - 1, indNewLemma)) {
                    throw std::logic_error("After generalization, indNewLemma is not consistent with edeges!");
                }

                newLemma = indNewLemma;
                addMaySummary(pob.vertex, pob.bound, newLemma,
                              LemmaOrigin::IndItp | lemmaOriginOfPob(pob));

                if (cfg.interpolation) {
                    bool strongerOldLemma = not implies(originalNewLemma, indNewLemma, logic);
                    if (strongerOldLemma)
                        TRACE(1, ">>>> NEWLEMMA IS STRONGER OR INCOMPARABLE ");
                }
            }

            if (pob.parent != nullptr) {
                blockingLemmas(pob.parent->vertex, pob.parent->constraint, pob.parent->bound)
                    .insert(pob.vertex, newLemma, cfg.maxLemmasForCc);
            }

            if (pob.bound < lowestChangedLevel) { lowestChangedLevel = pob.bound; }

            if (pob.isMayPO) {
                TRACE(1, "    $$$$$$$$$$$$ MAY PO WAS BLOCKED $$$$$$$$$$$$");
            }
            TRACE(1, "[x] Blocked POB with new lemma at level " << pob.bound);
            traceMayFate(pob, "BLOCKED");
            updateCcInputs(pob, newLemma, "blocked");
            pqueue.pop(); // This POB has been successfully blocked

        } else {
            traceMayFate(pob, "SPAWNED");
            for (auto & npob : newProofObligations) {
                TRACE(1, "[+] MUST PRED: Adding new "
                      << (npob->isMayPO ? "MAY" : "MUST") << " PO "
                      << npob->constraint.x << " at level " << npob->bound);
                TRACE(3, "Pushing new proof obligation " << logic.pp(npob->constraint) << " for " << npob->vertex.x
                      << " at level " << npob->bound);
                pqueue.push(std::move(npob));
            }
        }
        for (auto & npob : newMayPO) {
            TRACE(1, "[+] MAY PRED: Adding new MAY PO " << npob->constraint.x << " at level " << npob->bound);
            pqueue.push(std::move(npob));
        }
    } // end of main cycle
    return BoundedSafetyResult::SAFE; // not reachable at this bound
}

SpacerContext::QueryResult SpacerContext::sat(PTRef A, PTRef B) const {
    QueryResult qres;
    if (A == logic.getTerm_false()) {
        qres.answer = QueryAnswer::UNSAT;
        return qres;
    }
    SMTSolver solver(logic);
    solver.assertProp(A);
    solver.assertProp(B);
    auto res = solver.check();
    if (res == SMTSolver::Answer::SAT) {
        qres.answer = QueryAnswer::SAT;
        qres.model = solver.getModel();
    } else if (res == SMTSolver::Answer::UNSAT) {
        qres.answer = QueryAnswer::UNSAT;
    } else if (res == SMTSolver::Answer::UNKNOWN) {
        qres.answer = QueryAnswer::UNKNOWN;
    } else if (res == SMTSolver::Answer::ERROR) {
        qres.answer = QueryAnswer::ERROR;
    } else {
        assert(false);
        throw std::logic_error("Unreachable code!");
    }
    return qres;
}

SpacerContext::ItpQueryResult SpacerContext::interpolatingSat(PTRef A, PTRef B) {
    SMTSolver solver(logic, SMTSolver::WitnessProduction::ONLY_INTERPOLANTS);
    solver.getConfig().setSimplifyInterpolant(4);
    solver.assertProp(A);
    solver.assertProp(B);
    auto res = solver.check();
    ItpQueryResult qres;
    if (res == SMTSolver::Answer::SAT) {
        qres.answer = QueryAnswer::SAT;
    } else if (res == SMTSolver::Answer::UNSAT) {
        qres.answer = QueryAnswer::UNSAT;
        auto itpCtx = solver.getInterpolationContext();
        std::vector<PTRef> itps;
        ipartitions_t mask = 1;
        itpCtx->getSingleInterpolant(itps, mask);
        qres.interpolant = itps[0];
    } else if (res == SMTSolver::Answer::UNKNOWN) {
        qres.answer = QueryAnswer::UNKNOWN;
    } else if (res == SMTSolver::Answer::ERROR) {
        qres.answer = QueryAnswer::ERROR;
    } else {
        assert(false);
        throw std::logic_error("Unreachable code!");
    }
    return qres;
}

PTRef SpacerContext::inductiveConflict(PTRef maySummary, PTRef transition, const std::vector<GuardVar>& guardVariables, PTRef phi) {
    TermUtils termUtils(logic);

    ModelBasedProjection mbp_solver(logic);

    SMTSolver cti_solver(logic, SMTSolver::WitnessProduction::ONLY_MODEL);
    cti_solver.assertProp(maySummary);
    cti_solver.assertProp(transition);

    vec<PTRef> xsPrime = termUtils.getVars(phi);
    vec<PTRef> xs;
    // TODO this could be improved
    for (PTRef var : termUtils.getVars(logic.mkAnd(maySummary, transition))) {
        if (std::find(xsPrime.begin(), xsPrime.end(), var) == xsPrime.end()) {
            xs.push(var);
        }
    }

    // TODO: incrementality
    auto get_local_unsatcore = [&](PTRef mbp) -> std::pair<PTRef, PTRef> {
        SMTSolver itp_solver(logic, SMTSolver::WitnessProduction::ONLY_UNSAT_CORE);
        itp_solver.assertProp(phi);
        int counter = 0;
        for (auto conj : termUtils.getTopLevelConjuncts(mbp)) {
            itp_solver.tryAssertNamedProp(conj, std::to_string(counter++));
        }
        // itp_solver.push();
        // std::cerr << "ITP(mbp, B) with mbp := " << logic.printTerm(mbp) << std::endl;
        auto res = itp_solver.check();
        if (res != SMTSolver::Answer::UNSAT) {
            throw std::logic_error("Error in UCORE: result is not unsatisfiable.");
        }
        auto core = itp_solver.getUnsatCore();
        const auto& terms = core->getTerms();
        // vec<PTRef> negatedTerms;
        // negatedTerms.capacity(terms.size());
        // for (PTRef term : terms) { negatedTerms.push(logic.mkNot(term)); }
        // auto interpolantPrime = logic.mkOr(negatedTerms);
        auto interpolantPrime = logic.mkAnd(terms);
        auto interpolant = VersionManager(logic).targetFormulaToBase(interpolantPrime);

        // assert(is_clause(is_clause, interpolant));
        // itp_solver.pop();
        return {interpolant, interpolantPrime};
    };

    // TODO: incrementality
    auto get_local_itp = [&](PTRef mbp) -> std::pair<PTRef, PTRef> {
        SMTSolver itp_solver(logic, SMTSolver::WitnessProduction::ONLY_INTERPOLANTS);
        itp_solver.getConfig().setSimplifyInterpolant(4);
        itp_solver.assertProp(mbp);
        itp_solver.assertProp(phi);
        // itp_solver.push();
        // std::cerr << "ITP(mbp, B) with mbp := " << logic.printTerm(mbp) << std::endl;
        auto res = itp_solver.check();
        if (res != SMTSolver::Answer::UNSAT) {
            throw std::logic_error("Error in ITP: result is not unsatisfiable.");
        }
        auto itpCtx = itp_solver.getInterpolationContext();
        std::vector<PTRef> itps;
        ipartitions_t mask = 1;
        itpCtx->getSingleInterpolant(itps, mask);
        PTRef interpolantPrime = itps[0];
        PTRef interpolant = VersionManager(logic).targetFormulaToBase(interpolantPrime);
        // auto ok = is_clause(logic, interpolant);
        // assert(is_clause(is_clause, interpolant));
        // itp_solver.pop();
        return {interpolant, interpolantPrime};
    };

    auto lemma = logic.getTerm_false();
    auto interpolantPrime = logic.getTerm_false();

    do {
        cti_solver.assertProp(logic.mkNot(interpolantPrime));

        cti_solver.push();
        for (const auto& guard : guardVariables) {
            cti_solver.assertProp(logic.mkImpl(guard.get(logic),
                                               VersionManager(logic).baseFormulaToSource(lemma, guard.instance)));
        }
        // cti_solver.assertProp(logic.mkNot(interpolantPrime));
        // TODO: exploit incrementality
        auto res = cti_solver.check();
        if (res == SMTSolver::Answer::UNSAT) { break; }
        if (res != SMTSolver::Answer::SAT) {
            throw std::logic_error("Error in looking for CTIs.");
        }
        auto cti = cti_solver.getModel();
        PTRef implicant = mbp_solver.getModelBasedImplicant(logic.mkAnd(maySummary, transition), xs, *cti);
        auto pair = get_local_itp(implicant);
        // PTRef mbp = mbp_solver.keepOnly(logic.mkAnd(maySummary, transition), xsPrime, *cti);
        // auto pair = get_local_unsatcore(mbp);
        lemma = logic.mkOr(lemma, pair.first);
        // auto pair = get_local_itp(logic.mkOr(interpolantPrime, implicant));
        // lemma = pair.first;
        interpolantPrime = pair.second;
        cti_solver.pop();
    } while (true);

    if (logic.isAnd(lemma) or logic.isOr(lemma)) {
        lemma = ::rewriteMaxArityAggresive(logic, lemma);
        lemma = ::simplifyUnderAssignment_Aggressive(lemma, logic);
    }

    return lemma; 
}

SpacerContext::ItpQueryResult SpacerContext::inductiveItp(PTRef maySummary,
                                                          PTRef transition,
                                                          const std::vector<GuardVar>& guardVariables,
                                                          PTRef phi) {
    SMTSolver solver(logic, SMTSolver::WitnessProduction::ONLY_INTERPOLANTS);
    solver.getConfig().setSimplifyInterpolant(4);
    solver.assertProp(maySummary);
    solver.assertProp(transition);
    solver.assertProp(phi);
    auto res = solver.check();
    ItpQueryResult qres;
    if (res == SMTSolver::Answer::SAT) {
        qres.answer = QueryAnswer::SAT;
    } else if (res == SMTSolver::Answer::UNSAT) {
        qres.answer = QueryAnswer::UNSAT;
        qres.interpolant = inductiveConflict(maySummary, transition, guardVariables, phi);
    } else if (res == SMTSolver::Answer::UNKNOWN) {
        qres.answer = QueryAnswer::UNKNOWN;
    } else if (res == SMTSolver::Answer::ERROR) {
        qres.answer = QueryAnswer::ERROR;
    } else {
        assert(false);
        throw std::logic_error("Unreachable code!");
    }
    return qres;
}

#if 0
PTRef SpacerContext::generalize_frame(PTRef lemma, const vec<PTRef>& frameLemmas, PTRef transition, PTRef guardVariable) {
    SMTSolver solver(logic, SMTSolver::WitnessProduction::ONLY_UNSAT_CORE);
    VersionManager vManager(logic);

    static std::size_t i = 0;
    for (const auto frameLemma : frameLemmas) {
        std::string name = "_frame#indgen#" + std::to_string(i++);
        bool added = solver.tryAssertNamedProp(frameLemma, name);
        assert(added);
    }
    solver.assertProp(transition);

    PTRef source = logic.mkImpl(guardVariable, vManager.baseFormulaToSource(lemma));
    PTRef target = logic.mkNot(vManager.baseFormulaToTarget(lemma));
    solver.assertProp(source);
    solver.assertProp(target);

    auto res = solver.check();
    if (res != SMTSolver::Answer::UNSAT) {
        throw std::logic_error("Error in Generalize: formula is not unsatisfiable!");
    }

    auto core = solver.getUnsatCore();
    vec<PTRef> inductiveDisjs;
    const auto& coreAssumptions = core->getTerms();
    auto newSize = coreAssumptions.size();
    PTRef neededFrameLemmas = logic.mkAnd(coreAssumptions);

    TRACE(1,
          "---- [IND] General frame:"
          << " from : " << frameLemmas.size() << " - to: " << newSize);

    return neededFrameLemmas;
}
#endif

PTRef SpacerContext::generalize(PTRef lemma, PTRef maySumm, PTRef transitions, const std::vector<GuardVar>& guardVariables) {
    SMTSolver solver(logic, SMTSolver::WitnessProduction::ONLY_UNSAT_CORE);
    VersionManager vManager(logic);

    const auto& candidates = TermUtils(logic).getTopLevelDisjuncts(lemma);

    if (candidates.size() == 0 or logic.isConstant(candidates[0])) {
        return lemma;
    }

    vec<PTRef> assumedTargets;
    assumedTargets.capacity(candidates.size());
    std::vector<vec<PTRef>> assumedSources;
    assumedSources.resize(guardVariables.size());
    std::map<PTRef, PTRef> mapping;

    static std::size_t i = 0;
    for (const auto candidate : candidates) {
        std::string name = "_assume#indgen#" + std::to_string(i++);
        PTRef assumption = logic.mkBoolVar(name.c_str());
        mapping[assumption] = candidate;

        for (auto gi = 0; gi < guardVariables.size(); ++gi) {
            const GuardVar& guardVar = guardVariables[gi];
            PTRef source = vManager.baseFormulaToSource(candidate, guardVar.instance);
            assumedSources[gi].push(logic.mkAnd(assumption, source));
        }

        PTRef notTarget = logic.mkNot(vManager.baseFormulaToTarget(candidate));
        assumedTargets.push(logic.mkImpl(assumption, notTarget));

        // std::cerr << logic.pp(assumption) << " := " << logic.pp(candidate) << std::endl;
        bool added = solver.tryAssertNamedProp(assumption, name);
        assert(added);
    }

    vec<PTRef> allSources; allSources.capacity(guardVariables.size());
    for (auto gi = 0; gi < guardVariables.size(); ++gi) {
        const GuardVar& guardVar = guardVariables[gi];
        allSources.push(logic.mkImpl(guardVar.get(logic), logic.mkOr(assumedSources[gi])));
    }
    PTRef source = logic.mkAnd(allSources);
    PTRef target = logic.mkAnd(assumedTargets);

    solver.assertProp(maySumm);
    solver.assertProp(transitions);
    solver.assertProp(source);
    solver.assertProp(target);

    auto res = solver.check();
    if (res != SMTSolver::Answer::UNSAT) {
        throw std::logic_error("Error in Generalize: formula is not unsatisfiable!");
    }

    auto core = solver.getUnsatCore();
    vec<PTRef> inductiveDisjs;
    const auto& coreAssumptions = core->getTerms();
    for (auto term : coreAssumptions) { inductiveDisjs.push(mapping[term]); }
    auto newLemma = logic.mkOr(inductiveDisjs);

    // std::cerr << "Old Lemma: " << logic.pp(lemma) << std::endl;
    // std::cerr << "New Lemma: " << logic.pp(newLemma) << std::endl;

if (cfg.debug) {
    SMTSolver debug_solver(logic);
    debug_solver.assertProp(logic.mkNot(vManager.baseFormulaToTarget(newLemma)));

    debug_solver.push();
    debug_solver.assertProp(vManager.baseFormulaToTarget(lemma));
    res = debug_solver.check();
    if (res != SMTSolver::Answer::UNSAT) {
        TRACE(1, "Generalization applied: newLemma is stronger!");
    }
    debug_solver.pop();

    debug_solver.assertProp(maySumm);
    debug_solver.assertProp(transitions);
    debug_solver.push();
    for (auto gi = 0; gi < guardVariables.size(); ++gi) {
        const GuardVar& guardVar = guardVariables[gi];
        debug_solver.assertProp(logic.mkImpl(guardVar.get(logic),
                                             vManager.baseFormulaToSource(newLemma, guardVar.instance)));
    }
    res = debug_solver.check();
    if (res != SMTSolver::Answer::UNSAT) {
        throw std::logic_error("Error in Generalize: newLemma is not inductive!");
    }
    debug_solver.pop();
    res = debug_solver.check();
    if (res != SMTSolver::Answer::UNSAT) {
        TRACE(1, "Inductive-generalization applied: newLemma is stronger than min-gen!");
    }
}

    return newLemma;
}

namespace { // Helper for SpacerContext::generalize_down
/// Sum of the absolute values of the variable coefficients of a (possibly negated) linear
/// inequality; nullopt for any other literal, which ranks it after every linear one.
std::optional<FastRational> coefficientWeight(Logic & logic, PTRef literal) {
    auto & arith = dynamic_cast<ArithLogic &>(logic);
    PTRef atom = arith.isNot(literal) ? arith.getPterm(literal)[0] : literal;
    if (not arith.isLeq(atom)) { return std::nullopt; }
    PTRef term = arith.leqToConstantAndTerm(atom).second;
    if (not arith.isLinearTerm(term)) { return std::nullopt; }
    vec<PTRef> factors;
    if (arith.isPlus(term)) {
        factors = arith.getConstantAndFactors(term).second;
    } else {
        factors.push(term);
    }
    FastRational weight(0);
    for (PTRef factor : factors) {
        auto [var, coeff] = arith.splitTermToVarAndConst(factor);
        if (var == PTRef_Undef) { continue; }
        FastRational const & value = arith.getNumConst(coeff);
        weight += value.sign() < 0 ? -value : value;
    }
    return weight;
}
} // namespace

PTRef SpacerContext::generalize_down(PTRef lemma, PTRef maySumm, PTRef transitions,
                                     const std::vector<GuardVar>& guardVariables) {
    VersionManager vManager(logic);
    const auto& candidates = TermUtils(logic).getTopLevelDisjuncts(lemma);

    if (candidates.size() < 2 or logic.isConstant(candidates[0])) { return lemma; }
    const int n = candidates.size();

    // Declare assumptions. do not assert them yet.
    static std::size_t freshId = 0;
    std::vector<PTRef> selectors;
    selectors.reserve(n);
    for (int i = 0; i < n; ++i) {
        std::string name = "_assume#gdown#" + std::to_string(freshId++);
        selectors.push_back(logic.mkBoolVar(name.c_str()));
    }

    std::vector<vec<PTRef>> assumedSources(guardVariables.size());
    vec<PTRef> assumedTargets;
    assumedTargets.capacity(n);
    for (int i = 0; i < n; ++i) {
        for (std::size_t gi = 0; gi < guardVariables.size(); ++gi) {
            PTRef source = vManager.baseFormulaToSource(candidates[i], guardVariables[gi].instance);
            assumedSources[gi].push(logic.mkAnd(selectors[i], source));
        }
        assumedTargets.push(
            logic.mkImpl(selectors[i], logic.mkNot(vManager.baseFormulaToTarget(candidates[i]))));
    }
    vec<PTRef> allSources;
    allSources.capacity(static_cast<int>(guardVariables.size()));
    for (std::size_t gi = 0; gi < guardVariables.size(); ++gi) {
        allSources.push(logic.mkImpl(guardVariables[gi].get(logic), logic.mkOr(assumedSources[gi])));
    }

    // baseline, without asserting assumption literals
    SMTSolver solver(logic, SMTSolver::WitnessProduction::NONE);
    solver.assertProp(maySumm);
    solver.assertProp(transitions);
    solver.assertProp(logic.mkAnd(allSources));
    solver.assertProp(logic.mkAnd(assumedTargets));

    // Is the lemma restricted to `keep` core inductive relative to the may summary?
    auto inductiveFor = [&](std::vector<bool> const & keep) {
        solver.push();
        for (int i = 0; i < n; ++i) {
            solver.assertProp(keep[i] ? selectors[i] : logic.mkNot(selectors[i]));
        }
        auto res = solver.check();
        solver.pop();
        return res == SMTSolver::Answer::UNSAT;
    };

    // Check which literals are inductive (rel to maysumm) on their own.
    std::vector<bool> preserved(n, false);
    for (int i = 0; i < n; ++i) {
        // remove all but one literal
        std::vector<bool> singleton(n, false);
        singleton[i] = true;
        preserved[i] = inductiveFor(singleton);
    }

    // A literal that is inductive on its own is already the best the down pass can reach: dropping
    // disjuncts only strengthens the clause, so a single literal is as strong as it gets. The greedy
    // pass below can miss it -- it tries the non-inductive literals first, while the inductive ones
    // are still in the clause, and may end on a residue of non-inductive literals that is inductive
    // together -- so keep such a literal directly.
    // Among several, rank first those inductive without the frame (from init and the transition
    // alone): a literal inductive only relative to the frame is often a level-local bound, e.g.
    // y <= 2x + 111 next to the invariant facet y <= 3x + 10. Then prefer small coefficients, which
    // keeps the large integer cuts of a convex closure out of the frame, then the stronger literal.
    SMTSolver frameless(logic, SMTSolver::WitnessProduction::NONE);
    frameless.assertProp(transitions);
    frameless.assertProp(logic.mkAnd(allSources));
    frameless.assertProp(logic.mkAnd(assumedTargets));
    auto inductiveWithoutFrame = [&](int lit) {
        frameless.push();
        for (int i = 0; i < n; ++i) {
            frameless.assertProp(i == lit ? selectors[i] : logic.mkNot(selectors[i]));
        }
        auto res = frameless.check();
        frameless.pop();
        return res == SMTSolver::Answer::UNSAT;
    };
    int alone = -1;
    bool aloneAbsolute = false;
    std::optional<FastRational> aloneWeight;
    for (int i = 0; i < n; ++i) {
        if (not preserved[i]) { continue; }
        bool const absolute = inductiveWithoutFrame(i);
        auto weight = coefficientWeight(logic, candidates[i]);
        bool better = alone < 0 or (absolute and not aloneAbsolute);
        if (not better and absolute == aloneAbsolute) {
            bool const tie = weight.has_value() == aloneWeight.has_value() and
                             (not weight or *weight == *aloneWeight);
            better = (weight and (not aloneWeight or *weight < *aloneWeight)) or
                     (tie and implies(candidates[i], candidates[alone], logic));
        }
        if (better) {
            alone = i;
            aloneAbsolute = absolute;
            aloneWeight = weight;
        }
    }

    std::vector<bool> keep(n, true);
    int kept = n;
    if (alone >= 0) {
        std::fill(keep.begin(), keep.end(), false);
        keep[alone] = true;
        kept = 1;
        TRACE(1, "---- [GDW] Kept the literal inductive on its own");
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
            if (inductiveFor(keep)) {
                --kept;
            } else {
                // if `i` cannot be removed without breking induction, then restore it
                keep[i] = true;
            }
        }
    }
    if (kept == 0) {
        TRACE(1, "---- [GDW] Empty core: vertex proved unreachable, lemma is false");
    }

    vec<PTRef> inductiveDisjs;
    inductiveDisjs.capacity(kept);
    for (int i = 0; i < n; ++i) {
        if (keep[i]) { inductiveDisjs.push(candidates[i]); }
    }
    PTRef newLemma = logic.mkOr(inductiveDisjs);

if (cfg.debug) {
    SMTSolver debug_solver(logic);
    debug_solver.assertProp(logic.mkNot(vManager.baseFormulaToTarget(newLemma)));

    debug_solver.push();
    debug_solver.assertProp(vManager.baseFormulaToTarget(lemma));
    if (debug_solver.check() != SMTSolver::Answer::UNSAT) {
        TRACE(1, "Generalization applied: newLemma is stronger!");
    }
    debug_solver.pop();

    debug_solver.assertProp(maySumm);
    debug_solver.assertProp(transitions);
    debug_solver.push();
    for (auto const & guardVar : guardVariables) {
        debug_solver.assertProp(
            logic.mkImpl(guardVar.get(logic), vManager.baseFormulaToSource(newLemma, guardVar.instance)));
    }
    if (debug_solver.check() != SMTSolver::Answer::UNSAT) {
        throw std::logic_error("Error in generalize_down: newLemma is not inductive!");
    }
    debug_solver.pop();
    if (debug_solver.check() != SMTSolver::Answer::UNSAT) {
        TRACE(1, "Inductive-generalization applied: newLemma is stronger than min-gen!");
    }
}

    return newLemma;
}

PTRef SpacerContext::tryBlockWithRelativeInduction(ProofObligationCore const & pob) const {
    const auto& edges = incomingEdges(pob.vertex);
    vec<PTRef> edgeRepresentations;
    edgeRepresentations.capacity(edges.size());
    std::vector<GuardVar> sourceGuards;
    for (EId eid : edges) {
        edgeRepresentations.push(getEdgeTransition(eid, sourceGuards));
    }
    PTRef transition = logic.mkOr(std::move(edgeRepresentations));
    PTRef maySummary = getGuardedMaySummary(sourceGuards, pob.bound - 1);

    std::vector<GuardVar> guardVariables;
    for (const auto& sourceGuard : sourceGuards) {
        if (sourceGuard.vertex == pob.vertex) {
            guardVariables.push_back(sourceGuard);
        }
    }
    if (guardVariables.empty()) {
        // no inductive edge
        return PTRef_Undef;
    }

    PTRef phi = pob.constraint; // already the target (primed) version

    TermUtils termUtils(logic);

    ModelBasedProjection mbp_solver(logic);

    SMTSolver cti_solver(logic, SMTSolver::WitnessProduction::ONLY_MODEL);
    cti_solver.assertProp(maySummary);
    cti_solver.assertProp(transition);

    vec<PTRef> xsPrime = termUtils.getVars(phi);
    vec<PTRef> xs;
    // TODO this could be improved
    for (PTRef var : termUtils.getVars(logic.mkAnd(maySummary, transition))) {
        if (std::find(xsPrime.begin(), xsPrime.end(), var) == xsPrime.end()) {
            xs.push(var);
        }
    }

    // TODO: incrementality
    auto get_local_unsatcore = [&](PTRef mbp) -> std::pair<PTRef, PTRef> {
        SMTSolver itp_solver(logic, SMTSolver::WitnessProduction::ONLY_UNSAT_CORE);
        itp_solver.assertProp(mbp);
        int counter = 0;
        for (auto conj : termUtils.getTopLevelConjuncts(phi)) {
            itp_solver.tryAssertNamedProp(conj, std::to_string(counter++));
        }
        // itp_solver.push();
        // std::cerr << "ITP(mbp, B) with mbp := " << logic.printTerm(mbp) << std::endl;
        auto res = itp_solver.check();
        if (res != SMTSolver::Answer::UNSAT) {
            // Not an error here, unlike in inductiveConflict(): we never assumed phi to be
            // one-step unreachable.  Every point of `mbp` has a predecessor in
            // maySummary /\ transition, so a satisfiable pair witnesses that phi is
            // reachable -- a counterexample to relative induction.  Report it upwards.
            return {PTRef_Undef, PTRef_Undef};
        }
        auto core = itp_solver.getUnsatCore();
        const auto& terms = core->getTerms();
        // auto interpolantPrime = logic.mkAnd(terms);
        vec<PTRef> negatedTerms;
         negatedTerms.capacity(terms.size());
        for (PTRef term : terms) { negatedTerms.push(logic.mkNot(term)); }
        auto interpolantPrime = logic.mkOr(negatedTerms);
        auto interpolant = VersionManager(logic).targetFormulaToBase(interpolantPrime);

        // assert(is_clause(is_clause, interpolant));
        // itp_solver.pop();
        return {interpolant, interpolantPrime};
    };

    // TODO: incrementality
    auto get_local_itp = [&](PTRef mbp) -> std::pair<PTRef, PTRef> {
        SMTSolver itp_solver(logic, SMTSolver::WitnessProduction::ONLY_INTERPOLANTS);
        itp_solver.getConfig().setSimplifyInterpolant(4);
        itp_solver.assertProp(mbp);
        itp_solver.assertProp(phi);
        // itp_solver.push();
        // std::cerr << "ITP(mbp, B) with mbp := " << logic.printTerm(mbp) << std::endl;
        auto res = itp_solver.check();
        if (res != SMTSolver::Answer::UNSAT) {
            // See get_local_unsatcore above: a satisfiable pair is a counterexample to
            // relative induction, not an error.
            return {PTRef_Undef, PTRef_Undef};
        }
        auto itpCtx = itp_solver.getInterpolationContext();
        std::vector<PTRef> itps;
        ipartitions_t mask = 1;
        itpCtx->getSingleInterpolant(itps, mask);
        PTRef interpolantPrime = itps[0];
        PTRef interpolant = VersionManager(logic).targetFormulaToBase(interpolantPrime);
        // auto ok = is_clause(logic, interpolant);
        // assert(is_clause(is_clause, interpolant));
        // itp_solver.pop();
        return {interpolant, interpolantPrime};
    };

    auto lemma = logic.getTerm_false();
    auto interpolantPrime = logic.getTerm_false();

    std::size_t iterations = 0;

    do {
        // ~lemma(x') accumulated incrementally: lemma is the disjunction of every
        // interpolant found so far, so its negation is the conjunction of the negations.
        cti_solver.assertProp(logic.mkNot(interpolantPrime));

        cti_solver.push();
        for (const auto& guard : guardVariables) {
            cti_solver.assertProp(logic.mkImpl(guard.get(logic),
                                               VersionManager(logic).baseFormulaToSource(lemma, guard.instance)));
        }
        // TODO: exploit incrementality
        auto res = cti_solver.check();
        if (res == SMTSolver::Answer::UNSAT) {
            cti_solver.pop();
            break; // lemma is inductive relative to the may summary, and lemma |= ~phi
        }
        if (res != SMTSolver::Answer::SAT) {
            throw std::logic_error("Error in looking for CTIs.");
        }
        if (++iterations > cfg.relindMaxIterations) {
            // Out of budget.  The partial lemma is NOT a valid summary: it neither
            // over-approximates the post-image nor is it closed under the transition, so it
            // must be discarded rather than handed to the caller.  Discarding is why
            // aborting at any iteration is safe.
            cti_solver.pop();
            return PTRef_Undef;
        }
        auto cti = cti_solver.getModel();
        PTRef implicant = mbp_solver.getModelBasedImplicant(logic.mkAnd(maySummary, transition), xs, *cti);
        auto pair = get_local_itp(implicant);
        // PTRef mbp = mbp_solver.keepOnly(logic.mkAnd(maySummary, transition), xsPrime, *cti);
        // auto pair = get_local_unsatcore(mbp);
        if (pair.first == PTRef_Undef) {
            // The region we would have to cover intersects phi, so it cannot be added
            // without breaking the invariant  lemma |= ~phi.  And the situation is
            // monotone: as the lemma grows the source restriction (g -> lemma(x)) only
            // weakens, so phi stays reachable and the loop can never close.  Give up and
            // let the caller fall back to the predecessor rule.
            cti_solver.pop();
            return PTRef_Undef;
        }
        lemma = logic.mkOr(lemma, pair.first);
        interpolantPrime = pair.second;
        cti_solver.pop();
    } while (true);

    if (logic.isAnd(lemma) or logic.isOr(lemma)) {
        lemma = ::rewriteMaxArityAggresive(logic, lemma);
        lemma = ::simplifyUnderAssignment_Aggressive(lemma, logic);
    }

if (cfg.debug) {
    {
        VersionManager vManager(logic);
        SMTSolver debug_solver(logic);
        debug_solver.push();
        debug_solver.assertProp(vManager.baseFormulaToTarget(lemma));
        debug_solver.assertProp(phi);
        if (debug_solver.check() != SMTSolver::Answer::UNSAT) {
            throw std::logic_error("Error in relind-grow: newLemma is not removing pob");
        }
        debug_solver.pop();
        debug_solver.assertProp(maySummary);
        debug_solver.assertProp(transition);
        for (auto const & guardVar : guardVariables) {
            debug_solver.assertProp(
                logic.mkImpl(guardVar.get(logic), vManager.baseFormulaToSource(lemma, guardVar.instance)));
        }
        debug_solver.assertProp(logic.mkNot(vManager.baseFormulaToTarget(lemma)));
        if (debug_solver.check() != SMTSolver::Answer::UNSAT) {
            throw std::logic_error("Error in relind-grow: newLemma is not inductive!");
        }
    }
}
    return lemma;
}

PTRef SpacerContext::tryBlockWithRelativeInductionBool(ProofObligationCore const & pob) const {
    const auto& edges = incomingEdges(pob.vertex);
    vec<PTRef> edgeRepresentations;
    edgeRepresentations.capacity(edges.size());
    std::vector<GuardVar> sourceGuards;
    for (EId eid : edges) {
        edgeRepresentations.push(getEdgeTransition(eid, sourceGuards));
    }
    PTRef transitions = logic.mkOr(std::move(edgeRepresentations));
    PTRef maySummary = getGuardedMaySummary(sourceGuards, pob.bound - 1);
    
    PTRef edgesMaySummary = logic.mkAnd(maySummary, transitions);

    std::vector<GuardVar> inductiveSources;
    for (const auto& sourceGuard : sourceGuards) {
        if (sourceGuard.vertex == pob.vertex) {
            inductiveSources.push_back(sourceGuard);
        }
    }
    if (inductiveSources.empty()) {
        // no inductive edge
        return PTRef_Undef;
    }

    // Try dropping conjuncts from pob.constraint looking for an UNSAT
    VersionManager vManager(logic);
    const auto& candidates = TermUtils(logic).getTopLevelConjuncts(vManager.targetFormulaToBase(pob.constraint));
    const int n = candidates.size();

    // Declare assumptions. do not assert them yet.
    static std::size_t freshId = 0;
    std::vector<PTRef> selectors;
    selectors.reserve(n);
    for (int i = 0; i < n; ++i) {
        std::string name = "_assume#relind#" + std::to_string(freshId++);
        selectors.push_back(logic.mkBoolVar(name.c_str()));
    }

    std::vector<vec<PTRef>> assumedSources(inductiveSources.size());
    vec<PTRef> assumedTargets;
    assumedTargets.capacity(n);
    for (int i = 0; i < n; ++i) {
        for (std::size_t gi = 0; gi < inductiveSources.size(); ++gi) {
            PTRef source = vManager.baseFormulaToSource(candidates[i], inductiveSources[gi].instance);
            assumedSources[gi].push(logic.mkAnd(selectors[i], logic.mkNot(source)));
        }
        assumedTargets.push(
            logic.mkImpl(selectors[i], vManager.baseFormulaToTarget(candidates[i])));
    }
    vec<PTRef> allSources;
    allSources.capacity(inductiveSources.size());
    for (std::size_t gi = 0; gi < inductiveSources.size(); ++gi) {
        allSources.push(logic.mkImpl(inductiveSources[gi].get(logic), logic.mkOr(assumedSources[gi])));
    }

    // baseline, without asserting assumption literals
    SMTSolver solver(logic, SMTSolver::WitnessProduction::NONE);
    solver.assertProp(maySummary);
    solver.assertProp(transitions);
    solver.assertProp(logic.mkAnd(allSources));
    solver.assertProp(logic.mkAnd(assumedTargets));

    // Is the lemma restricted to `keep` core inductive relative to the may summary?
    auto inductiveFor = [&](std::vector<bool> const & keep) {
        solver.push();
        for (int i = 0; i < n; ++i) {
            solver.assertProp(keep[i] ? selectors[i] : logic.mkNot(selectors[i]));
        }
        auto res = solver.check();
        solver.pop();
        return res == SMTSolver::Answer::UNSAT;
    };

    // Check which literals are inductive (rel to maysumm) on their own.
    std::vector<bool> preserved(n, false);
    for (int i = 0; i < n; ++i) {
        // remove all but one literal
        std::vector<bool> singleton(n, false);
        singleton[i] = true;
        preserved[i] = inductiveFor(singleton);
    }
    // Sort the literals prioritizing the ones that are *not* inductive
    std::vector<int> order(n);
    for (int i = 0; i < n; ++i) { order[i] = i; }
    std::stable_sort(order.begin(), order.end(),
                     [&](int a, int b) { return not preserved[a] and preserved[b]; });

    // Down pass, with `order` sorting
    std::vector<bool> keep(n, true);
    bool found = inductiveFor(keep);
    std::size_t kept = n;
    for (int i : order) {
        // try to delete next `i`
        keep[i] = false;
        --kept;
        if (inductiveFor(keep)) {
            // this removal obtains (or preserves) unsat
            found = true;
        } else {
            if (found) {
                // restore it, it is needed to preserve unsat
                keep[i] = true;
                ++kept;
            }
        }
    }

    if (not found) {
        return PTRef_Undef;
    }

    vec<PTRef> inductiveDisjs;
    inductiveDisjs.capacity(kept);
    for (int i = 0; i < n; ++i) {
        if (keep[i]) { inductiveDisjs.push(logic.mkNot(candidates[i])); }
    }
    PTRef newLemma = logic.mkOr(inductiveDisjs);

if (cfg.debug) {
    SMTSolver debug_solver(logic);
    debug_solver.push();
    debug_solver.assertProp(newLemma);
    debug_solver.assertProp(vManager.targetFormulaToBase(pob.constraint));
    if (debug_solver.check() != SMTSolver::Answer::UNSAT) {
        throw std::logic_error("Error in relind: newLemma is not removing pob");
    }
    debug_solver.pop();
    debug_solver.assertProp(maySummary);
    debug_solver.assertProp(transitions);
    for (auto const & guardVar : inductiveSources) {
        debug_solver.assertProp(
            logic.mkImpl(guardVar.get(logic),
                         vManager.baseFormulaToSource(newLemma, guardVar.instance)));
    }
    debug_solver.assertProp(logic.mkNot(vManager.baseFormulaToTarget(newLemma)));
    if (debug_solver.check() != SMTSolver::Answer::UNSAT) {
        throw std::logic_error("Error in relind: newLemma is not inductive!");
    }
}

    return newLemma;
}

bool SpacerContext::checkMustReachability(std::vector<EId> const & edges, ProofObligationCore const & pob) {
    assert(pob.bound > 0);
    // test if vertex can be reached using must summaries
    vec<PTRef> summaries;
    summaries.capacity(edges.size());
    for (EId edgeId : edges) {
        assert(graph.getTarget(edgeId) == pob.vertex);
        summaries.push(getEdgeMustSummary(edgeId, pob.bound - 1));
    }
    PTRef anySummary = logic.mkOr(summaries);
    auto checkRes = sat(anySummary, pob.constraint);
    if (checkRes.answer == SpacerContext::QueryAnswer::SAT) {
        TRACE(1, "[r] Reachable PO. Must summary successfully applied!")
        assert(checkRes.model);
        // eliminate variables from body except variables present in predicate of pob's vertex
        auto predicateVars = TermUtils(logic).getVars(graph.getNextStateVersion(pob.vertex));
        int counter = 0;
        for (PTRef summary : summaries) {
            if (checkRes.model->evaluate(summary) == logic.getTerm_true()) {
                PTRef newMustSummary = projectFormula(summary, predicateVars, *checkRes.model);
                assert(newMustSummary != PTRef_Undef);
                PTRef definitelyReachable = VersionManager(logic).targetFormulaToBase(newMustSummary);
                // Does this fact widen the under-approximation, or is it already covered?
                // This is the pay-off of a may-pob that cannot be blocked, so report it.
                if (pob.isMayPO) {
                    PTRef known = getMustSummary(pob.vertex, pob.bound);
                    bool const isNew = not implies(definitelyReachable, known, logic);
                    TRACE(1, "[r] MAY PO reachable -> must fact " << definitelyReachable.x
                          << " new? " << isNew);
                }
                addMustSummary(pob.vertex, pob.bound, definitelyReachable);
                if (logProof) {
                    logNewFactIntoDatabase(definitelyReachable, pob.vertex, pob.bound - 1, edges[counter],
                                           *checkRes.model);
                }
                return true;
            }
            ++counter;
        }
        assert(false); // Should be unreachable, we should encounter satisfied summary above
        return true;
    }
    return false;
}

bool SpacerContext::mayReachable(EId eid, PTRef targetConstraint, std::size_t bound) const {
    PTRef maySummary = getEdgeMaySummary(eid, bound);
    if (maySummary == logic.getTerm_false()) { return false; }
    auto checkRes = sat(maySummary, targetConstraint);
    if (checkRes.answer != SpacerContext::QueryAnswer::SAT and checkRes.answer != SpacerContext::QueryAnswer::UNSAT) {
        throw std::logic_error("Spacer: Error in checking implication in mayReachable");
    }
    return checkRes.answer == SpacerContext::QueryAnswer::SAT;
}

ProofObligation SpacerContext::computePredecessor(EId eid, ProofObligationCore const & pob) const {
    assert(pob.bound > 0);
    auto sourceBound = pob.bound - 1;
    auto const & sources = graph.getSources(eid);
    assert(not sources.empty());
    if (sources.size() == 1) {
        // Edge with single source, we only need to check if pob is reachable with over-approximation
        PTRef maySummary = getEdgeMaySummary(eid, sourceBound);
        auto res = sat(maySummary, pob.constraint);
        if (res.answer == QueryAnswer::SAT) {
            assert(res.model);
            // When this source is over-approximated and the edge becomes feasible -> extract next proof obligation
            auto source = sources[0];
            auto predicateVars = TermUtils(logic).getVars(graph.getStateVersion(source));
            // The model always comes from the may-summary check above; MBP_WITH_MAY_SUMMARY
            // decides whether the projection itself sees the frame.
            PTRef mbpArgument = cfg.mbpWithMaySummary
                                    ? maySummary
                                    : getEdgeMustOnlySummary(eid, sourceBound, 0);
            auto [newConstraint, newOverConstraint] = \
                projectFormulaWithOver(logic.mkAnd(mbpArgument, pob.constraint), predicateVars, *res.model);
            PTRef newPob = VersionManager(logic).sourceFormulaToTarget(newConstraint); // ensure POB is target fla
            if (cfg.maypo) {
            PTRef newOverPob = VersionManager(logic).sourceFormulaToTarget(newOverConstraint); // ensure POB is target fla
            if (newOverPob != newPob and newOverPob != logic.getTerm_true()) {
                PobInfo::atBound(pobInfo(pob.vertex, pob.constraint).overPredCache, pob.bound)
                    .insert(eid, 0, newOverPob, 0);
            }
            if (cfg.ccPob and newPob != logic.getTerm_true()) {
                PobInfo::atBound(pobInfo(pob.vertex, pob.constraint).underPredCache, pob.bound)
                    .insert(eid, 0, newPob, cfg.maxPobsForCc);
            }
            }
            TRACE(2, "New proof obligation generated");
            ProofObligation predPob(new ProofObligationCore{source, sourceBound, newPob, pob.isMayPO});
            predPob->parent = &pob;
            predPob->maySource = pob.maySource;
            predPob->life = pob.isMayPO ? pob.life - 1 : cfg.mayPoGas;
            return std::move(predPob);
        } else if (res.answer == QueryAnswer::UNSAT) {
            TRACE(2, "Edge blocked by current  may-summaries")
            return nullptr;
        }
        assert(false);
        throw std::logic_error("Unreachable!");
    }
    // Hyperedge case
    // TODO: Think if this could be optimized further
    bool maybeReachable = mayReachable(eid, pob.constraint, pob.bound - 1);
    if (not maybeReachable) {
        TRACE(2, "Edge blocked by current may-summaries")
        return nullptr;
    }
    // if we got there then it was not possible to prove that the edge can be taken or prove that it cannot be taken
    // examine the sources to generate a new proof obligation for this edge

    // Find the first source vertex such that over-approximating it (instead of under-approximating it) makes the edge feasible
    std::size_t vertexToRefine = 0; // vertex that is the last one to be over-approximated
    while (true) {
        PTRef mixedEdgeSummary = getEdgeMixedSummary(eid, sourceBound, vertexToRefine);
        auto res = sat(mixedEdgeSummary, pob.constraint);
        if (res.answer == QueryAnswer::SAT) {
            assert(res.model);
            // When this source is over-approximated and the edge becomes feasible -> extract next proof obligation
            auto source = sources[vertexToRefine];
            auto predicateVars = TermUtils(logic).getVars(
                graph.getStateVersion(source, vertexInstances.getInstanceNumber(eid, vertexToRefine)));
            // As above: model from the mixed summary; MBP_WITH_MAY_SUMMARY decides whether the
            // projection keeps the may-summaries of sources [0, vertexToRefine].
            PTRef mbpArgument = cfg.mbpWithMaySummary
                                    ? mixedEdgeSummary
                                    : getEdgeMustOnlySummary(eid, sourceBound, vertexToRefine);
            auto [newConstraint, newOverConstraint] =
                projectFormulaWithOver(logic.mkAnd(mbpArgument, pob.constraint), predicateVars, *res.model);
            PTRef newPob = VersionManager(logic).sourceFormulaToTarget(newConstraint); // ensure POB is target fla
            TRACE(2, "New proof obligation generated")
            if (cfg.maypo) {
            PTRef newOverPob = VersionManager(logic).sourceFormulaToTarget(newOverConstraint); // ensure POB is target fla
            if (newOverPob != newPob and newOverPob != logic.getTerm_true()) {
                PobInfo::atBound(pobInfo(pob.vertex, pob.constraint).overPredCache, pob.bound)
                    .insert(eid, vertexToRefine, newOverPob, 0);
            }
            if (cfg.ccPob and newPob != logic.getTerm_true()) {
                PobInfo::atBound(pobInfo(pob.vertex, pob.constraint).underPredCache, pob.bound)
                    .insert(eid, vertexToRefine, newPob, cfg.maxPobsForCc);
            }
            }
            ProofObligation predPob(new ProofObligationCore{sources[vertexToRefine], sourceBound, newPob, pob.isMayPO});
            predPob->parent = &pob;
            predPob->maySource = pob.maySource;
            predPob->life = pob.isMayPO ? pob.life - 1 : cfg.mayPoGas;
            return std::move(predPob);

        } else if (res.answer == QueryAnswer::UNSAT) {
            // Continue with the next vertex to refine
            ++vertexToRefine;
            assert(vertexToRefine < sources.size());
            continue;
        }
        assert(false);
        throw std::logic_error("Unreachable!");
    }
}

// *********** INDUCTIVE CHECK *****************************
SpacerContext::InductiveCheckResult SpacerContext::isInductive(std::size_t maxLevel) {
    std::size_t minLevel = lowestChangedLevel;
    for (std::size_t level = minLevel; level <= maxLevel; ++level) {
        bool inductive = true;
        //        std::cout << "Checking level " << level << std::endl;
        for (auto vid : graph.getVertices()) {
            if (vid == graph.getEntry()) { continue; }
            //            std::cout << " Checking vertex " << vid.id << std::endl;
            // encode body as disjunction over all the incoming edges
            vec<PTRef> edgeRepresentations;
            for (EId eid : incomingEdges(vid)) {
                edgeRepresentations.push(getEdgeMaySummary(eid, level));
                //                std::cout << "Representation of edge " << eid.id << " at level " << level << " is " << logic.printTerm(edgeRepresentations.last()) << std::endl;
            }
            PTRef body = logic.mkOr(edgeRepresentations);
            //            std::cout << "Body representation of " << vid.id << " at level " << level << " is " << logic.printTerm(body) << std::endl;
            // Figure out which components of the may summary are implied by body at level n and so can be pushed to level n+1
            //            std::cout << "Need to check " << maySummaryComponents.size() << " components for vertex " << vid.id << std::endl;
            bool allPushed = tryPushComponents(vid, level, body);
            if (allPushed and vid != graph.getExit()) {
                const auto& allComponents = over.getComponents(vid, level);
                TRACE(1, "[v] INDUCTIVE FRAME FOUND: pred: " << vid.x << " level: " << level );
                for (PTRef component : over.getComponents(vid, level)) {
                    auto const provenance = over.getProvenance(vid, component);
                    TRACE(1, component.x << " learnt with tag "
                          << lemmaOriginToString(provenance.first)
                          << (provenance.seen != provenance.first
                                  ? " also-seen " + lemmaOriginToString(provenance.seen)
                                  : std::string{}));
                }
            }
            inductive = inductive and allPushed;
            // TODO does it make sense to push other vertices if I already know the current level is not inductive?
        }
        if (inductive) {
            return InductiveCheckResult{InductiveCheckAnswer::INDUCTIVE, level};
        }
    }
    return InductiveCheckResult{InductiveCheckAnswer::NOT_INDUCTIVE, 0};
}

/* This is the original tryPushComponents implementation that tries to push the lemmas one by one */
#if 0
bool SpacerContext::tryPushComponents(SymRef vid, std::size_t level, PTRef body) {
    auto maySummaryComponents = over.getComponents(vid, level);
    bool allPushed = true;
    SMTConfig config;
    const char* msg = "ok";
    config.setOption(SMTConfig::o_produce_models, SMTOption(false), msg);
    config.setOption(SMTConfig::o_produce_inter, SMTOption(false), msg);
    MainSolver solver(logic, config, "inductive checker");
    solver.insertFormula(body);
    for (PTRef component : maySummaryComponents) {
        if (over.has(vid, level + 1, component)) {
            continue;
        }
        PTRef nextStateComponent = VersionManager(logic).baseFormulaToTarget(component);
        //        std::cout << " Checking component " << logic.printTerm(nextStateComponent) << std::endl;
        solver.push();
        solver.insertFormula(logic.mkNot(nextStateComponent));
        auto res = solver.check();
        if (res == s_False) {
            addMaySummary(vid, level + 1, component);
        } else {
            allPushed = false;
        }
        solver.pop();
    }
    return allPushed;
}
#endif

bool SpacerContext::tryPushComponents(SymRef vid, std::size_t level, PTRef body) {
    auto maySummaryComponents = over.getComponents(vid, level, false);
    vec<PTRef> targetCandidates;
    targetCandidates.capacity(maySummaryComponents.size());
    for (PTRef const component : maySummaryComponents) {
        if (over.has(vid, level + 1, component)) { continue; }
        targetCandidates.push(VersionManager(logic).baseFormulaToTarget(component));
    }
    std::size_t const candidatesCount = targetCandidates.size_();
    if (candidatesCount == 0) { return true; }

    auto pushed = impliedBy(std::move(targetCandidates), body, logic);
    if (pushed.size() > 0)
        TRACE(1, "[>] Pushed " << pushed.size() << " lemmas to " << level + 1);

    stats.increse_push(pushed.size());

    for (PTRef const lemma : pushed) {
        auto newLemma = VersionManager(logic).targetFormulaToBase(lemma);
        TRACE(1, "[>] Pushed lemma " << newLemma.x << " to " << level + 1
              << " tag " << lemmaOriginToString(over.getProvenance(vid, newLemma).first));
        addMaySummary(vid, level + 1, newLemma);
        over.remove(vid, level, newLemma);
    }

    return pushed.size_() == candidatesCount;
}

PTRef SpacerContext::projectFormula(PTRef fla, const vec<PTRef> & toVars, Model & model) const {
    assert(std::all_of(toVars.begin(), toVars.end(), [this](PTRef var) { return logic.isVar(var); }));
    //    std::cout << "Projecting " << logic.printTerm(fla) << " to variables ";
    //    std::for_each(toVars.begin(), toVars.end(), [&](PTRef var) { std::cout << logic.printTerm(var) << ' '; });
    //    std::cout << std::endl;
    auto varsInFla = TermUtils(logic).getVars(fla);

    vec<PTRef> toEliminate;
    for (PTRef var : varsInFla) {
        auto it = std::find(toVars.begin(), toVars.end(), var);
        if (it == toVars.end()) { toEliminate.push(var); }
    }
    ModelBasedProjection mbp(logic);
    PTRef res = mbp.project(fla, toEliminate, model);
    //    std::cout << "\nResult is " << logic.printTerm(res) << std::endl;
    return res;
}

std::pair<PTRef, PTRef> SpacerContext::projectFormulaWithOver(PTRef fla, const vec<PTRef> & toVars, Model & model) const {
    assert(std::all_of(toVars.begin(), toVars.end(), [this](PTRef var) { return logic.isVar(var); }));
    //    std::cout << "Projecting " << logic.printTerm(fla) << " to variables ";
    //    std::for_each(toVars.begin(), toVars.end(), [&](PTRef var) { std::cout << logic.printTerm(var) << ' '; });
    //    std::cout << std::endl;
    auto varsInFla = TermUtils(logic).getVars(fla);

    vec<PTRef> toEliminate;
    for (PTRef var : varsInFla) {
        auto it = std::find(toVars.begin(), toVars.end(), var);
        if (it == toVars.end()) { toEliminate.push(var); }
    }
    ModelBasedProjection mbp(logic);
    PTRef overapprox = PTRef_Undef;
    PTRef res = mbp.project(fla, toEliminate, model, overapprox);
    //    std::cout << "\nResult is " << logic.printTerm(res) << std::endl;
    return {res, overapprox};
}

PTRef SpacerContext::getEdgeMustSummary(EId eid, std::size_t bound) const {
    //    std::cout << "Must summary:\n ";
    PTRef edgeLabel = graph.getEdgeLabel(eid); // Edge labels are versioned
    //    std::cout << "Edge label: " << logic.pp(edgeLabel) << '\n';
    vec<PTRef> bodyComponents{edgeLabel};
    //    std::cout << "Edge sources:\n";
    auto const & sources = graph.getSources(eid);
    for (unsigned sourceIndex = 0; sourceIndex < sources.size(); ++sourceIndex) {
        auto source = sources[sourceIndex];
        PTRef mustSummary = getMustSummary(source, bound);
        PTRef summaryAsSource =
            VersionManager(logic).baseFormulaToSource(mustSummary, vertexInstances.getInstanceNumber(eid, sourceIndex));
        //        std::cout << source.id << " with summary " << logic.pp(summaryAsSource) << '\n';
        bodyComponents.push(summaryAsSource);
    }
    //    std::cout << std::flush;
    return logic.mkAnd(std::move(bodyComponents));
}

PTRef SpacerContext::getEdgeTransition(EId eid, std::vector<GuardVar>& sourceGuards) const {
    PTRef edgeLabel = graph.getEdgeLabel(eid);
    vec<PTRef> bodyComponents{edgeLabel};
    auto const & sources = graph.getSources(eid);
    for (unsigned sourceIndex = 0; sourceIndex < sources.size(); ++sourceIndex) {
        auto source = sources[sourceIndex];
        auto guardVar = graph.getVertexGuardVariable(source);
        auto instance = vertexInstances.getInstanceNumber(eid, sourceIndex);
        bodyComponents.push(VersionManager(logic).baseFormulaToSource(guardVar, instance));
        // TODO: use std::set
        if (not std::any_of(sourceGuards.begin(), sourceGuards.end(),
                            [guardVar, instance](const GuardVar& gVar) {
                                return gVar.baseGuard == guardVar and gVar.instance == instance;
                            })) {
            sourceGuards.push_back(GuardVar{source, guardVar, instance});
        }
    }
    return logic.mkAnd(std::move(bodyComponents));
}


PTRef SpacerContext::getGuardedMaySummary(const GuardVar& guard, std::size_t bound) const {
    PTRef maySummary = getMaySummary(guard.vertex, bound);
    return guard.getGuardedVersion(logic, maySummary);
}

PTRef SpacerContext::getGuardedMaySummary(const std::vector<GuardVar>& guards, std::size_t bound) const {
    vec<PTRef> summaries;
    summaries.capacity(guards.size());
    for (const auto& guard : guards) {
        summaries.push(getGuardedMaySummary(guard, bound));
    }
    return logic.mkAnd(std::move(summaries));
}

PTRef SpacerContext::getEdgeMaySummary(EId eid, std::size_t bound) const {
    PTRef edgeLabel = graph.getEdgeLabel(eid);
    vec<PTRef> bodyComponents{edgeLabel};
    auto const & sources = graph.getSources(eid);
    for (unsigned sourceIndex = 0; sourceIndex < sources.size(); ++sourceIndex) {
        auto source = sources[sourceIndex];
        PTRef maySummary = getMaySummary(source, bound);
        auto instance = vertexInstances.getInstanceNumber(eid, sourceIndex);
        PTRef summaryAsSource =
            VersionManager(logic).baseFormulaToSource(maySummary, instance);
        //        std::cout << source.id << " with summary " << logic.pp(summaryAsSource) << '\n';
        bodyComponents.push(summaryAsSource);
    }
    //    std::cout << std::flush;
    return logic.mkAnd(std::move(bodyComponents));
}

PTRef SpacerContext::getEdgeMaySummaryWithNewLemma(EId eid, std::size_t bound, SymRef v, PTRef lemma) const {
    PTRef edgeLabel = graph.getEdgeLabel(eid);
    vec<PTRef> bodyComponents{edgeLabel};
    auto const & sources = graph.getSources(eid);
    for (unsigned sourceIndex = 0; sourceIndex < sources.size(); ++sourceIndex) {
        auto source = sources[sourceIndex];
        PTRef maySummary = getMaySummary(source, bound);
        if (source == v) {
            maySummary = logic.mkAnd(maySummary, lemma);
        }
        auto instance = vertexInstances.getInstanceNumber(eid, sourceIndex);
        PTRef summaryAsSource =
            VersionManager(logic).baseFormulaToSource(maySummary, instance);
        //        std::cout << source.id << " with summary " << logic.pp(summaryAsSource) << '\n';
        bodyComponents.push(summaryAsSource);
    }
    //    std::cout << std::flush;
    return logic.mkAnd(std::move(bodyComponents));
}

PTRef SpacerContext::getEdgeMixedSummary(EId eid, std::size_t bound, std::size_t lastMayIndex) const {
    auto const & sources = graph.getSources(eid);
    auto sourceCount = sources.size();
    vec<PTRef> components;
    components.capacity(static_cast<int>(sourceCount) + 1);
    for (std::size_t i = 0; i <= lastMayIndex; ++i) {
        PTRef maySummary = getMaySummary(sources[i], bound);
        PTRef summaryAsSource =
            VersionManager(logic).baseFormulaToSource(maySummary, vertexInstances.getInstanceNumber(eid, i));
        components.push(summaryAsSource);
    }
    for (std::size_t i = lastMayIndex + 1; i < sources.size(); ++i) {
        PTRef mustSummary = getMustSummary(sources[i], bound);
        PTRef summaryAsSource =
            VersionManager(logic).baseFormulaToSource(mustSummary, vertexInstances.getInstanceNumber(eid, i));
        components.push(summaryAsSource);
    }
    components.push(graph.getEdgeLabel(eid));
    return logic.mkAnd(std::move(components));
}

PTRef SpacerContext::getEdgeMustOnlySummary(EId eid, std::size_t bound, std::size_t lastMayIndex) const {
    auto const & sources = graph.getSources(eid);
    vec<PTRef> components;
    components.capacity(static_cast<int>(sources.size()) + 1);
    // Exactly getEdgeMixedSummary, except that source `lastMayIndex`
    for (std::size_t i = 0; i < sources.size(); ++i) {
        if (i == lastMayIndex) { continue; }
        PTRef summary =
            i < lastMayIndex ? getMaySummary(sources[i], bound) : getMustSummary(sources[i], bound);
        components.push(VersionManager(logic).baseFormulaToSource(
            summary, vertexInstances.getInstanceNumber(eid, i)));
    }
    components.push(graph.getEdgeLabel(eid));
    return logic.mkAnd(std::move(components));
}

void SpacerContext::logNewFactIntoDatabase(PTRef fact, SymRef vertex, std::size_t level, EId edgeId, Model & model) {
    DerivationDatabase::DerivedFact newFact = {fact, vertex};
    std::vector<DerivationDatabase::ID> premises;
    // figure out the premises
    VersionManager versionManager(logic);
    auto const & sourceNodes = graph.getSources(edgeId);
    for (std::size_t index = 0; index < sourceNodes.size(); ++index) {
        auto sourceNode = sourceNodes[index];
        auto components = under.getComponents(sourceNode, level, false);
        auto instanceNumber = vertexInstances.getInstanceNumber(edgeId, index);
        bool found = false;
        for (PTRef component : components) {
            PTRef versionedComponent = versionManager.baseFormulaToSource(component, instanceNumber);
            if (model.evaluate(versionedComponent) == logic.getTerm_true()) {
                premises.push_back(database.getIdFor({component, sourceNode}));
                found = true;
                break;
            }
        }
        assert(found);
        if (not found) { throw std::logic_error("Unreachable!"); }
    }
    database.newDerivation(newFact, edgeId, std::move(premises));
}

namespace { // Helper for SpacerContext::reconstructInvalidityWitness
struct Entry {
    DerivationDatabase::ID databaseEntryId;
    PTRef factInstance;
    std::vector<PTRef> premiseInstances;
};

void computePremiseInstances(DerivationDatabase::Entry const & databaseEntry, Entry & entry,
                             DerivationDatabase const & database, ChcDirectedHyperGraph const & graph,
                             ChcDirectedHyperGraph::VertexInstances const & vertexInstances) {
    // Simplest way: Compute a model for a formula consisting of
    //  1. Constraint of the edge
    //  2. Premise constraints
    //  3. The fact we want to derive
    // This will give us a model from which we can compute the instances of the premises
    assert(entry.premiseInstances.empty());
    Logic & logic = graph.getLogic();
    EId edge = databaseEntry.incomingEdge;
    SMTSolver solver(logic, SMTSolver::WitnessProduction::ONLY_MODEL);
    VersionManager versionManager(logic);
    vec<PTRef> sourcePredicates;
    for (std::size_t i = 0; i < databaseEntry.premises.size(); ++i) {
        auto premiseEntry = database.getEntry(databaseEntry.premises[i]);
        assert(premiseEntry.derivedFact.node == graph.getSources(edge)[i]);
        auto instanceNumber = vertexInstances.getInstanceNumber(edge, i);
        PTRef premiseConstraint = versionManager.baseFormulaToSource(premiseEntry.derivedFact.fact, instanceNumber);
        sourcePredicates.push(graph.getStateVersion(premiseEntry.derivedFact.node, instanceNumber));
        solver.assertProp(premiseConstraint);
        //        std::cout << logic.pp(premiseConstraint) << '\n';
    }
    PTRef edgeConstraint = graph.getEdgeLabel(edge);
    PTRef factInstance = entry.factInstance;
    auto targetNode = graph.getTarget(edge);
    if (targetNode != graph.getExit()) {
        assert(targetNode == logic.getSymRef(factInstance));
        PTRef targetVersion = graph.getNextStateVersion(graph.getTarget(edge));
        TermUtils::substitutions_map mapping;
        TermUtils(logic).mapFromPredicate(targetVersion, factInstance, mapping);
        PTRef simplifiedConstraint = TermUtils(logic).varSubstitute(edgeConstraint, mapping);
        solver.assertProp(simplifiedConstraint);
    } else {
        solver.assertProp(edgeConstraint);
    }
    auto res = solver.check();
    if (res != SMTSolver::Answer::SAT) { throw std::logic_error("Error in computing derivation!"); }
    auto model = solver.getModel();
    std::transform(sourcePredicates.begin(), sourcePredicates.end(), std::back_inserter(entry.premiseInstances),
                   [&](PTRef premise) {
                       auto vars = TermUtils(logic).predicateArgsInOrder(premise);
                       vec<PTRef> evaluatedVars(vars.size());
                       std::transform(vars.begin(), vars.end(), evaluatedVars.begin(),
                                      [&](PTRef var) { return model->evaluate(var); });
                       PTRef premiseInstance = logic.insertTerm(logic.getSymRef(premise), std::move(evaluatedVars));
                       //        std::cout << logic.pp(premise) << " -> " << logic.pp(premiseInstance) << std::endl;
                       return premiseInstance;
                   });
}
} // namespace

InvalidityWitness SpacerContext::reconstructInvalidityWitness() const {
    if (not logProof) { return {}; }
    //    database.print(logic);
    // We make a DFS style traversal of the database, starting from the derivation of FALSE
    // After the premises of a derived fact has been processed, we can add the fact to the InvalidityWitness
    InvalidityWitness::Derivation witnessingDerivation;
    std::unordered_map<PTRef, std::size_t, PTRefHash> derivationSteps;
    DerivationDatabase::DerivedFact root{.fact = logic.getTerm_true(), .node = graph.getExit()};
    auto rootIndex = database.getIdFor(root);
    std::deque<Entry> toProcess; // MB: We use deque to have stable references
    toProcess.push_back({rootIndex, logic.getTerm_true(), {}});
    while (not toProcess.empty()) {
        auto & entry = toProcess.back();
        if (entry.databaseEntryId != rootIndex and derivationSteps.count(entry.factInstance) > 0) {
            toProcess.pop_back();
            continue;
        }
        auto const & databaseEntry = database.getEntry(entry.databaseEntryId);
        if (not databaseEntry.premises.empty() and entry.premiseInstances.empty()) {
            computePremiseInstances(databaseEntry, entry, database, graph, vertexInstances);
        }
        bool allPremissesProcessed = true;
        assert(databaseEntry.premises.size() == entry.premiseInstances.size());
        for (std::size_t i = 0; i < databaseEntry.premises.size(); ++i) {
            auto it = derivationSteps.find(entry.premiseInstances[i]);
            if (it == derivationSteps.end()) {
                allPremissesProcessed = false;
                toProcess.push_back({databaseEntry.premises[i], entry.premiseInstances[i], {}});
            }
        }
        if (not allPremissesProcessed) { continue; }
        // all premises processed, we can process this step
        InvalidityWitness::Derivation::DerivationStep step;
        step.index = witnessingDerivation.size();
        step.derivedFact = entry.factInstance;
        step.clauseId = databaseEntry.incomingEdge;
        std::transform(entry.premiseInstances.begin(), entry.premiseInstances.end(), std::back_inserter(step.premises),
                       [&](auto id) {
                           auto it = derivationSteps.find(id);
                           assert(it != derivationSteps.end());
                           return it->second;
                       });
        if (databaseEntry.derivedFact.node == graph.getExit()) { // MB: Patch the final derivation step
            assert(step.derivedFact == logic.getTerm_true());
            step.derivedFact = logic.getTerm_false();
        }
        derivationSteps.insert({step.derivedFact, step.index});
        witnessingDerivation.addDerivationStep(std::move(step));
        toProcess.pop_back();
    }
    InvalidityWitness witness;
    witness.setDerivation(std::move(witnessingDerivation));
    return witness;
}
} // namespace golem
