/*
 * Copyright (c) 2021-2022, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef GOLEM_TPA_H
#define GOLEM_TPA_H

#include "Engine.h"

class TransitionSystem;

enum class ReachabilityResult { REACHABLE, UNREACHABLE };

class SolverWrapper {
protected:
    PTRef transition = PTRef_Undef;

public:
    virtual ~SolverWrapper() = default;
    virtual ReachabilityResult checkConsistent(PTRef query) = 0;
    virtual void strenghtenTransition(PTRef nTransition) = 0;
    virtual std::unique_ptr<Model> lastQueryModel() = 0;
    virtual PTRef lastQueryTransitionInterpolant() = 0;
};

class TPABase;

class TPAEngine : public Engine {
    Logic & logic;
    Options options;
    friend class TransitionSystemNetworkManager;

public:
    TPAEngine(Logic & logic, Options options) : logic(logic), options(std::move(options)) {}

    VerificationResult solve(ChcDirectedHyperGraph const & graph) override;

    static const std::string TPA;
    static const std::string SPLIT_TPA;

private:
    VerificationResult solve(const ChcDirectedGraph & system);

    bool isTrivial(ChcDirectedGraph const & graph);

    VerificationResult solveTrivial(ChcDirectedGraph const & graph);

    std::unique_ptr<TPABase> mkSolver();

    VerificationResult solveTransitionSystemGraph(ChcDirectedGraph const & graph);

    ValidityWitness computeValidityWitness(ChcDirectedGraph const & graph, TransitionSystem const & ts,
                                           PTRef inductiveInvariant) const;

    InvalidityWitness computeInvalidityWitness(ChcDirectedGraph const & graph, unsigned steps) const;
};

enum class TPAType : char { LESS_THAN, EQUALS };

struct SafetyExplanation {
    enum class TransitionInvariantType : char { NONE, UNRESTRICTED, RESTRICTED_TO_INIT, RESTRICTED_TO_QUERY };

    enum class FixedPointType : char { LEFT, RIGHT };

    TransitionInvariantType invariantType{TransitionInvariantType::NONE};
    TPAType relationType{TPAType::LESS_THAN};
    FixedPointType fixedPointType{FixedPointType::LEFT};
    unsigned power{0};
};

struct ReachedStates {
    PTRef reachedStates{PTRef_Undef};
    unsigned steps{0};
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

    PTRef identity{PTRef_Undef};

public:
    TPABase(Logic & logic, Options const & options) : logic(logic), options(options) {
        if (options.hasOption(Options::VERBOSE)) { verbosity = std::stoi(options.getOption(Options::VERBOSE)); }
        if (options.hasOption(Options::TPA_USE_QE)) { useQE = true; }
    }

    virtual ~TPABase() = default;

    virtual VerificationAnswer solveTransitionSystem(TransitionSystem & system);

    void resetTransitionSystem(TransitionSystem const & system);

    VerificationAnswer solve();

    void resetInitialStates(PTRef);

    void updateQueryStates(PTRef);

    PTRef getInit() const;
    PTRef getTransitionRelation() const;
    PTRef getQuery() const;

    PTRef getSafetyExplanation() const;
    PTRef getReachedStates() const;
    unsigned getTransitionStepCount() const;
    PTRef getInductiveInvariant() const;

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

    struct VersionHasher {
        std::size_t operator()(std::pair<PTRef, int> val) const {
            return std::hash<uint32_t>()(val.first.x) ^ std::hash<int>()(val.second);
        }
    };
    mutable std::unordered_map<std::pair<PTRef, int>, PTRef, VersionHasher> versioningCache;

    PTRef getNextVersion(PTRef currentVersion, int) const;
    PTRef getNextVersion(PTRef currentVersion) const { return getNextVersion(currentVersion, 1); };

    vec<PTRef> getStateVars(int version) const;

    /* Shifts only next-next vars to next vars */
    PTRef cleanInterpolant(PTRef itp);
    /* Shifts only next vars to next-next vars */
    PTRef shiftOnlyNextVars(PTRef transition) const;

    PTRef simplifyInterpolant(PTRef itp);

    int verbose() const { return verbosity; }

    bool isPureStateFormula(PTRef fla) const;
    bool isPureTransitionFormula(PTRef fla) const;

    bool verifyKinductiveInvariant(PTRef invariant, unsigned long k) const;

    PTRef refineTwoStepTarget(PTRef start, PTRef transition, PTRef goal, Model & model);

    PTRef extractMidPoint(PTRef start, PTRef firstTransition, PTRef secondTransition, PTRef goal, Model & model);

    PTRef eliminateVars(PTRef fla, vec<PTRef> const & vars, Model & model);

    PTRef keepOnlyVars(PTRef fla, vec<PTRef> const & vars, Model & model);

    PTRef safeSupersetOfInitialStates(PTRef start, PTRef transitionInvariant, PTRef target) const;

    bool checkLessThanFixedPoint(unsigned short power);

    QueryResult reachabilityExactOneStep(PTRef from, PTRef to);
    QueryResult reachabilityExactZeroStep(PTRef from, PTRef to);

    PTRef computeIdentity() const;

    void resetExplanation();

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
};

class TPABasic : public TPABase {

    vec<PTRef> transitionHierarchy;

    vec<SolverWrapper *> reachabilitySolvers;

public:
    TPABasic(Logic & logic, Options const & options) : TPABase(logic, options) {}

    ~TPABasic() override;

private:
    void resetPowers() override;

    VerificationAnswer checkPower(unsigned short power) override;

    PTRef getPower(unsigned short power, TPAType relationType) const override;
    bool verifyPower(unsigned short power, TPAType relationType) const override;

    PTRef getLevelTransition(unsigned short) const;
    void storeLevelTransition(unsigned short, PTRef);

    SolverWrapper * getReachabilitySolver(unsigned short power) const;

    QueryResult reachabilityQuery(PTRef from, PTRef to, unsigned short power);

    bool verifyPower(unsigned short level) const;
};

#endif // GOLEM_TPA_H
