//
// Created by Martin Blicha on 01.06.21.
//

#ifndef OPENSMT_ACCELERATEDBMC_H
#define OPENSMT_ACCELERATEDBMC_H

#include "Engine.h"

class TransitionSystem;

enum class ReachabilityResult {REACHABLE, UNREACHABLE};

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
    Options const & options;
    friend class TransitionSystemNetworkManager;
public:
    TPAEngine(Logic & logic, Options const & options) : logic(logic), options(options) {}

    GraphVerificationResult solve(ChcDirectedHyperGraph & system) override {
        throw std::logic_error("Not supported yet!");
    }

    GraphVerificationResult solve(const ChcDirectedGraph & system) override;

private:
    std::unique_ptr<TPABase> mkSolver();
    
    GraphVerificationResult solveTransitionSystemChain(ChcDirectedGraph const & graph);
};

class TPABase {
protected:
    Logic & logic;
    Options const & options;
    int verbosity = 0;
    bool useQE = false;

    // Versioned representation of the transition system
    PTRef init;
    PTRef transition;
    PTRef query;
    vec<PTRef> stateVariables;
    vec<PTRef> auxiliaryVariables;
    PTRef inductiveInvariant = PTRef_Undef;
    PTRef explanation = PTRef_Undef;

public:
    TPABase(Logic& logic, Options const & options) : logic(logic), options(options) {
        if (options.hasOption(Options::VERBOSE)) {
            verbosity = std::stoi(options.getOption(Options::VERBOSE));
        }
        if (options.hasOption(Options::TPA_USE_QE)) {
            useQE = true;
        }
    }

    virtual ~TPABase() = default;

    virtual GraphVerificationResult solveTransitionSystem(TransitionSystem & system, ChcDirectedGraph const & graph);

    void resetTransitionSystem(TransitionSystem const & system);

    VerificationResult solve();

    void resetInitialStates(PTRef);

    void updateQueryStates(PTRef);

    PTRef getInit() const;
    PTRef getTransitionRelation() const;
    PTRef getQuery() const;

    PTRef getExplanation() const;

protected:

    virtual VerificationResult checkPower(unsigned short power) = 0;

    virtual void resetPowers() = 0;

    struct QueryResult {
        ReachabilityResult result;
        PTRef refinedTarget = PTRef_Undef;
    };

    static bool isReachable (QueryResult res) { return res.result == ReachabilityResult::REACHABLE; };
    static bool isUnreachable (QueryResult res) { return res.result == ReachabilityResult::UNREACHABLE; };
    static PTRef extractReachableTarget (QueryResult res) { return res.refinedTarget; };

    using CacheType = std::unordered_map<std::pair<PTRef, PTRef>, QueryResult, PTRefPairHash>;
    std::vector<CacheType> queryCache;

    struct VersionHasher {
        std::size_t operator()(std::pair<PTRef, int> val) const {
            return std::hash<uint32_t>()(val.first.x) ^ std::hash<int>()(val.second);
        }
    };
    mutable std::unordered_map<std::pair<PTRef, int>, PTRef, VersionHasher> versioningCache;

    PTRef getNextVersion(PTRef currentVersion, int) const ;
    PTRef getNextVersion(PTRef currentVersion) const { return getNextVersion(currentVersion, 1); };

    vec<PTRef> getStateVars(int version) const;

    /* Shifts only next-next vars to next vars */
    PTRef cleanInterpolant(PTRef itp);
    /* Shifts only next vars to next-next vars */
    PTRef shiftOnlyNextVars(PTRef transition);

    PTRef simplifyInterpolant(PTRef itp);

    int verbose() const { return verbosity; }
    bool shouldComputeExplanation() const { return true; } // TODO: make this configurable

    bool isPureStateFormula(PTRef fla) const;
    bool isPureTransitionFormula(PTRef fla) const;

    bool verifyKinductiveInvariant(PTRef invariant, unsigned long k);
    PTRef kinductiveToInductive(PTRef invariant, unsigned long k);

    PTRef refineTwoStepTarget(PTRef start, PTRef transition, PTRef goal, Model& model);

    PTRef extractMidPoint(PTRef start, PTRef firstTransition, PTRef secondTransition, PTRef goal, Model& model);

    PTRef eliminateVars(PTRef fla, vec<PTRef> const & vars, Model & model);

    PTRef keepOnlyVars(PTRef fla, vec<PTRef> const & vars, Model & model);

    PTRef unsafeInitialStates(PTRef transitionInvariant);
};

class TPASplit : public TPABase {

    vec<PTRef> exactPowers;
    vec<PTRef> lessThanPowers;

    vec<SolverWrapper*> reachabilitySolvers;

public:
    TPASplit(Logic& logic, Options const & options) : TPABase(logic, options) {}

    ~TPASplit() override;

private:
    void resetPowers() override;

    VerificationResult checkPower(unsigned short power) override;

    PTRef getExactPower(unsigned short power) const;
    void storeExactPower(unsigned short power, PTRef tr);

    PTRef getLessThanPower(unsigned short power) const;
    void storeLessThanPower(unsigned short power, PTRef tr);

    SolverWrapper* getExactReachabilitySolver(unsigned short power) const;

    QueryResult reachabilityQueryExact(PTRef from, PTRef to, unsigned short power);
    QueryResult reachabilityQueryLessThan(PTRef from, PTRef to, unsigned short power);

    QueryResult reachabilityExactOneStep(PTRef from, PTRef to);
    QueryResult reachabilityExactZeroStep(PTRef from, PTRef to);

    bool verifyLessThanPower(unsigned short power);
    bool verifyExactPower(unsigned short power);

    bool checkLessThanFixedPoint(unsigned short power);
    bool checkExactFixedPoint(unsigned short power);
};

class TPABasic : public TPABase {

    vec<PTRef> transitionHierarchy;

    vec<SolverWrapper*> reachabilitySolvers;

public:
    TPABasic(Logic& logic, Options const & options) : TPABase(logic, options) {}

    ~TPABasic() override;


private:
    void resetPowers() override;

    VerificationResult checkPower(unsigned short power) override;

    PTRef getLevelTransition(unsigned short) const;
    void storeLevelTransition(unsigned short, PTRef);

    SolverWrapper* getReachabilitySolver(unsigned short power) const;

    QueryResult reachabilityQuery(PTRef from, PTRef to, unsigned short power);

    QueryResult reachabilityExactOneStep(PTRef from, PTRef to);
    QueryResult reachabilityExactZeroStep(PTRef from, PTRef to);

    bool verifyLevel(unsigned short level);

    bool checkFixedPoint(unsigned short power);
};


#endif //OPENSMT_ACCELERATEDBMC_H
