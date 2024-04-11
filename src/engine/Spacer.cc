/*
 * Copyright (c) 2021-2022, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "Spacer.h"

#include "utils/SmtSolver.h"
#include "ModelBasedProjection.h"

#include <queue>
#include <unordered_map>
#include <unordered_set>

#define TRACE_LEVEL 0

#define TRACE(l,m) if (TRACE_LEVEL >= l) { std::cout << m << std::endl; }

class ApproxMap {
public:
    vec<PTRef> getComponents(SymRef vid, std::size_t bound) const {
        vec<PTRef> res;
        (const_cast<ApproxMap*>(this))->ensureBound(bound);
        auto const& boundMap = innerMap[bound];
        auto it = boundMap.find(vid);
        if (it != boundMap.end()) {
            res.capacity(it->second.size());
            for (PTRef component : it->second) {
                res.push(component);
            }
        }
        return res;
    }

    void insert(SymRef vid, std::size_t bound, PTRef summary) {
        ensureBound(bound);
        auto & boundMap = innerMap[bound];
        auto & components = boundMap[vid];
        components.insert(summary);
    }

    bool has(SymRef vid, std::size_t bound, PTRef summary) {
        ensureBound(bound);
        auto const & boundMap = innerMap[bound];
        auto it = boundMap.find(vid);
        if (it != boundMap.end()) {
            return it->second.find(summary) != it->second.end();
        }
        return false;
    }

private:
    std::vector<std::unordered_map<SymRef, std::unordered_set<PTRef, PTRefHash>, SymRefHash>> innerMap; // bound -> vertex -> elements of approximation

    void ensureBound(std::size_t bound) {
        while (innerMap.size() <= bound) {
            innerMap.emplace_back();
        }
    }
};

class UnderApproxMap : public ApproxMap {

};

class OverApproxMap : public ApproxMap {

};

struct ProofObligation {
    SymRef vertex;
    std::size_t bound;
    PTRef constraint;
};

bool operator<(ProofObligation const& pob1, ProofObligation const& pob2) {
    // TODO: Does it make sense to break ties using vertices?
    return pob1.bound < pob2.bound or
           (pob1.bound == pob2.bound and pob1.vertex.x < pob2.vertex.x);
}

// TODO: why we need both operators??
bool operator>(ProofObligation const& pob1, ProofObligation const& pob2) {
    return pob1.bound > pob2.bound or
           (pob1.bound == pob2.bound and pob1.vertex.x > pob2.vertex.x);
}

struct PriorityQueue {

    void push(ProofObligation pob) { pqueue.push(pob); }
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

    Entry const & getEntry(ID index) const { assert(index < table.size()); return table.at(index); }

    // DEBUG
    void print(Logic & logic) const {
        for (auto const & entry : *this) {
            std::cout << logic.printSym(entry.derivedFact.node) << " " << logic.pp(entry.derivedFact.fact) << " " << entry.incomingEdge.id << " | ";
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
        if (table[i].derivedFact == fact) {
            return i;
        }
    }
    throw std::logic_error("Given fact not found in the database of derived facts");
}

void DerivationDatabase::newDerivation(DerivationDatabase::DerivedFact fact, EId edge, std::vector<ID> premises) {
    table.push_back({.derivedFact = fact, .incomingEdge = edge, .premises = std::move(premises)});
}

class SpacerContext {
    Logic & logic;
    ChcDirectedHyperGraph const & graph;

    UnderApproxMap under;
    OverApproxMap over;

    DerivationDatabase database;
    bool logProof;

    std::size_t lowestChangedLevel = 0;

    // Helper data structures to get the versioning right
    ChcDirectedHyperGraph::VertexInstances vertexInstances;

    void addMaySummary(SymRef vid, std::size_t bound, PTRef summary) {
        over.insert(vid, bound, summary);
    }

    void addMustSummary(SymRef vid, std::size_t bound, PTRef summary) {
        under.insert(vid, bound, summary);
    }

    PTRef getMustSummary(SymRef vid, std::size_t bound) const {
        return logic.mkOr(under.getComponents(vid, bound));
    }

    PTRef getMaySummary(SymRef vid, std::size_t bound) const {
        return logic.mkAnd(over.getComponents(vid, bound));
    }

    PTRef getEdgeMustSummary(EId eid, std::size_t bound) const;

    PTRef getEdgeMaySummary(EId eid, std::size_t bound) const;

    PTRef getEdgeMixedSummary(EId eid, std::size_t bound, std::size_t lastMayIndex) const;

    enum class BoundedSafetyResult { SAFE, UNSAFE };

    BoundedSafetyResult boundSafety(std::size_t currentBound);

    enum class InductiveCheckAnswer { INDUCTIVE, NOT_INDUCTIVE };

    struct InductiveCheckResult {
        InductiveCheckAnswer answer;
        std::size_t inductiveLevel;
    };

    InductiveCheckResult isInductive(std::size_t);

    bool tryPushComponents(SymRef, std::size_t, PTRef);


    enum class QueryAnswer : char {UNKNOWN, SAT, UNSAT, ERROR};
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

    bool checkMustReachability(std::vector<EId> const & edges, ProofObligation const & pob);

    bool mayReachable(EId eid, PTRef targetConstraint, std::size_t bound) const;

    std::optional<ProofObligation> computePredecessor(EId eid, ProofObligation const & pob) const;

    PTRef projectFormula(PTRef fla, vec<PTRef> const & vars, Model & model) const;

    void logNewFactIntoDatabase(PTRef fact, SymRef vertex, std::size_t sourceLevel, EId eid, Model & model);

    InvalidityWitness reconstructInvalidityWitness() const;
public:
    SpacerContext(Logic & logic, ChcDirectedHyperGraph const & graph, bool logProof);

    VerificationResult run();
};

VerificationResult Spacer::solve(ChcDirectedHyperGraph const & system) {
    bool logProof = options.hasOption(Options::COMPUTE_WITNESS) and options.getOption(Options::COMPUTE_WITNESS) == "true";
    return SpacerContext(logic, system, logProof).run();
}

SpacerContext::SpacerContext(Logic & logic, ChcDirectedHyperGraph const & graph, bool logProof)
    : logic(logic), graph(graph), logProof(logProof), vertexInstances(graph) {
    auto vertices = graph.getVertices();
    for (auto vid : vertices) {
        PTRef toInsert = vid == graph.getEntry() ? logic.getTerm_true() : logic.getTerm_false();
        addMaySummary(vid, 0, toInsert);
        addMustSummary(vid, 0, toInsert);
    }
    database.newDerivation({.fact = logic.getTerm_true(), .node = graph.getEntry()}, {static_cast<std::size_t>(-1)}, {});
}

VerificationResult SpacerContext::run() {
    std::size_t currentBound = 1;
    while(true) {
        addMaySummary(graph.getEntry(), currentBound, logic.getTerm_true());
        addMustSummary(graph.getEntry(), currentBound, logic.getTerm_true());
        TRACE(1, "Checking bound safety for " << currentBound)
        auto boundedResult = boundSafety(currentBound);
        switch (boundedResult) {
            case BoundedSafetyResult::UNSAFE:
                return VerificationResult(VerificationAnswer::UNSAFE, reconstructInvalidityWitness());
            case BoundedSafetyResult::SAFE: {
                auto inductiveResult = isInductive(currentBound);
                if (inductiveResult.answer == InductiveCheckAnswer::INDUCTIVE) {
                    std::unordered_map<PTRef, PTRef, PTRefHash> solution;
                    auto inductiveLevel = inductiveResult.inductiveLevel;
                    for (auto vid : graph.getVertices()) {
                        PTRef statePredicate = graph.getStateVersion(vid);
                        if (vid == graph.getEntry() or vid == graph.getExit()) { continue; }
                        // MB: 0-ary predicate would be treated as variables in VersionManager, not what we want
                        PTRef predicate = logic.getPterm(statePredicate).size() > 0 ? VersionManager(logic).sourceFormulaToBase(statePredicate) : statePredicate;
                        PTRef invariantSummary = logic.mkAnd(over.getComponents(vid, inductiveLevel));
                        if (logic.isOr(invariantSummary) or logic.isAnd(invariantSummary)) {
                            invariantSummary = simplifyUnderAssignment_Aggressive(invariantSummary, logic);
                        }
                        auto insertRes = solution.insert(std::make_pair(predicate, invariantSummary));
                        assert(insertRes.second);
                        if (not insertRes.second) {
                            throw std::logic_error("Duplicate definition for a predicate encountered!");
                        }
                    }
                    return {VerificationAnswer::SAFE, ValidityWitness(std::move(solution))};
                }
                ++currentBound;
                break;
            }
            default:
                assert(false);
                throw std::logic_error("Unreachable!");
        }
    }
}


std::vector<EId> incomingEdges(SymRef v, ChcDirectedHyperGraph const & graph) {
    // TODO: Remember the adjacency representation and do not recompute this all the time
    std::vector<EId> incoming;
    graph.forEachEdge([&](auto const & edge) {
       if (graph.getTarget(edge.id) == v) { incoming.push_back(edge.id); }
    });
    return incoming;
}

SpacerContext::BoundedSafetyResult SpacerContext::boundSafety(std::size_t currentBound) {
    TRACE(1, "\nRunning bounded safety check at level " << currentBound)
    auto query = graph.getExit();
    PriorityQueue pqueue;
    pqueue.push(ProofObligation{query, currentBound, logic.getTerm_true()});
    lowestChangedLevel = currentBound;
    while(not pqueue.empty()) {
        TRACE(2, "Examining proof obligation " << pqueue.peek().vertex.x)
        auto const & pob = pqueue.peek();
        if (pob.vertex == graph.getEntry()) {
            assert(false); // With the must summaries, we actually never finish here
            return BoundedSafetyResult::UNSAFE;
        }
        auto edges = incomingEdges(pob.vertex, graph);
        bool mustReached = checkMustReachability(edges, pob);
        if (mustReached) {
            if (pob.vertex == query) {
                return BoundedSafetyResult::UNSAFE; // query is reachable
            }
            pqueue.pop();
            continue;
        }
        std::vector<ProofObligation> newProofObligations;
        for (EId edgeId : edges) {
            auto newProofObligation = computePredecessor(edgeId, pob);
            if (newProofObligation.has_value()) {
                newProofObligations.push_back(newProofObligation.value());
            }
        }
        if (newProofObligations.empty()) {
            // all edges are blocked; compute new lemma blocking the current proof obligation
            // TODO:
            vec<PTRef> edgeRepresentations; edgeRepresentations.capacity(edges.size());
            for (EId eid : edges) {
                edgeRepresentations.push(getEdgeMaySummary(eid, pob.bound - 1));
            }
            auto res = interpolatingSat(logic.mkOr(edgeRepresentations), pob.constraint);
            assert(res.answer == QueryAnswer::UNSAT);
            if (res.answer != QueryAnswer::UNSAT) {
                throw std::logic_error("All edges should have been blocked, but they are not!");
            }
            PTRef newLemma = VersionManager(logic).targetFormulaToBase(res.interpolant);
            TRACE(2, "Learnt new lemma for " << pob.vertex.x << " at level " << pob.bound << " - " << logic.pp(newLemma))
            addMaySummary(pob.vertex, pob.bound, newLemma);
            if (pob.bound < lowestChangedLevel) {
                lowestChangedLevel = pob.bound;
            }
            pqueue.pop(); // This POB has been successfully blocked
        } else {
            for (auto const& npob : newProofObligations) {
                TRACE(2,"Pushing new proof obligation " << logic.pp(npob.constraint) << " for " << npob.vertex.x << " at level " << npob.bound)
                pqueue.push(npob);
            }
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
    SMTSolver solverWrapper(logic);
    auto & solver = solverWrapper.getCoreSolver();
    solver.insertFormula(A);
    solver.insertFormula(B);
    auto res = solver.check();
    if (res == s_True) {
        qres.answer = QueryAnswer::SAT;
        qres.model = solver.getModel();
    }
    else if (res == s_False) {
        qres.answer = QueryAnswer::UNSAT;
    }
    else if (res == s_Undef) {
        qres.answer = QueryAnswer::UNKNOWN;
    }
    else if (res == s_Error) {
        qres.answer = QueryAnswer::ERROR;
    }
    else {
        assert(false);
        throw std::logic_error("Unreachable code!");
    }
    return qres;
}

SpacerContext::ItpQueryResult SpacerContext::interpolatingSat(PTRef A, PTRef B) {
    SMTSolver solverWrapper(logic, SMTSolver::WitnessProduction::ONLY_INTERPOLANTS);
    solverWrapper.getConfig().setSimplifyInterpolant(4);
    auto & solver = solverWrapper.getCoreSolver();
    solver.insertFormula(A);
    solver.insertFormula(B);
    auto res = solver.check();
    ItpQueryResult qres;
    if (res == s_True) {
        qres.answer = QueryAnswer::SAT;
    }
    else if (res == s_False) {
        qres.answer = QueryAnswer::UNSAT;
        auto itpCtx = solver.getInterpolationContext();
        std::vector<PTRef> itps;
        ipartitions_t mask = 1;
        itpCtx->getSingleInterpolant(itps, mask);
        qres.interpolant = itps[0];
    }
    else if (res == s_Undef) {
        qres.answer = QueryAnswer::UNKNOWN;
    }
    else if (res == s_Error) {
        qres.answer = QueryAnswer::ERROR;
    }
    else {
        assert(false);
        throw std::logic_error("Unreachable code!");
    }
    return qres;
}

bool SpacerContext::checkMustReachability(std::vector<EId> const & edges, ProofObligation const & pob) {
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
        TRACE(1, "Must summary successfully applied!")
        assert(checkRes.model);
        // eliminate variables from body except variables present in predicate of pob's vertex
        auto predicateVars = TermUtils(logic).getVars(graph.getNextStateVersion(pob.vertex));
        int counter = 0;
        for (PTRef summary : summaries) {
            if (checkRes.model->evaluate(summary) == logic.getTerm_true()) {
                PTRef newMustSummary = projectFormula(summary, predicateVars, *checkRes.model);
                assert(newMustSummary != PTRef_Undef);
                PTRef definitelyReachable = VersionManager(logic).targetFormulaToBase(newMustSummary);
                addMustSummary(pob.vertex, pob.bound, definitelyReachable);
                if (logProof) {
                    logNewFactIntoDatabase(definitelyReachable, pob.vertex, pob.bound - 1, edges[counter], *checkRes.model);
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

std::optional<ProofObligation> SpacerContext::computePredecessor(EId eid, ProofObligation const & pob) const {
    assert(pob.bound > 0);
    auto sourceBound = pob.bound - 1;
    auto const & sources = graph.getSources(eid);
    assert(not sources.empty());
    if (sources.size() == 1) { // Edge with single source, we only need to check if pob is reachable with over-approximation
        PTRef maySummary = getEdgeMaySummary(eid, sourceBound);
        auto res = sat(maySummary, pob.constraint);
        if (res.answer == QueryAnswer::SAT) {
            assert(res.model);
            // When this source is over-approximated and the edge becomes feasible -> extract next proof obligation
            auto source = sources[0];
            auto predicateVars = TermUtils(logic).getVars(graph.getStateVersion(source));
            PTRef newConstraint = projectFormula(logic.mkAnd(maySummary, pob.constraint), predicateVars, *res.model);
            PTRef newPob = VersionManager(logic).sourceFormulaToTarget(newConstraint); // ensure POB is target fla
            TRACE(2, "New proof obligation generated")
            return ProofObligation{source, sourceBound, newPob};
        } else if (res.answer == QueryAnswer::UNSAT) {
            TRACE(2, "Edge blocked by current may-summaries")
            return std::nullopt;
        }
        assert(false);
        throw std::logic_error("Unreachable!");
    }
    // Hyperedge case
    // TODO: Think if this could be optimized further
    bool maybeReachable = mayReachable(eid, pob.constraint, pob.bound - 1);
    if (not maybeReachable) {
        TRACE(2, "Edge blocked by current may-summaries")
        return std::nullopt;
    }
    // if we got there then it was not possible to prove that the edge can be taken or prove that it cannot be taken
    // examine the sources to generate a new proof obligation for this edge

    // Find the first source vertex such that over-approximating it (instead of under-approximating it) makes the edge feasible
    std::size_t vertexToRefine = 0; // vertex that is the last one to be over-approximated
    while(true) {
        PTRef mixedEdgeSummary = getEdgeMixedSummary(eid, sourceBound, vertexToRefine);
        auto res = sat(mixedEdgeSummary, pob.constraint);
        if (res.answer == QueryAnswer::SAT) {
            assert(res.model);
            // When this source is over-approximated and the edge becomes feasible -> extract next proof obligation
            auto source = sources[vertexToRefine];
            auto predicateVars = TermUtils(logic).getVars(graph.getStateVersion(source, vertexInstances.getInstanceNumber(eid, vertexToRefine)));
            PTRef newConstraint = projectFormula(logic.mkAnd(mixedEdgeSummary, pob.constraint), predicateVars, *res.model);
            PTRef newPob = VersionManager(logic).sourceFormulaToTarget(newConstraint); // ensure POB is target fla
            TRACE(2, "New proof obligation generated")
            return ProofObligation{sources[vertexToRefine], sourceBound, newPob};
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
            for (EId eid : incomingEdges(vid, graph)) {
                edgeRepresentations.push(getEdgeMaySummary(eid, level));
//                std::cout << "Representation of edge " << eid.id << " at level " << level << " is " << logic.printTerm(edgeRepresentations.last()) << std::endl;
            }
            PTRef body = logic.mkOr(edgeRepresentations);
//            std::cout << "Body representation of " << vid.id << " at level " << level << " is " << logic.printTerm(body) << std::endl;
            // Figure out which components of the may summary are implied by body at level n and so can be pushed to level n+1
//            std::cout << "Need to check " << maySummaryComponents.size() << " components for vertex " << vid.id << std::endl;
            bool allPushed = tryPushComponents(vid, level, body);
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
    auto maySummaryComponents = over.getComponents(vid, level);
    vec<PTRef> targetCandidates;
    targetCandidates.capacity(maySummaryComponents.size());
    vec<PTRef> activationLiterals;
    activationLiterals.capacity(maySummaryComponents.size());
    unsigned counter = 0;
    for (PTRef component : maySummaryComponents) {
        if (over.has(vid, level + 1, component)) {
            continue;
        }
        std::string name = ".act" + std::to_string(counter++);
        PTRef activationVariable = logic.mkBoolVar(name.c_str());
        targetCandidates.push(VersionManager(logic).baseFormulaToTarget(component));
        activationLiterals.push(activationVariable);
    }
    if (targetCandidates.size() == 0) { return true; }

    bool allPushed = true;
    SMTSolver solverWrapper(logic, SMTSolver::WitnessProduction::ONLY_MODEL);
    auto & solver = solverWrapper.getCoreSolver();
    solver.insertFormula(body);
    vec<PTRef> queries;
    queries.capacity(targetCandidates.size());
    for (auto i = 0; i < targetCandidates.size(); ++i) {
        queries.push(logic.mkAnd(activationLiterals[i], logic.mkNot(targetCandidates[i])));
    }
    solver.insertFormula(logic.mkOr(queries));

    auto disabled = 0u;
    while (disabled < queries.size_()) {
        solver.push();
        solver.insertFormula(logic.mkAnd(activationLiterals));
        auto res = solver.check();
        if (res == s_False) { break; }
        if (res != s_True) { throw std::logic_error("Solver could not solve a problem while trying to push components!"); }
        assert(res == s_True);
        auto model = solver.getModel();
        for (auto i = 0; i < activationLiterals.size(); ++i) {
            if (logic.isNot(activationLiterals[i])) { continue; } // already disabled
            if (model->evaluate(queries[i]) == logic.getTerm_true()) {
                ++disabled;
                assert(not logic.isNot(activationLiterals[i]));
                activationLiterals[i] = logic.mkNot(activationLiterals[i]);
            }
        }
        solver.pop();
    }

    for (auto i = 0; i < targetCandidates.size(); ++i) {
        if (not logic.isNot(activationLiterals[i])) {
            addMaySummary(vid, level + 1, VersionManager(logic).targetFormulaToBase(targetCandidates[i]));
        } else {
            allPushed = false;
        }
    }
    return allPushed;
}




PTRef SpacerContext::projectFormula(PTRef fla, const vec<PTRef> &toVars, Model & model) const {
    assert(std::all_of(toVars.begin(), toVars.end(), [this](PTRef var) { return logic.isVar(var); }));
//    std::cout << "Projecting " << logic.printTerm(fla) << " to variables ";
//    std::for_each(toVars.begin(), toVars.end(), [&](PTRef var) { std::cout << logic.printTerm(var) << ' '; });
//    std::cout << std::endl;
    auto varsInFla = TermUtils(logic).getVars(fla);

    vec<PTRef> toEliminate;
    for (PTRef var : varsInFla) {
        auto it = std::find(toVars.begin(), toVars.end(), var);
        if (it == toVars.end()) {
            toEliminate.push(var);
        }
    }
    ModelBasedProjection mbp(logic);
    PTRef res = mbp.project(fla, toEliminate, model);
//    std::cout << "\nResult is " << logic.printTerm(res) << std::endl;
    return res;
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
        PTRef summaryAsSource = VersionManager(logic).baseFormulaToSource(mustSummary, vertexInstances.getInstanceNumber(eid, sourceIndex));
//        std::cout << source.id << " with summary " << logic.pp(summaryAsSource) << '\n';
        bodyComponents.push(summaryAsSource);
    }
//    std::cout << std::flush;
    return logic.mkAnd(std::move(bodyComponents));
}

PTRef SpacerContext::getEdgeMaySummary(EId eid, std::size_t bound) const {
//    std::cout << "May summary:\n ";
    PTRef edgeLabel = graph.getEdgeLabel(eid);
//    std::cout << "Edge label: " << logic.pp(edgeLabel) << '\n';
    vec<PTRef> bodyComponents{edgeLabel};
//    std::cout << "Edge sources:\n";
    auto const & sources = graph.getSources(eid);
    for (unsigned sourceIndex = 0; sourceIndex < sources.size(); ++sourceIndex) {
        auto source = sources[sourceIndex];
        PTRef maySummary = getMaySummary(source, bound);
        PTRef summaryAsSource = VersionManager(logic).baseFormulaToSource(maySummary, vertexInstances.getInstanceNumber(eid, sourceIndex));
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
        PTRef summaryAsSource = VersionManager(logic).baseFormulaToSource(maySummary, vertexInstances.getInstanceNumber(eid, i));
        components.push(summaryAsSource);
    }
    for (std::size_t i = lastMayIndex + 1; i < sources.size(); ++i) {
        PTRef mustSummary = getMustSummary(sources[i], bound);
        PTRef summaryAsSource = VersionManager(logic).baseFormulaToSource(mustSummary, vertexInstances.getInstanceNumber(eid, i));
        components.push(summaryAsSource);
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
        auto components = under.getComponents(sourceNode, level);
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
        if (not found) {
            throw std::logic_error("Unreachable!");
        }
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
                             DerivationDatabase const & database,
                             ChcDirectedHyperGraph const & graph,
                             ChcDirectedHyperGraph::VertexInstances const & vertexInstances) {
    // Simplest way: Compute a model for a formula consisting of
    //  1. Constraint of the edge
    //  2. Premise constraints
    //  3. The fact we want to derive
    // This will give us a model from which we can compute the instances of the premises
    assert(entry.premiseInstances.empty());
    Logic & logic = graph.getLogic();
    EId edge = databaseEntry.incomingEdge;
    SMTSolver solverWrapper(logic, SMTSolver::WitnessProduction::ONLY_MODEL);
    auto & solver = solverWrapper.getCoreSolver();
    PTRef edgeConstraint = graph.getEdgeLabel(edge);
    solver.insertFormula(edgeConstraint);
//    std::cout << logic.pp(edgeConstraint) << '\n';
    VersionManager versionManager(logic);
    vec<PTRef> sourcePredicates;
    for (std::size_t i = 0; i < databaseEntry.premises.size(); ++i) {
        auto premiseEntry = database.getEntry(databaseEntry.premises[i]);
        assert(premiseEntry.derivedFact.node == graph.getSources(edge)[i]);
        auto instanceNumber = vertexInstances.getInstanceNumber(edge, i);
        PTRef premiseConstraint = versionManager.baseFormulaToSource(premiseEntry.derivedFact.fact, instanceNumber);
        sourcePredicates.push(graph.getStateVersion(premiseEntry.derivedFact.node, instanceNumber));
        solver.insertFormula(premiseConstraint);
//        std::cout << logic.pp(premiseConstraint) << '\n';
    }
    PTRef factInstance = entry.factInstance;
    auto targetNode = graph.getTarget(edge);
    if (targetNode != graph.getExit()) {
        assert(targetNode == logic.getSymRef(factInstance));
        PTRef targetVersion = graph.getNextStateVersion(graph.getTarget(edge));
        TermUtils::substitutions_map mapping;
        TermUtils(logic).mapFromPredicate(targetVersion, factInstance, mapping);
        vec<PTRef> factValues;
        for (auto const & varValue : mapping) {
            factValues.push(logic.mkEq(varValue.first, varValue.second));
        }
        PTRef factConstraint = logic.mkAnd(std::move(factValues));
        solver.insertFormula(factConstraint);
//        std::cout << logic.pp(factConstraint) << std::endl;
    }
    auto res = solver.check();
    if (res != s_True) {
        throw std::logic_error("Error in computing derivation!");
    }
    auto model = solver.getModel();
    std::transform(sourcePredicates.begin(), sourcePredicates.end(), std::back_inserter(entry.premiseInstances), [&](PTRef premise){
        auto vars = TermUtils(logic).predicateArgsInOrder(premise);
        vec<PTRef> evaluatedVars(vars.size());
        std::transform(vars.begin(), vars.end(), evaluatedVars.begin(), [&](PTRef var){ return model->evaluate(var); });
        PTRef premiseInstance = logic.insertTerm(logic.getSymRef(premise), std::move(evaluatedVars));
//        std::cout << logic.pp(premise) << " -> " << logic.pp(premiseInstance) << std::endl;
        return premiseInstance;
    });
}
}

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
        std::transform(entry.premiseInstances.begin(), entry.premiseInstances.end(), std::back_inserter(step.premises), [&](auto id) {
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
