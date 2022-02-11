/*
 * Copyright (c) 2021-2022, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "Spacer.h"
#include "ModelBasedProjection.h"

#include <unordered_map>
#include <unordered_set>

#define TRACE_LEVEL 0

#define TRACE(l,m) if (TRACE_LEVEL >= l) { std::cout << m << std::endl; }

class ApproxMap {
public:
    vec<PTRef> getComponents(VId vid, std::size_t bound) {
        vec<PTRef> res;
        ensureBound(bound);
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

    void insert(VId vid, std::size_t bound, PTRef summary) {
        ensureBound(bound);
        auto & boundMap = innerMap[bound];
        auto & components = boundMap[vid];
        components.insert(summary);
    }

    bool has(VId vid, std::size_t bound, PTRef summary) {
        ensureBound(bound);
        auto const & boundMap = innerMap[bound];
        auto it = boundMap.find(vid);
        if (it != boundMap.end()) {
            return it->second.find(summary) != it->second.end();
        }
        return false;
    }

private:
    std::vector<std::unordered_map<VId, std::unordered_set<PTRef, PTRefHash>, VertexHasher>> innerMap; // bound -> vertex -> conjuncts of approximation

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
    VId vertex;
    std::size_t bound;
    PTRef constraint;
};

bool operator<(ProofObligation const& pob1, ProofObligation const& pob2) {
    return pob1.bound < pob2.bound or
           (pob1.bound == pob2.bound and pob1.vertex.id < pob2.vertex.id);
}

bool operator>(ProofObligation const& pob1, ProofObligation const& pob2) {
    return pob1.bound > pob2.bound or
           (pob1.bound == pob2.bound and pob1.vertex.id > pob2.vertex.id);
}

struct PriorityQueue {

    void push(ProofObligation pob) { pqueue.push(pob); }
    ProofObligation const & peek() const { return pqueue.top(); }
    void pop() { pqueue.pop(); }
    bool empty() const { return pqueue.empty(); }
private:
    std::priority_queue<ProofObligation, std::vector<ProofObligation>, std::greater<ProofObligation>> pqueue;
};

class SpacerContext {
    Logic & logic;
    ChcDirectedHyperGraph const & graph;

    UnderApproxMap under;
    OverApproxMap over;

    std::size_t lowestChangedLevel = 0;

    PTRef getMustSummary(VId vid, std::size_t bound) {
        return logic.mkOr(under.getComponents(vid, bound));
    }

    PTRef getMaySummary(VId vid, std::size_t bound) {
        return logic.mkAnd(over.getComponents(vid, bound));
    }

    enum class BoundedSafetyResult { SAFE, UNSAFE };

    BoundedSafetyResult boundSafety(std::size_t currentBound);

    enum class InductiveCheckAnswer { INDUCTIVE, NOT_INDUCTIVE };

    struct InductiveCheckResult {
        InductiveCheckAnswer answer;
        std::size_t inductiveLevel;
    };

    InductiveCheckResult isInductive(std::size_t currentBound);

    bool tryPushComponents(VId , std::size_t, PTRef);


    enum class QueryAnswer {VALID, INVALID, ERROR, UNKNOWN};
    struct QueryResult {
        QueryAnswer answer;
        std::unique_ptr<Model> model;
    };
    QueryResult implies(PTRef antecedent, PTRef consequent);

    struct ItpQueryResult {
        QueryAnswer answer;
        PTRef interpolant = PTRef_Undef;
    };
    ItpQueryResult interpolatingImplies(PTRef antecedent, PTRef consequent);

    struct MustReachResult {
        bool applied = false;
        PTRef mustSummary = PTRef_Undef;
    };

    struct MayReachResult {
        bool blocked = false;
        PTRef maySummary = PTRef_Undef;
    };

    MustReachResult mustReachable(EId eid, PTRef targetConstraint, std::size_t bound);

    MayReachResult mayReachable(EId eid, PTRef targetConstraint, std::size_t bound);

    PTRef projectFormula(PTRef fla, vec<PTRef> const & vars, Model* model);


public:
    SpacerContext(Logic & logic, ChcDirectedHyperGraph const & graph): logic(logic), graph(graph) {
        for (VId vid : graph.getVertices()) {
            PTRef toInsert = vid == graph.getEntryId() ? logic.getTerm_true() : logic.getTerm_false();
            over.insert(vid, 0, toInsert);
            under.insert(vid, 0, toInsert);
        }
    }

    GraphVerificationResult run();
};

GraphVerificationResult Spacer::solve(ChcDirectedHyperGraph & system) {
    return SpacerContext(logic, system).run();
}

GraphVerificationResult Spacer::solve(const ChcDirectedGraph & system) {
    auto hyperGraph = system.toHyperGraph();
    return SpacerContext(logic, *hyperGraph).run();
}

GraphVerificationResult SpacerContext::run() {
    std::size_t currentBound = 1;
    while(true) {
        over.insert(graph.getEntryId(), currentBound, logic.getTerm_true());
        under.insert(graph.getEntryId(), currentBound, logic.getTerm_true());
        auto boundedResult = boundSafety(currentBound);
        switch (boundedResult) {
            case BoundedSafetyResult::UNSAFE:
                return GraphVerificationResult(VerificationResult::UNSAFE);
            case BoundedSafetyResult::SAFE: {
                auto inductiveResult = isInductive(currentBound);
                if (inductiveResult.answer == InductiveCheckAnswer::INDUCTIVE) {
                    std::unordered_map<PTRef, PTRef, PTRefHash> solution;
                    auto inductiveLevel = inductiveResult.inductiveLevel;
                    for (VId vid : graph.getVertices()) {
                        PTRef predicate = graph.getStateVersion(vid);
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
                    return GraphVerificationResult(VerificationResult::SAFE, ValidityWitness(std::move(solution)));
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


std::vector<EId> incomingEdges(VId v, ChcDirectedHyperGraph const & graph) {
    auto res = graph.getEdges();
    res.erase(std::remove_if(res.begin(), res.end(), [&](EId e) { return graph.getEdge(e).to != v; }), res.end());
    return res;
}

SpacerContext::BoundedSafetyResult SpacerContext::boundSafety(std::size_t currentBound) {
    TRACE(1, "\nRunning bounded safety check at level " << currentBound)
    VId query = graph.getExitId();
    PriorityQueue pqueue;
    pqueue.push(ProofObligation{query, currentBound, logic.getTerm_true()});
    lowestChangedLevel = currentBound;
    while(not pqueue.empty()) {
        TRACE(2, "Examining proof obligation " << pqueue.peek().vertex.id)
        auto const & pob = pqueue.peek();
        if (pob.vertex == graph.getEntryId()) {
            assert(false); // With the must summaries, we actually never finish here
            return BoundedSafetyResult::UNSAFE;
        }
        auto edges = incomingEdges(pob.vertex, graph);
        bool mustReached = false;
        std::vector<ProofObligation> newProofObligations;
        for (EId edgeId : edges) {
            TRACE(2, "Considering edge " << edgeId.id)
            auto edge = graph.getEdge(edgeId);
            assert(edge.to == pob.vertex);
            // test if vertex can be reached using must summaries
            assert(pob.bound > 0);
            auto result = mustReachable(edgeId, pob.constraint, pob.bound - 1);
            if (result.applied) {
                TRACE(1, "Must summary successfully applied!")
                assert(result.mustSummary != PTRef_Undef);
                PTRef definitelyReachable = TimeMachine(logic).sendFlaThroughTime(result.mustSummary, -1);
                // definitelyReachable must be current state fla in vertex pob.vertex
                under.insert(pob.vertex, pob.bound, definitelyReachable);
                if (pob.vertex == query) {
                    return BoundedSafetyResult::UNSAFE; // query is reachable
                }
                pqueue.pop();
                mustReached = true;
                break;
            } else {
                auto result = mayReachable(edgeId, pob.constraint, pob.bound - 1);
                if (result.blocked) {
                    TRACE(2, "Edge blocked by current may-summaries")
                    continue; // This edge has been blocked, we can continue
                }
            }
            // if we got there then it was not possible to prove that the edge can be taken or prove that it cannot be taken
            // examine the sources to generate a new proof obligation for this edge

            // Find the first source vertex such that under-approximating it (instead of over-approximating it) makes the target unreachable
            auto const& targets = edge.from;
            assert(not targets.empty());
            std::size_t vertexToRefine = 0; // vertex that is the last one to be over-approximated
            auto bound = pob.bound - 1;
            // looking for vertex which is the point where using over-approximation makes the edge feasible
            while(true) {
                vec<PTRef> components;
                for (std::size_t i = 0; i <= vertexToRefine; ++i) {
                    components.push(getMaySummary(targets[i], bound));
                }
                for (std::size_t i = vertexToRefine + 1; i < targets.size(); ++i) {
                    components.push(getMustSummary(targets[i], bound));
                }
                components.push(edge.fla.fla);
                PTRef body = logic.mkAnd(components);
                auto res = implies(body, logic.mkNot(pob.constraint));
                if (res.answer == QueryAnswer::INVALID) {
                    // When this target is over-approximated and the edge becomes feasible -> extract next proof obligation
                    VId source = targets[vertexToRefine];
                    auto predicateVars = TermUtils(logic).getVars(graph.getStateVersion(source));
                    PTRef newConstraint = projectFormula(logic.mkAnd(body, pob.constraint), predicateVars, res.model.get());
                    PTRef newPob = TimeMachine(logic).sendFlaThroughTime(newConstraint, 1); // ensure POB is next-state fla
                    newProofObligations.push_back(ProofObligation{targets[vertexToRefine], bound, newPob});
                    TRACE(2, "New proof obligation generated")
                    break;
                }
                if (res.answer == QueryAnswer::VALID) {
                    // Continue with the next vertex to refine
                    ++vertexToRefine;
                    assert(vertexToRefine < targets.size());
                    continue;
                }
                assert(false);
                throw std::logic_error("Unreachable!");
            }
        }
        if (mustReached) { continue; }
        else {
            if (newProofObligations.empty()) {
                // all edges are blocked; compute new lemma blocking the current proof obligation
                // TODO:
                vec<PTRef> edgeRepresentations;
                for (EId eid : edges) {
                    vec<PTRef> sourceFlas;
                    auto sources = graph.getSources(eid);
                    for (VId source : sources) {
                        sourceFlas.push(getMaySummary(source, pob.bound - 1));
                    }
                    sourceFlas.push(graph.getEdgeLabel(eid));
                    edgeRepresentations.push(logic.mkAnd(sourceFlas));
                }
                auto res = interpolatingImplies(logic.mkOr(edgeRepresentations), logic.mkNot(pob.constraint));
                assert(res.answer == QueryAnswer::VALID);
                if (res.answer != QueryAnswer::VALID) {
                    throw std::logic_error("All edges should have been blocked, but they are not!");
                }
                PTRef newLemma = TimeMachine(logic).sendFlaThroughTime(res.interpolant, -1);
                TRACE(2, "Learnt new lemma for " << pob.vertex.id << " at level " << pob.bound << " - " << logic.pp(newLemma))
                over.insert(pob.vertex, pob.bound, newLemma);
                if (pob.bound < lowestChangedLevel) {
                    lowestChangedLevel = pob.bound;
                }
                pqueue.pop(); // This POB has been successfully blocked
            } else {
                for (auto const& npob : newProofObligations) {
                    TRACE(2,"Pushing new proof obligation " << logic.pp(npob.constraint) << " for " << npob.vertex.id << " at level " << npob.bound)
                    pqueue.push(npob);
                }
            }
        }
    } // end of main cycle
    return BoundedSafetyResult::SAFE; // not reachable at this bound
}

SpacerContext::QueryResult SpacerContext::implies(PTRef antecedent, PTRef consequent) {
    SMTConfig config;
    MainSolver solver(logic, config, "checker");
    solver.insertFormula(antecedent);
    solver.insertFormula(logic.mkNot(consequent));
    auto res = solver.check();
    QueryResult qres;
    if (res == s_True) {
        qres.answer = QueryAnswer::INVALID;
        qres.model = solver.getModel();
    }
    else if (res == s_False) {
        qres.answer = QueryAnswer::VALID;
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

SpacerContext::ItpQueryResult SpacerContext::interpolatingImplies(PTRef antecedent, PTRef consequent) {
    SMTConfig config;
    const char* msg = "ok";
    bool set = config.setOption(SMTConfig::o_produce_inter, SMTOption(true), msg);
    assert(set); (void)set;
    config.setSimplifyInterpolant(4);
    MainSolver solver(logic, config, "checker");
    solver.insertFormula(antecedent);
    solver.insertFormula(logic.mkNot(consequent));
    auto res = solver.check();
    ItpQueryResult qres;
    if (res == s_True) {
        qres.answer = QueryAnswer::INVALID;
    }
    else if (res == s_False) {
        qres.answer = QueryAnswer::VALID;
        auto itpCtx = solver.getInterpolationContext();
        std::vector<PTRef> itps;
        ipartitions_t mask = 0;
        setbit(mask, 0);
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

SpacerContext::MustReachResult SpacerContext::mustReachable(EId eid, PTRef targetConstraint, std::size_t bound) {
    auto edge = graph.getEdge(eid);
    VId target = edge.to;
    PTRef edgeLabel = edge.fla.fla;
    vec<PTRef> bodyComponents{edgeLabel};
    for (VId source : edge.from) {
        PTRef mustSummary = getMustSummary(source, bound);
        bodyComponents.push(mustSummary);
    }
    PTRef body = logic.mkAnd(bodyComponents);
    auto implCheckRes = implies(body, logic.mkNot(targetConstraint));
    MustReachResult res;
    if (implCheckRes.answer == SpacerContext::QueryAnswer::INVALID) {
        res.applied = true;
        // eliminate variables from body except variables present in predicate of edge target
        auto predicateVars = TermUtils(logic).getVars(graph.getNextStateVersion(target));
        PTRef newMustSummary = projectFormula(body, predicateVars, implCheckRes.model.get()); // TODO: is body OK, or do I need to project also the head?
        res.mustSummary = newMustSummary;
    } else {
        res.applied = false;
        res.mustSummary = PTRef_Undef;
    }
    return res;
}

SpacerContext::MayReachResult SpacerContext::mayReachable(EId eid, PTRef targetConstraint, std::size_t bound) {
    auto edge = graph.getEdge(eid);
    VId target = edge.to;
    PTRef edgeLabel = edge.fla.fla;
    vec<PTRef> bodyComponents{edgeLabel};
    for (VId source : edge.from) {
        PTRef maySummary = getMaySummary(source, bound);
        bodyComponents.push(maySummary);
    }
    PTRef body = logic.mkAnd(bodyComponents);
    auto implCheckRes = interpolatingImplies(body, logic.mkNot(targetConstraint));
    MayReachResult res;
    if (implCheckRes.answer == SpacerContext::QueryAnswer::VALID) {
        res.blocked = true;
        res.maySummary = implCheckRes.interpolant;
    } else {
        res.blocked = false;
        res.maySummary = PTRef_Undef;
    }
    return res;
}

// *********** INDUCTIVE CHECK *****************************
SpacerContext::InductiveCheckResult SpacerContext::isInductive(std::size_t maxLevel) {
    std::size_t minLevel = lowestChangedLevel;
    for (std::size_t level = minLevel; level <= maxLevel; ++level) {
        bool inductive = true;
//        std::cout << "Checking level " << level << std::endl;
        for (VId vid : graph.getVertices()) {
//            std::cout << " Checking vertex " << vid.id << std::endl;
            // encode body as disjunction over all the incoming edges
            vec<PTRef> edgeRepresentations;
            for (EId eid : incomingEdges(vid, graph)) {
                vec<PTRef> edgeBodyArgs;
                for (VId source : graph.getSources(eid)) {
                    edgeBodyArgs.push(getMaySummary(source, level));
                }
                edgeBodyArgs.push(graph.getEdgeLabel(eid));
                edgeRepresentations.push(logic.mkAnd(edgeBodyArgs));
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

bool SpacerContext::tryPushComponents(VId vid, std::size_t level, PTRef body) {
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
        PTRef nextStateComponent = TimeMachine(logic).sendFlaThroughTime(component, 1);
//        std::cout << " Checking component " << logic.printTerm(nextStateComponent) << std::endl;
        solver.push();
        solver.insertFormula(logic.mkNot(nextStateComponent));
        auto res = solver.check();
        if (res == s_False) {
            over.insert(vid, level + 1, component);
        } else {
            allPushed = false;
        }
        solver.pop();
    }
    return allPushed;
}




PTRef SpacerContext::projectFormula(PTRef fla, const vec<PTRef> &toVars, Model *model) {
    if (not model) {
        throw std::logic_error("Model not provided to MBP!");
    }
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
    PTRef res = mbp.project(fla, toEliminate, *model);
//    std::cout << "\nResult is " << logic.printTerm(res) << std::endl;
    return res;
}
