//
// Created by Martin Blicha on 17.07.20.
//

#include "ChcGraph.h"

#include <iostream>
#include <map>

std::unique_ptr<ChcDirectedHyperGraph> ChcGraphBuilder::buildGraph(NormalizedChcSystem const & system) {
    std::vector<Vertex> vertices;
    std::vector<DirectedHyperEdge> edges;

    std::size_t id = 0;
    auto getOrCreateVertex = [&vertices, &id](SymRef sym) {
        auto vertexIt = std::find_if(vertices.begin(), vertices.end(), [&sym](Vertex const& v) { return v.predicateSymbol == sym; });
        if (vertexIt == vertices.end()) {
            vertexIt = vertices.insert(vertexIt, Vertex{.predicateSymbol = sym, .id = {id++}});
        }
        return vertexIt->id;
    };
    ChcSystem const & chcSystem = *system.normalizedSystem;
    // Special case to cover initial clauses, we are adding artificial "TRUE" starting predicate
    VId init = getOrCreateVertex(logic.getSym_true());
    // Special vertex representing error location, we assume it is represented by FALSE predicate in the system
    VId error = getOrCreateVertex(logic.getSym_false());
    for (auto const & clause : chcSystem.getClauses()) {
        auto const& head = clause.head;
        auto const& body = clause.body;
        auto toVertex = getOrCreateVertex(logic.getSymRef(head.predicate.predicate));

        std::vector<VId> from;
        for (auto const& bodyPredicate : body.uninterpretedPart) {
            from.push_back(getOrCreateVertex(logic.getSymRef(bodyPredicate.predicate)));
        }
        if (from.empty()) {
            from.push_back(init);
        }
        edges.push_back(DirectedHyperEdge{.from = std::move(from), .to = toVertex, .fla = body.interpretedPart});
    }
    return std::unique_ptr<ChcDirectedHyperGraph>(
        new ChcDirectedHyperGraph(std::move(vertices), std::move(edges),
                                  system.canonicalPredicateRepresentation,
                                  init,
                                  error
                                  ));
}

bool ChcDirectedHyperGraph::isNormalGraph() const {
    return std::all_of(edges.begin(), edges.end(), [](const DirectedHyperEdge& edge) { assert(not edge.from.empty()); return edge.from.size() == 1; });
}

std::unique_ptr<ChcDirectedGraph> ChcDirectedHyperGraph::toNormalGraph(Logic & logic) const {
    TimeMachine timeMachine(logic);
    VersionManager manager(logic);
    TermUtils utils(logic);
    LinearCanonicalPredicateRepresentation newPredicates(logic);
    for (Vertex v : vertices) {
        std::vector<PTRef> vars;
        PTRef originalTerm = predicates.getSourceTermFor(v.predicateSymbol);
        for (PTRef var : logic.getPterm(originalTerm)) {
            assert(logic.isVar(var));
            vars.push_back(var);
        }
        std::transform(vars.begin(), vars.end(), vars.begin(), [&](PTRef var){
            return manager.toBase(var);
        });
        newPredicates.addRepresentation(v.predicateSymbol, std::move(vars));
    }

    std::vector<DirectedEdge> normalEdges;
    std::transform(this->edges.begin(), this->edges.end(), std::back_inserter(normalEdges), [&](DirectedHyperEdge const& edge) {
        assert(edge.from.size() == 1);
        VId source = edge.from[0];
        VId target = edge.to;
        TermUtils::substitutions_map subst;
        {
            auto sourceVars = utils.getVarsFromPredicateInOrder(getStateVersion(source));
            for (PTRef sourceVar : sourceVars) {
                PTRef newVar = timeMachine.getVarVersionZero(manager.toBase(sourceVar));
                subst.insert({sourceVar, newVar});
            }
        }
        {
            auto targetVars = utils.getVarsFromPredicateInOrder(getNextStateVersion(target));
            for (PTRef targetVar : targetVars) {
                PTRef newVar = timeMachine.sendVarThroughTime(timeMachine.getVarVersionZero(manager.toBase(targetVar)), 1);
                subst.insert({targetVar, newVar});
            }
        }

        PTRef newLabel = TermUtils(logic).varSubstitute(edge.fla.fla, subst);
        return DirectedEdge{.from = edge.from[0], .to = edge.to, .fla = {newLabel}};
    });
    return std::unique_ptr<ChcDirectedGraph>( new ChcDirectedGraph(vertices, std::move(normalEdges), std::move(newPredicates), entry, exit));
}

void ChcDirectedGraph::toDot(std::ostream & out, Logic const& logic) const {

    out << "digraph proof {" << '\n';

    std::map<VId, std::string> dotIds;

    for (auto const & vertex : vertices) {
        auto id = vertex.id;
        auto pred = this->getStateVersion(id);
        dotIds.insert(std::make_pair(id, "n" + std::to_string(id.id)));
        std::string label = logic.printTerm(pred);
        out << dotIds[id] << "\t[label =  \"" << label << "\"];\n";
    }

    for (auto const& edge : edges) {
        out << dotIds[edge.from] << " -> " << dotIds[edge.to] << " [label = \"" << logic.printTerm(edge.fla.fla) << "\"];\n";
    }

    out << "}" << std::endl;
}

DirectedEdge ChcDirectedGraph::reverseEdge(DirectedEdge const & edge, TermUtils & utils) const {
    VId rfrom = edge.to;
    VId rto = edge.from;
    PTRef ofla = edge.fla.fla;
    std::unordered_map<PTRef, PTRef, PTRefHash> subst;
    // variables from 'from' are expressed as state vars, they must be changed to next state
    utils.insertVarPairsFromPredicates(this->getStateVersion(edge.from), this->getNextStateVersion(edge.from), subst);
    // variables from 'to' are expressed as next state vars, they must be changed to state
    utils.insertVarPairsFromPredicates(this->getNextStateVersion(edge.to), this->getStateVersion(edge.to), subst);
    // simulataneous substitution
    PTRef rfla = utils.varSubstitute(ofla, subst);
    return DirectedEdge{.from = rfrom, .to = rto, .fla = InterpretedFla{rfla}};
}

ChcDirectedGraph ChcDirectedGraph::reverse(Logic & logic) const {
    // same vertices, same canonical representation, switch entry and exit and reverse edges
    // NOTE: reversing edge means flipping state and next state variables
    assert(vertices[entry.id].predicateSymbol == logic.getSym_true() and vertices[exit.id].predicateSymbol == logic.getSym_false());
    auto rvertices = vertices;
    std::swap(rvertices[entry.id].predicateSymbol, rvertices[exit.id].predicateSymbol);
    TermUtils utils(logic);
    std::vector<DirectedEdge> redges;
    for (auto const& edge : this->edges) {
        redges.push_back(reverseEdge(edge, utils));
    }
    auto rentry = exit;
    auto rexit = entry;
    return ChcDirectedGraph(std::move(rvertices), std::move(redges), this->predicates, rentry, rexit);
}

void ChcDirectedGraph::contractVertex(VId vid, Logic & logic) {
    auto adjacencyList = AdjacencyListsGraphRepresentation::from(*this);
    auto const & incomingEdges = adjacencyList.getIncomingEdgesFor(vid);
    auto const & outgoingEdges = adjacencyList.getOutgoingEdgesFor(vid);
    for (EId incomingId : incomingEdges) {
        assert(getEdge(incomingId).to != getEdge(incomingId).from);
        for (EId outgoingId : outgoingEdges) {
            assert(getEdge(outgoingId).to != getEdge(outgoingId).from);
            mergeEdges(incomingId, outgoingId, logic);
        }
    }
    deleteNode(vid);
}

PTRef ChcDirectedGraph::mergeLabels(const DirectedEdge & incoming, const DirectedEdge & outgoing, Logic & logic) {
    assert(incoming.to == outgoing.from);
    PTRef incomingLabel = incoming.fla.fla;
    PTRef outgoingLabel = outgoing.fla.fla;
    TermUtils utils(logic);
    TermUtils::substitutions_map subMap;
    utils.insertVarPairsFromPredicates(getNextStateVersion(incoming.to), getStateVersion(outgoing.from), subMap);
    PTRef updatedIncomingLabel = utils.varSubstitute(incomingLabel, subMap);
    PTRef combinedLabel = logic.mkAnd(updatedIncomingLabel, outgoingLabel);
//    std::cout << logic.pp(combinedLabel) << '\n';
    PTRef simplifiedLabel = TrivialQuantifierElimination(logic).tryEliminateVars(utils.getVarsFromPredicateInOrder(
        getStateVersion(outgoing.from)), combinedLabel);
//    std::cout << logic.pp(simplifiedLabel) << '\n';
    return simplifiedLabel;
}

void ChcDirectedGraph::mergeEdges(EId incomingId, EId outgoingId, Logic & logic) {
    auto const & incoming = getEdge(incomingId);
    auto const & outgoing = getEdge(outgoingId);
    if (incoming.to != outgoing.from) { throw std::logic_error("ChcDirectedGraph::mergeEdges: Trying to merge edges without common node!\n"); }

    VId source = incoming.from;
    VId target = outgoing.to;
    PTRef mergedLabel = mergeLabels(incoming, outgoing, logic);
    edges.push_back(DirectedEdge{.from = source, .to = target, .fla = InterpretedFla{mergedLabel}});
}

void ChcDirectedGraph::mergeMultiEdges(Logic & logic) {
    std::unordered_map<std::pair<VId, VId>, std::vector<unsigned>, EdgeHasher> buckets;
    std::vector<unsigned> edgesToRemove;
    for (unsigned i = 0; i < edges.size(); ++i) {
        auto const & edge = edges[i];
        auto pair = std::make_pair(edge.from, edge.to);
        buckets[pair].push_back(i);
    }
    for (auto const & bucketEntry : buckets) {
        auto const & bucket = bucketEntry.second;
        if (bucket.size() < 2) { continue; }
        vec<PTRef> labels;
        labels.capacity(bucket.size());
        for (auto index : bucket) {
            labels.push(edges[index].fla.fla);
        }
        edges[bucket[0]].fla = InterpretedFla{logic.mkOr(std::move(labels))};
        std::for_each(bucket.begin() + 1, bucket.end(), [&edgesToRemove](unsigned i) { edgesToRemove.push_back(i); });
    }
    std::sort(edgesToRemove.begin(), edgesToRemove.end());
    std::for_each(edgesToRemove.crbegin(), edgesToRemove.crend(), [this](auto index) { edges.erase(begin(edges) + index); });
}

void ChcDirectedGraph::deleteNode(VId vid) {
    assert(vid != getEntryId() and vid != getExitId());
    edges.erase(std::remove_if(edges.begin(), edges.end(), [vid](DirectedEdge const & edge) {
        return edge.from == vid or edge.to == vid;
    }), edges.end());

    VId last = vertices.back().id;
    vertices[vid.id] = vertices.back();
    vertices[vid.id].id = vid;
    vertices.pop_back();
    for (DirectedEdge & edge : edges) {
        if (edge.to == last) { edge.to = vid; }
        if (edge.from == last) { edge.from = vid; }
    }
}

AdjacencyListsGraphRepresentation AdjacencyListsGraphRepresentation::from(const ChcDirectedGraph & graph) {
    auto edges = graph.getEdges();
    auto vertices = graph.getVertices();
    std::vector<std::vector<EId>> incoming;
    std::vector<std::vector<EId>> outgoing;
    const std::size_t N = vertices.size();
    incoming.resize(N);
    outgoing.resize(N);
    for (EId eid : edges) {
        incoming[graph.getTarget(eid).id].push_back(eid);
        outgoing[graph.getSource(eid).id].push_back(eid);
    }
    return AdjacencyListsGraphRepresentation(std::move(incoming), std::move(outgoing), [&graph](EId eid) { return graph.getEdge(eid); });
}

class DFS {
    AdjacencyListsGraphRepresentation const * graph;
    std::vector<bool> marked;

    template<typename TPreorderAction, typename TPostorderAction>
    void runOnVertex(VId v, TPreorderAction const & preorder, TPostorderAction const & postorder) {
        if (marked[v.id]) { return; }
        marked[v.id] = true;
        preorder(v);
        for (EId outEdge : graph->getOutgoingEdgesFor(v)) {
            runOnVertex(graph->getEdge(outEdge).to, preorder, postorder);
        }
        postorder(v);
    }
public:
    template<typename TPreorderAction, typename TPostorderAction>
    void run(TPreorderAction const & preorder, TPostorderAction const & postorder, AdjacencyListsGraphRepresentation const & graph) && {
        auto vertexCount = graph.getVertexNum();
        marked.resize(vertexCount, false);
        this->graph = &graph;
        for (std::size_t i = 0; i < vertexCount; ++i) {
            runOnVertex(VId{i}, preorder, postorder);
        }
    }
};

std::vector<VId> AdjacencyListsGraphRepresentation::reversePostOrder() const {
    std::vector<VId> order;
    DFS().run([](VId){}, [&order](VId v){ order.push_back(v); }, *this);
    std::reverse(order.begin(), order.end());
    return order;
}

std::vector<VId> AdjacencyListsGraphRepresentation::postOrder() const {
    std::vector<VId> order;
    DFS().run([](VId){}, [&order](VId v){ order.push_back(v); }, *this);
    return order;
}

std::unique_ptr<ChcDirectedHyperGraph> ChcDirectedGraph::toHyperGraph(Logic & logic) const {
    TimeMachine timeMachine(logic);
    VersionManager manager(logic);
    TermUtils utils(logic);
    NonlinearCanonicalPredicateRepresentation newPredicates(logic);
    for (Vertex v : vertices) {
        PTRef originalTerm = predicates.getSourceTermFor(v.predicateSymbol);
        std::vector<PTRef> vars = utils.getVarsFromPredicateInOrder(originalTerm);
        std::transform(vars.begin(), vars.end(), vars.begin(), [&](PTRef var){
            return timeMachine.getUnversioned(var);
        });
        newPredicates.addRepresentation(v.predicateSymbol, std::move(vars));
    }

    std::vector<DirectedHyperEdge> newEdges;
    std::transform(this->edges.begin(), this->edges.end(), std::back_inserter(newEdges), [&](DirectedEdge const & edge) {
        VId source = edge.from;
        VId target = edge.to;
        TermUtils::substitutions_map subst;
        {
            auto sourceVars = utils.getVarsFromPredicateInOrder(getStateVersion(source));
            for (PTRef sourceVar : sourceVars) {
                assert(timeMachine.isVersioned(sourceVar));
                PTRef newVar = manager.toSource(timeMachine.getUnversioned(sourceVar));
                subst.insert({sourceVar, newVar});
            }
        }
        {
            auto targetVars = utils.getVarsFromPredicateInOrder(getNextStateVersion(target));
            for (PTRef targetVar : targetVars) {
                assert(timeMachine.isVersioned(targetVar));
                PTRef newVar = manager.toTarget(timeMachine.getUnversioned(targetVar));
                subst.insert({targetVar, newVar});
            }
        }

        PTRef newLabel = TermUtils(logic).varSubstitute(edge.fla.fla, subst);
        return DirectedHyperEdge{.from = {edge.from}, .to = edge.to, .fla = {newLabel}};
    });
    return std::unique_ptr<ChcDirectedHyperGraph>( new ChcDirectedHyperGraph(vertices, std::move(newEdges), std::move(newPredicates), entry, exit));
}

std::optional<EId> getSelfLoopFor(VId node, ChcDirectedGraph const & graph, AdjacencyListsGraphRepresentation const & adjacencyRepresentation) {
    auto const & outEdges = adjacencyRepresentation.getOutgoingEdgesFor(node);
    auto it = std::find_if(outEdges.begin(), outEdges.end(), [&](EId eid) {
        return graph.getEdge(eid).to == node;
    });
    return it != outEdges.end() ? *it : std::optional<EId>{};
}