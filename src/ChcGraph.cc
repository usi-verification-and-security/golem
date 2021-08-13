//
// Created by Martin Blicha on 17.07.20.
//

#include "ChcGraph.h"

#include <iostream>

std::unique_ptr<ChcDirectedHyperGraph> ChcGraphBuilder::buildGraph(NormalizedChcSystem const & system) {
    std::vector<Vertex> vertices;
    std::vector<DirectedHyperEdge> edges;

    std::size_t id = 0;
    auto getOrCreateVertex = [&vertices, &id](SymRef sym) {
        auto vertexIt = std::find_if(vertices.begin(), vertices.end(), [&sym](Vertex const& v) { return v.predicateSymbol == sym; });
        if (vertexIt == vertices.end()) {
            vertexIt = vertices.insert(vertexIt, Vertex{.predicateSymbol = sym, .id = id++});
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

std::unique_ptr<ChcDirectedGraph> ChcDirectedHyperGraph::toNormalGraph() const {
    std::vector<DirectedEdge> normalEdges;
    std::transform(this->edges.begin(), this->edges.end(), std::back_inserter(normalEdges), [](DirectedHyperEdge const& edge) {
        return DirectedEdge{.from = edge.from[0], .to = edge.to, .fla = edge.fla};
    });
    return std::unique_ptr<ChcDirectedGraph>( new ChcDirectedGraph(vertices, std::move(normalEdges), predicates, entry, exit));
}

void ChcDirectedGraph::toDot(ostream & out, Logic const& logic) const {

    out << "digraph proof {" << endl;

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

std::unique_ptr<ChcDirectedHyperGraph> ChcDirectedGraph::toHyperGraph() const {
    std::vector<DirectedHyperEdge> hyperEdges;
    std::transform(this->edges.begin(), this->edges.end(), std::back_inserter(hyperEdges), [](DirectedEdge const& edge) {
        return DirectedHyperEdge{.from = {edge.from}, .to = edge.to, .fla = edge.fla};
    });
    return std::unique_ptr<ChcDirectedHyperGraph>( new ChcDirectedHyperGraph(vertices, std::move(hyperEdges), predicates, entry, exit));
}
