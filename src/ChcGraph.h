//
// Created by Martin Blicha on 17.07.20.
//

#ifndef OPENSMT_CHCGRAPH_H
#define OPENSMT_CHCGRAPH_H

#include "ChcSystem.h"
#include "TermUtils.h"
#include "Normalizer.h"

#include <memory>
#include <iosfwd>

struct VId {
    std::size_t id;
};

struct EId {
	std::size_t id;
};


inline bool operator ==(VId first, VId second) { return first.id == second.id; }
inline bool operator !=(VId first, VId second) { return not(first == second); }
inline bool operator <(VId first, VId second) { return first.id < second.id; }

inline bool operator ==(EId first, EId second) { return first.id == second.id; }
inline bool operator !=(EId first, EId second) { return not(first == second); }
inline bool operator <(EId first, EId second) { return first.id < second.id; }

struct Vertex{
    SymRef predicateSymbol;
    VId id;
};

struct DirectedHyperEdge {
    std::vector<VId> from;
    VId to;
    InterpretedFla fla;
};

struct DirectedEdge {
    VId from;
    VId to;
    InterpretedFla fla;
};

class ChcDirectedGraph;

class AdjacencyListsGraphRepresentation {
    using AdjacencyList = std::vector<std::vector<EId>>;
    AdjacencyList incomingEdges;
    AdjacencyList outgoingEdges;
    std::function<DirectedEdge(EId)> edgeGetter;

	AdjacencyListsGraphRepresentation(AdjacencyList && incoming, AdjacencyList && outgoing, std::function<DirectedEdge(EId)> && edgeGetter)
		: incomingEdges(std::move(incoming)),
		  outgoingEdges(std::move(outgoing)),
		  edgeGetter(std::move(edgeGetter))
	{}

public:
    static AdjacencyListsGraphRepresentation from(ChcDirectedGraph const& graph);
    std::vector<EId> const & getIncomingEdgesFor(VId v) const { return incomingEdges[v.id]; }
    std::vector<EId> const & getOutgoingEdgesFor(VId v) const { return outgoingEdges[v.id]; }

    std::size_t getVertexNum() const { return incomingEdges.size(); }
	DirectedEdge getEdge(EId e) const { return edgeGetter(e); }
    std::vector<VId> reversePostOrder() const;

    std::optional<EId> getSelfLoopFor(VId) const;
};

class ChcDirectedHyperGraph;

// Helper structure for lookup of edges given its vertices
struct EdgeHasher {
    std::size_t operator()(std::pair<VId, VId> pair) const {
        // From Boost hash_combine
        std::hash<std::size_t> hasher;
        std::size_t res = 0;
        res ^= hasher(pair.first.id) + 0x9e3779b9 + (res<<6) + (res>>2);
        res ^= hasher(pair.second.id) + 0x9e3779b9 + (res<<6) + (res>>2);
        return res;
    }
};

struct VertexHasher {
    std::size_t operator()(VId vid) const {
        std::hash<std::size_t> hasher;
        return hasher(vid.id);
    }
};

class ChcDirectedGraph {

    VId entry;
    VId exit;

    std::vector<Vertex> vertices;
    std::vector<DirectedEdge> edges;
    CanonicalPredicateRepresentation predicates;

    // graph transformations
    friend class GraphTransformations;
    void contractVertex(VId vid, Logic & logic);
    void mergeEdges(EId incoming, EId outgoing, Logic & logic);
    void deleteNode(VId vid);
    PTRef mergeLabels(DirectedEdge const & incoming, DirectedEdge const & outgoing, Logic & logic);
    void mergeMultiEdges(Logic & logic);

    template<typename TFun>
    void removeEdges(TFun fun) {
        edges.erase(std::remove_if(edges.begin(), edges.end(), fun), edges.end());
    }

public:
    ChcDirectedGraph(std::vector<Vertex> vertices, std::vector<DirectedEdge> edges, CanonicalPredicateRepresentation predicates, VId entry, VId exit) :
        vertices(std::move(vertices)), edges(std::move(edges)), predicates(std::move(predicates)), entry(entry), exit(exit)
    {
        assert(entry != exit);
    }

    void toDot(std::ostream& out, Logic const & logic) const;
    ChcDirectedGraph reverse(Logic&) const;
    DirectedEdge reverseEdge(DirectedEdge const & edge, TermUtils & utils) const;

    std::vector<Vertex> getVertexCopies() const { return vertices; }

    std::vector<DirectedEdge> getEdgeCopies() const { return edges; }

    std::vector<VId> getVertices() const {
        std::vector<VId> res;
        std::size_t counter = 0;
        std::generate_n(std::back_inserter(res), vertices.size(), [&counter]() { return VId{counter++}; });
        return res;
    }

    std::vector<EId> getEdges() const {
        std::vector<EId> res;
        std::size_t counter = 0;
        std::generate_n(std::back_inserter(res), edges.size(), [&counter]() { return EId{counter++}; });
        return res;
    }

    Vertex const & getVertex(VId vid) const { return vertices[vid.id]; }

    PTRef getStateVersion(VId vid) const { return predicates.getStateRepresentation(getVertex(vid).predicateSymbol); }

    PTRef getNextStateVersion(VId vid) const { return predicates.getNextStateRepresentation(getVertex(vid).predicateSymbol); }

    VId getEntryId() const { return entry; }

    VId getExitId() const { return exit; }

    DirectedEdge getEdge(EId eid) const {
        assert(eid.id < edges.size());
        return edges[eid.id];
    }

    PTRef getEdgeLabel(EId eid) const {
        return getEdge(eid).fla.fla;
    }

    VId getSource(EId eid) const {
        return getEdge(eid).from;
    }

	VId getTarget(EId eid) const {
		return getEdge(eid).to;
	}

    std::unique_ptr<ChcDirectedHyperGraph> toHyperGraph() const;
};


class ChcDirectedHyperGraph {
    VId entry;
    VId exit;

    std::vector<Vertex> vertices;
    std::vector<DirectedHyperEdge> edges;
    CanonicalPredicateRepresentation predicates;

public:
    ChcDirectedHyperGraph(std::vector<Vertex> vertices, std::vector<DirectedHyperEdge> edges,
                          CanonicalPredicateRepresentation predicates, VId entry, VId exit) :
        vertices(std::move(vertices)), edges(std::move(edges)), predicates(std::move(predicates)), entry(entry), exit(exit)
    {}

    bool isNormalGraph() const;
    std::unique_ptr<ChcDirectedGraph> toNormalGraph() const;

    std::vector<Vertex> getVertexCopies() const { return vertices; }

    std::vector<DirectedHyperEdge> getEdgeCopies() const { return edges; }

    std::vector<VId> getVertices() const {
        std::vector<VId> res;
        std::size_t counter = 0;
        std::generate_n(std::back_inserter(res), vertices.size(), [&counter]() { return VId{counter++}; });
        return res;
    }

    std::vector<EId> getEdges() const {
        std::vector<EId> res;
        std::size_t counter = 0;
        std::generate_n(std::back_inserter(res), edges.size(), [&counter]() { return EId{counter++}; });
        return res;
    }
    Vertex const & getVertex(VId vid) const { return vertices[vid.id]; }

    PTRef getStateVersion(VId vid) const { return predicates.getStateRepresentation(getVertex(vid).predicateSymbol); }

    PTRef getNextStateVersion(VId vid) const { return predicates.getNextStateRepresentation(getVertex(vid).predicateSymbol); }

    VId getEntryId() const { return entry; }

    VId getExitId() const { return exit; }

    DirectedHyperEdge getEdge(EId eid) const {
        assert(eid.id < edges.size());
        return edges[eid.id];
    }

    PTRef getEdgeLabel(EId eid) const {
        return getEdge(eid).fla.fla;
    }

    std::vector<VId> getSources(EId eid) const {
        return getEdge(eid).from;
    }

    VId getTarget(EId eid) const {
        return getEdge(eid).to;
    }
};

class ChcGraphBuilder {
    Logic& logic;
public:
    ChcGraphBuilder(Logic& logic) : logic(logic) {}

    std::unique_ptr<ChcDirectedHyperGraph> buildGraph(NormalizedChcSystem const & system);
};

class ChcGraphContext {
    ChcDirectedGraph & graph;
    Logic & logic;
public:
    ChcGraphContext(ChcDirectedGraph & graph, Logic & logic) : graph(graph), logic(logic) {}
    ChcDirectedGraph & getGraph() { return graph; }
    Logic & getLogic() { return logic; }
};

#endif //OPENSMT_CHCGRAPH_H
