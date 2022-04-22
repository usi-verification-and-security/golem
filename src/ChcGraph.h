//
// Created by Martin Blicha on 17.07.20.
//

#ifndef OPENSMT_CHCGRAPH_H
#define OPENSMT_CHCGRAPH_H

#include "ChcSystem.h"
#include "TermUtils.h"
#include "Normalizer.h"

#include <iosfwd>
#include <map>
#include <memory>
#include <optional>

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
    std::vector<SymRef> from;
    SymRef to;
    InterpretedFla fla;
    EId id;
};

struct DirectedEdge {
    SymRef from;
    SymRef to;
    InterpretedFla fla;
    EId id;
};

class ChcDirectedGraph;
class ChcDirectedHyperGraph;

class AdjacencyListsGraphRepresentation {
    using AdjacencyList = std::unordered_map<SymRef, std::vector<EId>, SymRefHash>;
    AdjacencyList incomingEdges;
    AdjacencyList outgoingEdges;

	AdjacencyListsGraphRepresentation(AdjacencyList && incoming, AdjacencyList && outgoing)
		: incomingEdges(std::move(incoming)),
		  outgoingEdges(std::move(outgoing))
	{}

public:
    static AdjacencyListsGraphRepresentation from(ChcDirectedGraph const& graph);
    static AdjacencyListsGraphRepresentation from(ChcDirectedHyperGraph const& graph);
    std::vector<EId> const & getIncomingEdgesFor(SymRef sym) const {
        assert(incomingEdges.count(sym) > 0);
        return incomingEdges.at(sym);
    }
    std::vector<EId> const & getOutgoingEdgesFor(SymRef sym) const {
        assert(outgoingEdges.count(sym) > 0);
        return outgoingEdges.at(sym);
    }

    std::size_t getVertexNum() const { return incomingEdges.size(); }
};

class ChcDirectedHyperGraph;

// Helper structure for lookup of edges given its vertices
struct EdgeHasher {
    std::size_t operator()(std::pair<SymRef, SymRef> pair) const {
        // From Boost hash_combine
        std::hash<std::size_t> hasher;
        std::size_t res = 0;
        res ^= hasher(pair.first.x) + 0x9e3779b9 + (res<<6) + (res>>2);
        res ^= hasher(pair.second.x) + 0x9e3779b9 + (res<<6) + (res>>2);
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
    std::map<EId, DirectedEdge> edges;
    LinearCanonicalPredicateRepresentation predicates;
    Logic & logic;
    mutable std::size_t freeId {0};

    // graph transformations
    friend class GraphTransformations;
    void contractVertex(SymRef sym);
    void mergeEdges(EId incoming, EId outgoing);
    void deleteNode(SymRef sym);
    PTRef mergeLabels(DirectedEdge const & incoming, DirectedEdge const & outgoing);
    void mergeMultiEdges();

public:
    ChcDirectedGraph(std::vector<DirectedEdge> edges, LinearCanonicalPredicateRepresentation predicates,
                     Logic & logic) :
         predicates(std::move(predicates)), logic(logic) {
        for (auto & edge : edges) {
            EId eid = freshId();
            edge.id = eid;
            this->edges.emplace(eid, edge);
        }
    }

    std::vector<SymRef> getVertices() const;

    Logic & getLogic() { return logic; }
    Logic const & getLogic() const { return logic; }
    void toDot(std::ostream& out) const;
    ChcDirectedGraph reverse() const;
    DirectedEdge reverseEdge(DirectedEdge const & edge, TermUtils & utils) const;

    LinearCanonicalPredicateRepresentation getPredicateRepresentation() const { return predicates; }

    SymRef getEntry() const { return logic.getSym_true(); }
    SymRef getExit() const { return logic.getSym_false(); }

    PTRef getStateVersion(SymRef sym) const { return predicates.getSourceTermFor(sym); }

    PTRef getNextStateVersion(SymRef sym) const { return predicates.getTargetTermFor(sym); }

    PTRef getEdgeLabel(EId eid) const {
        return getEdge(eid).fla.fla;
    }

    SymRef getSource(EId eid) const {
        return getEdge(eid).from;
    }

	SymRef getTarget(EId eid) const {
		return getEdge(eid).to;
	}

    std::unique_ptr<ChcDirectedHyperGraph> toHyperGraph() const;

    template<typename TAction>
    void forEachEdge(TAction action) const {
        for (auto const & edge : edges) {
            action(edge.second);
        }
    }

private:
    DirectedEdge const & getEdge(EId eid) const {
        return edges.at(eid);
    }

    template<typename TPred>
    void deleteMatchingEdges(TPred predicate) {
        for (auto it = edges.cbegin(); it != edges.cend(); /* no increment */) {
            if (predicate(it->second)) {
                it = edges.erase(it);
            } else {
                ++it;
            }
        }
    }

    EId freshId() const { return EId{freeId++};}

    void newEdge(SymRef from, SymRef to, InterpretedFla label) {
        EId eid = freshId();
        edges.emplace(eid, DirectedEdge{.from = from, .to = to, .fla = label, .id = eid});
    }

};


class ChcDirectedHyperGraph {
    std::map<EId, DirectedHyperEdge> edges;
    NonlinearCanonicalPredicateRepresentation predicates;
    Logic & logic;
    mutable std::size_t freeId {0};

    EId freshId() const { return EId{freeId++}; }

public:
    ChcDirectedHyperGraph(std::vector<DirectedHyperEdge> edges,
                          NonlinearCanonicalPredicateRepresentation predicates,
                          Logic & logic) :
        predicates(std::move(predicates)), logic(logic)
    {
        for (auto & edge : edges) {
            EId eid = freshId();
            edge.id = eid;
            this->edges.emplace(eid, edge);
        }
    }

    std::vector<SymRef> getVertices() const;
    Logic & getLogic() { return logic; }
    Logic const & getLogic() const { return logic; }
    bool isNormalGraph() const;
    std::unique_ptr<ChcDirectedGraph> toNormalGraph() const;

    SymRef getEntry() const { return logic.getSym_true(); }
    SymRef getExit() const { return logic.getSym_false(); }

    PTRef getStateVersion(SymRef sym, unsigned instance = 0) const { return predicates.getSourceTermFor(sym, instance); }

    PTRef getNextStateVersion(SymRef sym) const { return predicates.getTargetTermFor(sym); }

    DirectedHyperEdge const & getEdge(EId eid) const {
        return edges.at(eid);
    }

    PTRef getEdgeLabel(EId eid) const {
        return getEdge(eid).fla.fla;
    }

    std::vector<SymRef> const & getSources(EId eid) const {
        return getEdge(eid).from;
    }

    SymRef getTarget(EId eid) const {
        return getEdge(eid).to;
    }
    DirectedHyperEdge contractTrivialChain(std::vector<EId> const & trivialChain);

    template<typename TAction>
    void forEachEdge(TAction action) const {
        for (auto const & entry : edges) {
            action(entry.second);
        }
    }
private:
    EId newEdge(std::vector<SymRef> && from, SymRef to, InterpretedFla label) {
        EId eid = freshId();
        edges.emplace(eid, DirectedHyperEdge{.from = std::move(from), .to = to, .fla = label, .id = eid});
        return eid;
    }

    template<typename TPred>
    void deleteMatchingEdges(TPred predicate) {
        for (auto it = edges.cbegin(); it != edges.cend(); /* no increment */) {
            if (predicate(it->second)) {
                it = edges.erase(it);
            } else {
                ++it;
            }
        }
    }

    void deleteNode(SymRef sym);
    DirectedHyperEdge mergeEdges(std::vector<EId> const & chain);
    PTRef mergeLabels(std::vector<EId> const & chain);
};

class ChcGraphBuilder {
    Logic& logic;
public:
    ChcGraphBuilder(Logic& logic) : logic(logic) {}

    std::unique_ptr<ChcDirectedHyperGraph> buildGraph(NormalizedChcSystem const & system);
};

std::optional<EId> getSelfLoopFor(SymRef, ChcDirectedGraph const & graph, AdjacencyListsGraphRepresentation const & adjacencyRepresentation);

std::vector<SymRef> reversePostOrder(ChcDirectedGraph const & graph, AdjacencyListsGraphRepresentation const & adjacencyRepresentation);
std::vector<SymRef> postOrder(ChcDirectedGraph const & graph, AdjacencyListsGraphRepresentation const & adjacencyRepresentation);

#endif //OPENSMT_CHCGRAPH_H
