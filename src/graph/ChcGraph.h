/*
 * Copyright (c) 2020-2023, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef GOLEM_CHCGRAPH_H
#define GOLEM_CHCGRAPH_H

#include "ChcSystem.h"
#include "TermUtils.h"

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
    using Node = SymRef;
    using NodeHash = SymRefHash;
    using AdjacencyList = std::unordered_map<Node, std::vector<EId>, NodeHash>;
    AdjacencyList incomingEdges;
    AdjacencyList outgoingEdges;


	AdjacencyListsGraphRepresentation(AdjacencyList && incoming, AdjacencyList && outgoing)
		: incomingEdges(std::move(incoming)),
		  outgoingEdges(std::move(outgoing))
	{}

public:
    static AdjacencyListsGraphRepresentation from(ChcDirectedGraph const& graph);
    static AdjacencyListsGraphRepresentation from(ChcDirectedHyperGraph const& graph);
    [[nodiscard]] std::vector<EId> const & getIncomingEdgesFor(SymRef sym) const {
        assert(incomingEdges.count(sym) > 0);
        return incomingEdges.at(sym);
    }
    [[nodiscard]] std::vector<EId> const & getOutgoingEdgesFor(SymRef sym) const {
        assert(outgoingEdges.count(sym) > 0);
        return outgoingEdges.at(sym);
    }

    [[nodiscard]] std::size_t getVertexNum() const { return incomingEdges.size(); }

    [[nodiscard]] std::vector<Node> getNodes() const {
        std::vector<Node> res;
        res.reserve(incomingEdges.size());
        for (auto const & entry : incomingEdges) {
            res.push_back(entry.first);
        }
        return res;
    }
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

struct VarPosition {
    SymRef vertex;
    uint32_t pos;

    inline bool operator==(VarPosition other) const { return vertex == other.vertex and pos == other.pos; }
};
struct VarPositionHasher {
    std::size_t operator()(VarPosition pos) const {
        std::hash<std::uint32_t> hasher;
        return hasher(pos.vertex.x) ^ hasher(pos.pos);
    }
};

using LocationVarMap = std::unordered_map<SymRef, PTRef, SymRefHash>;
using PositionVarMap = std::unordered_map<VarPosition, PTRef, VarPositionHasher>;

struct WitnessInfo {
    SymRef loopVertex;
    LocationVarMap locations;
    PositionVarMap positions;
};

class ChcDirectedGraph {
    std::map<EId, DirectedEdge> edges;
    LinearCanonicalPredicateRepresentation predicates;
    Logic & logic;
    mutable std::size_t freeId {0};

    // graph transformations
    friend class NestedLoopTransformation;
    friend class SingleLoopTransformation;
    WitnessInfo contractConnectedVertices(std::vector<EId> edges);

public:
    ChcDirectedGraph(std::vector<DirectedEdge> const & edges, LinearCanonicalPredicateRepresentation predicates,
                     Logic & logic) :
         predicates(std::move(predicates)), logic(logic) {
        std::size_t maxId = 0;
        for (auto & edge : edges) {
            maxId = std::max(maxId, edge.id.id);
            this->edges.emplace(edge.id, edge);
        }
        this->freeId = maxId + 1;
    }

    std::vector<SymRef> getVertices() const;
    std::vector<EId> getEdges() const;

    Logic & getLogic() const { return logic; }
    void toDot(std::ostream& out, bool full = false) const;
    ChcDirectedGraph reverse() const;
    DirectedEdge reverseEdge(DirectedEdge const & edge, TermUtils const & utils) const;

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

    void updateEdgeLabel(EId edge, InterpretedFla label) {
        edges[edge].fla  = label;
    }

    void updateEdgeSource(EId edge, SymRef source) {
        edges[edge].from  = source;
    }

    void updateEdgeTarget(EId edge, SymRef target) {
        edges[edge].to  = target;
    }

    void removeEdge(EId edge){
        const auto it = edges.find(edge);
        if (it != edges.end())
            edges.erase(it);
    }

};


class ChcDirectedHyperGraph {
    std::map<EId, DirectedHyperEdge> edges;
    NonlinearCanonicalPredicateRepresentation predicates;
    Logic & logic;
    mutable std::size_t freeId {0};

    EId freshId() const { return EId{freeId++}; }

public:
    class VertexInstances {
        std::map<EId, std::vector<unsigned>> instanceCounter;
    public:
        explicit VertexInstances(ChcDirectedHyperGraph const & graph);

        [[nodiscard]] unsigned getInstanceNumber(EId eid, unsigned sourceIndex) const {
            return instanceCounter.at(eid)[sourceIndex];
        }
    };

    static std::unique_ptr<ChcDirectedHyperGraph> makeEmpty(Logic & logic);

    struct VertexContractionResult {
        std::vector<DirectedHyperEdge> incoming;
        std::vector<DirectedHyperEdge> outgoing;
        std::vector<std::pair<DirectedHyperEdge, std::pair<std::size_t, std::size_t>>> replacing;
    };

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
    std::vector<DirectedHyperEdge> getEdges() const;
    Logic & getLogic() const { return logic; }
    NonlinearCanonicalPredicateRepresentation const & predicateRepresentation() const { return predicates; }
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
    VertexContractionResult contractVertex(SymRef sym);

    using MergedEdges = std::vector<std::pair<std::vector<DirectedHyperEdge>, DirectedHyperEdge>>;
    MergedEdges mergeMultiEdges();

    template<typename TAction>
    void forEachEdge(TAction action) const {
        for (auto const & entry : edges) {
            action(entry.second);
        }
    }

    template<typename TAction>
    void forEachEdge(TAction action) {
        for (auto & entry : edges) {
            action(entry.second);
        }
    }

    void deleteFalseEdges();
    void deleteEdges(std::vector<EId> const & edgesToDelete);
    void deleteNode(SymRef sym);

    bool isHyperEdge(EId eid) const { return getSources(eid).size() > 1; }
    bool isSimpleLoopEdge(EId eid) const {
        assert(not isHyperEdge(eid));
        auto const & edge = getEdge(eid);
        return edge.from.front() == edge.to;
    }

private:
    PTRef createAuxiliaryVariable(SRef ref) const {
        static long long counter = 0;
        std::string name = "aux#g#" + std::to_string(counter++);
        return TimeMachine(logic).getVarVersionZero(name, ref);
    }

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

    DirectedHyperEdge mergeEdgePair(EId first, EId second);

    /** Merges a chaing of simple non-looping edges into a single edge */
    DirectedHyperEdge mergeTrivialChain(std::vector<EId> const & chain);

    /** Computes a merged label of a chain of simple non-looping edges */
    PTRef mergeTrivialChainLabels(std::vector<EId> const & chain) const;
};

std::optional<EId> getSelfLoopFor(SymRef, ChcDirectedGraph const & graph, AdjacencyListsGraphRepresentation const & adjacencyRepresentation);

std::vector<SymRef> reversePostOrder(ChcDirectedGraph const & graph, AdjacencyListsGraphRepresentation const & adjacencyRepresentation);
std::vector<SymRef> postOrder(ChcDirectedGraph const & graph, AdjacencyListsGraphRepresentation const & adjacencyRepresentation);

class ReverseDFS {
    ChcDirectedHyperGraph const & graph;
    AdjacencyListsGraphRepresentation const & adjacencyRepresentation;
    std::unordered_set<SymRef, SymRefHash> marked;

    [[nodiscard]] bool isMarked(SymRef sym) const { return marked.find(sym) != marked.end(); }
    void mark(SymRef sym) { marked.insert(sym); }

    template<typename TPreorderAction, typename TPostorderAction>
    void runOnVertex(SymRef sym, TPreorderAction const & preorder, TPostorderAction const & postorder) {
        if (isMarked(sym)) { return; }
        mark(sym);
        preorder(sym);
        for (EId inEdge : adjacencyRepresentation.getIncomingEdgesFor(sym)) {
            auto const & sources = graph.getSources(inEdge);
            for (auto source : sources) {
                runOnVertex(source, preorder, postorder);
            }
        }
        postorder(sym);
    }
public:
    ReverseDFS(ChcDirectedHyperGraph const & graph, AdjacencyListsGraphRepresentation const & adjacencyRepresentation) :
        graph(graph),
        adjacencyRepresentation(adjacencyRepresentation)
    {}

    template<typename TPreorderAction, typename TPostorderAction>
    void run(TPreorderAction const & preorder, TPostorderAction const & postorder) && {
        runOnVertex(graph.getExit(), preorder, postorder);
    }
};

bool isNonLoopNode(SymRef, AdjacencyListsGraphRepresentation const &, ChcDirectedHyperGraph const & graph);

bool hasHyperEdge(SymRef, AdjacencyListsGraphRepresentation const &, ChcDirectedHyperGraph const & graph);

bool isSimpleNode(SymRef, AdjacencyListsGraphRepresentation const &);

#endif //GOLEM_CHCGRAPH_H
