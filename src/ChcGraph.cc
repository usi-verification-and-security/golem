//
// Created by Martin Blicha on 17.07.20.
//

#include "ChcGraph.h"

#include <iostream>
#include <map>

std::unique_ptr<ChcDirectedHyperGraph> ChcGraphBuilder::buildGraph(NormalizedChcSystem const & system) {
    std::vector<DirectedHyperEdge> edges;

    ChcSystem const & chcSystem = *system.normalizedSystem;
    // Special case to cover initial clauses, we are adding artificial "TRUE" starting predicate
    SymRef init = logic.getSym_true();
    for (auto const & clause : chcSystem.getClauses()) {
        auto const& head = clause.head;
        auto const& body = clause.body;
        auto headSymbol = logic.getSymRef(head.predicate.predicate);

        std::vector<SymRef> from;
        for (auto const& bodyPredicate : body.uninterpretedPart) {
            from.push_back(logic.getSymRef(bodyPredicate.predicate));
        }
        if (from.empty()) {
            from.push_back(init);
        }
        edges.push_back(DirectedHyperEdge{.from = std::move(from), .to = headSymbol, .fla = body.interpretedPart, .id = {0}});
    }
    return std::make_unique<ChcDirectedHyperGraph>(std::move(edges), system.canonicalPredicateRepresentation, logic);
}

bool ChcDirectedHyperGraph::isNormalGraph() const {
    return std::all_of(edges.begin(), edges.end(), [](auto const & entry) {
        auto const & sources = entry.second.from;
        assert(not sources.empty());
        return sources.size() == 1;
    });
}

std::unique_ptr<ChcDirectedGraph> ChcDirectedHyperGraph::toNormalGraph() const {
    TimeMachine timeMachine(logic);
    VersionManager manager(logic);
    TermUtils utils(logic);
    LinearCanonicalPredicateRepresentation newPredicates(logic);
    for (SymRef sym : getVertices()) {
        std::vector<PTRef> vars;
        PTRef originalTerm = predicates.getSourceTermFor(sym);
        for (PTRef var : logic.getPterm(originalTerm)) {
            assert(logic.isVar(var));
            vars.push_back(var);
        }
        std::transform(vars.begin(), vars.end(), vars.begin(), [&](PTRef var){
            return manager.toBase(var);
        });
        newPredicates.addRepresentation(sym, std::move(vars));
    }

    std::vector<DirectedEdge> normalEdges;
    forEachEdge([&](DirectedHyperEdge const& edge) {
        assert(edge.from.size() == 1);
        auto source = edge.from[0];
        auto target = edge.to;
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
        normalEdges.emplace_back(DirectedEdge{.from = edge.from[0], .to = edge.to, .fla = {newLabel}, .id = {0}});
    });
    return std::make_unique<ChcDirectedGraph>(std::move(normalEdges), std::move(newPredicates), logic);
}

void ChcDirectedGraph::toDot(std::ostream & out) const {

    out << "digraph proof {" << '\n';

    std::unordered_map<SymRef, std::string, SymRefHash> dotIds;

    for (SymRef sym : getVertices()) {
        auto pred = this->getStateVersion(sym);
        dotIds.insert(std::make_pair(sym, "n" + std::to_string(sym.x)));
        std::string label = logic.printTerm(pred);
        out << dotIds[sym] << "\t[label =  \"" << label << "\"];\n";
    }

    forEachEdge([&](auto const & edge) {
        out << dotIds[edge.from] << " -> " << dotIds[edge.to] << " [label = \"" << logic.printTerm(edge.fla.fla) << "\"];\n";
    });

    out << "}" << std::endl;
}

DirectedEdge ChcDirectedGraph::reverseEdge(DirectedEdge const & edge, TermUtils & utils) const {
    auto rfrom = edge.to;
    auto rto = edge.from;
    PTRef ofla = edge.fla.fla;
    std::unordered_map<PTRef, PTRef, PTRefHash> subst;
    // variables from 'from' are expressed as state vars, they must be changed to next state
    utils.insertVarPairsFromPredicates(this->getStateVersion(edge.from), this->getNextStateVersion(edge.from), subst);
    // variables from 'to' are expressed as next state vars, they must be changed to state
    utils.insertVarPairsFromPredicates(this->getNextStateVersion(edge.to), this->getStateVersion(edge.to), subst);
    // simulataneous substitution
    PTRef rfla = utils.varSubstitute(ofla, subst);
    return DirectedEdge{.from = rfrom, .to = rto, .fla = InterpretedFla{rfla}, .id = edge.id};
}

ChcDirectedGraph ChcDirectedGraph::reverse() const {
    // same vertices, same canonical representation, switch entry and exit and reverse edges
    // NOTE: reversing edge means flipping state and next state variables
    TermUtils utils(logic);
    std::vector<DirectedEdge> redges;
    auto swapTrueFalse = [&](SymRef sym) {
        return sym == logic.getSym_false() ? logic.getSym_true()
            : sym == logic.getSym_true() ? logic.getSym_false() : sym;
    };
    forEachEdge([&](auto const & edge) {
        auto reversed = reverseEdge(edge, utils);
        swapTrueFalse(reversed.from);
        swapTrueFalse(reversed.to);
        redges.push_back(reversed);
    });
    return ChcDirectedGraph(std::move(redges), this->predicates, logic);
}

void ChcDirectedGraph::contractVertex(SymRef sym) {
    auto adjacencyList = AdjacencyListsGraphRepresentation::from(*this);
    auto const & incomingEdges = adjacencyList.getIncomingEdgesFor(sym);
    auto const & outgoingEdges = adjacencyList.getOutgoingEdgesFor(sym);
    for (EId incomingId : incomingEdges) {
        assert(getEdge(incomingId).to != getEdge(incomingId).from);
        for (EId outgoingId : outgoingEdges) {
            assert(getEdge(outgoingId).to != getEdge(outgoingId).from);
            mergeEdges(incomingId, outgoingId);
        }
    }
    deleteNode(sym);
}

PTRef ChcDirectedGraph::mergeLabels(const DirectedEdge & incoming, const DirectedEdge & outgoing) {
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

void ChcDirectedGraph::mergeEdges(EId incomingId, EId outgoingId) {
    auto const & incoming = getEdge(incomingId);
    auto const & outgoing = getEdge(outgoingId);
    if (incoming.to != outgoing.from) { throw std::logic_error("ChcDirectedGraph::mergeEdges: Trying to merge edges without common node!\n"); }

    auto source = incoming.from;
    auto target = outgoing.to;
    PTRef mergedLabel = mergeLabels(incoming, outgoing);
    newEdge(source, target, InterpretedFla{mergedLabel});
}

void ChcDirectedGraph::mergeMultiEdges() {
    std::unordered_map<std::pair<SymRef, SymRef>, std::vector<EId>, EdgeHasher> buckets;
    std::vector<EId> edgesToRemove;
    forEachEdge([&](auto const & edge) {
        auto pair = std::make_pair(edge.from, edge.to);
        buckets[pair].push_back(edge.id);
    });
    for (auto const & bucketEntry : buckets) {
        auto const & bucket = bucketEntry.second;
        if (bucket.size() < 2) { continue; }
        vec<PTRef> labels;
        labels.capacity(bucket.size());
        for (auto index : bucket) {
            labels.push(edges[index].fla.fla);
        }
        edges[bucket[0]].fla = InterpretedFla{logic.mkOr(std::move(labels))};
        std::for_each(bucket.begin() + 1, bucket.end(), [&edgesToRemove](EId eid) { edgesToRemove.push_back(eid); });
    }
    std::for_each(edgesToRemove.cbegin(), edgesToRemove.cend(), [this](EId eid) { edges.erase(eid); });
}

void ChcDirectedGraph::deleteNode(SymRef sym) {
    deleteMatchingEdges([sym](DirectedEdge const & edge) {
        return edge.from == sym or edge.to == sym;
    });
}

AdjacencyListsGraphRepresentation AdjacencyListsGraphRepresentation::from(const ChcDirectedGraph & graph) {
    AdjacencyList incoming;
    AdjacencyList outgoing;
    graph.forEachEdge([&](DirectedEdge const & edge) {
        incoming[edge.to].push_back(edge.id);
        outgoing[edge.from].push_back(edge.id);
        // TODO: figure out a better way to ensure that all vertices are present in both lists
        incoming[edge.from];
        outgoing[edge.to];
    });
    return AdjacencyListsGraphRepresentation(std::move(incoming), std::move(outgoing));
}

AdjacencyListsGraphRepresentation AdjacencyListsGraphRepresentation::from(const ChcDirectedHyperGraph & graph) {
    AdjacencyList incoming;
    AdjacencyList outgoing;
    graph.forEachEdge([&](DirectedHyperEdge const & edge) {
        // TODO: figure out a better way to ensure that all vertices are present in both lists
        incoming[edge.to].push_back(edge.id);
        for (SymRef sym : edge.from) {
            incoming[sym];
            outgoing[sym].push_back(edge.id);
        }
        outgoing[edge.to];
    });
    return AdjacencyListsGraphRepresentation(std::move(incoming), std::move(outgoing));
}

std::unique_ptr<ChcDirectedHyperGraph> ChcDirectedGraph::toHyperGraph() const {
    TimeMachine timeMachine(logic);
    VersionManager manager(logic);
    TermUtils utils(logic);
    NonlinearCanonicalPredicateRepresentation newPredicates(logic);
    for (SymRef sym : getVertices()) {
        PTRef originalTerm = predicates.getSourceTermFor(sym);
        std::vector<PTRef> vars = utils.getVarsFromPredicateInOrder(originalTerm);
        std::transform(vars.begin(), vars.end(), vars.begin(), [&](PTRef var){
            return timeMachine.getUnversioned(var);
        });
        newPredicates.addRepresentation(sym, std::move(vars));
    }

    std::vector<DirectedHyperEdge> newEdges;
    forEachEdge([&](DirectedEdge const & edge) {
        auto source = edge.from;
        auto target = edge.to;
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
        newEdges.push_back(DirectedHyperEdge{.from = {edge.from}, .to = edge.to, .fla = {newLabel}, .id = {0}});
    });
    return std::make_unique<ChcDirectedHyperGraph>(std::move(newEdges), std::move(newPredicates), logic);
}

std::optional<EId> getSelfLoopFor(SymRef sym, ChcDirectedGraph const & graph, AdjacencyListsGraphRepresentation const & adjacencyRepresentation) {
    auto const & outEdges = adjacencyRepresentation.getOutgoingEdgesFor(sym);
    auto it = std::find_if(outEdges.begin(), outEdges.end(), [&](EId eid) {
        return graph.getTarget(eid) == sym;
    });
    return it != outEdges.end() ? *it : std::optional<EId>{};
}

class DFS {
    ChcDirectedGraph const & graph;
    AdjacencyListsGraphRepresentation const & adjacencyRepresentation;
    std::unordered_set<SymRef, SymRefHash> marked;

    bool isMarked(SymRef sym) const { return marked.find(sym) != marked.end(); }
    void mark(SymRef sym) { marked.insert(sym); }

    template<typename TPreorderAction, typename TPostorderAction>
    void runOnVertex(SymRef sym, TPreorderAction const & preorder, TPostorderAction const & postorder) {
        if (isMarked(sym)) { return; }
        mark(sym);
        preorder(sym);
        for (EId outEdge : adjacencyRepresentation.getOutgoingEdgesFor(sym)) {
            runOnVertex(graph.getTarget(outEdge), preorder, postorder);
        }
        postorder(sym);
    }
public:
    DFS(ChcDirectedGraph const & graph, AdjacencyListsGraphRepresentation const & adjacencyRepresentation) :
        graph(graph),
        adjacencyRepresentation(adjacencyRepresentation)
    {}

    template<typename TPreorderAction, typename TPostorderAction>
    void run(TPreorderAction const & preorder, TPostorderAction const & postorder) && {
            runOnVertex(graph.getEntry(), preorder, postorder);
    }
};

std::vector<SymRef> reversePostOrder(ChcDirectedGraph const & graph, AdjacencyListsGraphRepresentation const & adjacencyRepresentation) {
    std::vector<SymRef> order = postOrder(graph, adjacencyRepresentation);
    std::reverse(order.begin(), order.end());
    return order;
}

std::vector<SymRef> postOrder(ChcDirectedGraph const & graph, AdjacencyListsGraphRepresentation const & adjacencyRepresentation) {
    std::vector<SymRef> order;
    DFS(graph, adjacencyRepresentation).run([](SymRef){}, [&order](SymRef v){ order.push_back(v); });
    return order;
}

DirectedHyperEdge ChcDirectedHyperGraph::contractTrivialChain(std::vector<EId> const & trivialChain) {
    assert(trivialChain.size() >= 2);
    auto summaryEdge = mergeEdges(trivialChain);
    std::vector<SymRef> vertices;
    for (EId eid : trivialChain) {
        vertices.push_back(getTarget(eid));
    }
    vertices.pop_back(); // We want to keep the last one
    for (auto vertex : vertices) {
        deleteNode(vertex);
    }
    return summaryEdge;
}

void ChcDirectedHyperGraph::deleteNode(SymRef sym) {
    deleteMatchingEdges([sym](auto const & edge) {
        return edge.to == sym or std::find(edge.from.begin(), edge.from.end(), sym) != edge.from.end();
    });
}

DirectedHyperEdge ChcDirectedHyperGraph::mergeEdges(std::vector<EId> const & chain) {
    auto source = getSources(chain.front()).front();
    auto target = getTarget(chain.back());
    PTRef mergedLabel = mergeLabels(chain);
    auto eid = newEdge({source}, target, InterpretedFla{mergedLabel});
    return getEdge(eid);
}

PTRef ChcDirectedHyperGraph::mergeLabels(std::vector<EId> const & chain) {
    // MB: We can rely on the fact that every predicate has unique variables in its canonical representation
    // This is guaranteed by Normalizer
    assert(chain.size() >= 2);
    auto source = getSources(chain.front()).front();
    auto target = getTarget(chain.back());
    vec<PTRef> labels;
    TermUtils utils(logic);
    TermUtils::substitutions_map subMap;
    for (auto incomingIt = chain.begin(), outgoingIt = chain.begin() + 1; outgoingIt != chain.end(); ++incomingIt, ++outgoingIt) {
        EId incoming = *incomingIt;
        EId outgoing = *outgoingIt;
        auto common = getTarget(incoming);
        assert(getSources(outgoing).size() == 1 and getSources(outgoing).front() == common);
        // MB: Simply casting the target variables to current state from next state is only possible because this is trivial chain
        utils.insertVarPairsFromPredicates(getNextStateVersion(common), getStateVersion(common), subMap);
        labels.push(getEdgeLabel(incoming));
    }
    PTRef combinedLabel = logic.mkAnd(std::move(labels));
    PTRef updatedLabel = utils.varSubstitute(combinedLabel, subMap);
//    std::cout << logic.pp(updatedLabel) << '\n';
    PTRef simplifiedLabel = TrivialQuantifierElimination(logic).tryEliminateVarsExcept(utils.getVarsFromPredicateInOrder(
        getStateVersion(source)) + utils.getVarsFromPredicateInOrder(getNextStateVersion(target)), updatedLabel);
//    std::cout << logic.pp(simplifiedLabel) << '\n';
    return simplifiedLabel;
}

std::vector<SymRef> ChcDirectedGraph::getVertices() const {
    std::unordered_set<SymRef, SymRefHash> vertices;
    forEachEdge([&](DirectedEdge const & edge){
        vertices.insert(edge.to);
    });
    vertices.insert(getEntry());
    return std::vector<SymRef>(vertices.begin(), vertices.end());
}

std::vector<SymRef> ChcDirectedHyperGraph::getVertices() const {
    std::unordered_set<SymRef, SymRefHash> vertices;
    forEachEdge([&](DirectedHyperEdge const & edge){
        vertices.insert(edge.to);
    });
    vertices.insert(getEntry());
    return std::vector<SymRef>(vertices.begin(), vertices.end());
}