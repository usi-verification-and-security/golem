/*
 * Copyright (c) 2020-2023, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "ChcGraph.h"

#include <iostream>
#include <map>


namespace{

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
}

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
            auto sourceVars = utils.predicateArgsInOrder(getStateVersion(source));
            for (PTRef sourceVar : sourceVars) {
                PTRef newVar = timeMachine.getVarVersionZero(manager.toBase(sourceVar));
                subst.insert({sourceVar, newVar});
            }
        }
        {
            auto targetVars = utils.predicateArgsInOrder(getNextStateVersion(target));
            for (PTRef targetVar : targetVars) {
                PTRef newVar = timeMachine.sendVarThroughTime(timeMachine.getVarVersionZero(manager.toBase(targetVar)), 1);
                subst.insert({targetVar, newVar});
            }
        }

        PTRef newLabel = TermUtils(logic).varSubstitute(edge.fla.fla, subst);
        normalEdges.emplace_back(DirectedEdge{.from = edge.from[0], .to = edge.to, .fla = {newLabel}, .id = edge.id});
    });
    return std::make_unique<ChcDirectedGraph>(std::move(normalEdges), std::move(newPredicates), logic);
}

void ChcDirectedGraph::toDot(std::ostream & out, bool full) const {

    out << "digraph proof {" << '\n';

    std::unordered_map<SymRef, std::string, SymRefHash> dotIds;

    for (SymRef sym : getVertices()) {
        auto pred = this->getStateVersion(sym);
        dotIds.insert(std::make_pair(sym, "n" + std::to_string(sym.x)));
        std::string label = full ? logic.printTerm(pred) : logic.printSym(sym);
        out << dotIds[sym] << "\t[label =  \"" << label << "\"];\n";
    }

    forEachEdge([&](auto const & edge) {
        out << dotIds[edge.from] << " -> " << dotIds[edge.to] << " [label = \"" << (full ? logic.printTerm(edge.fla.fla) : "") << "\"];\n";
    });

    out << "}" << std::endl;
}

DirectedEdge ChcDirectedGraph::reverseEdge(DirectedEdge const & edge, TermUtils & utils) const {
    auto rfrom = edge.to;
    auto rto = edge.from;
    PTRef ofla = edge.fla.fla;
    std::unordered_map<PTRef, PTRef, PTRefHash> subst;
    // variables from 'from' are expressed as state vars, they must be changed to next state
    utils.mapFromPredicate(this->getStateVersion(edge.from), this->getNextStateVersion(edge.from), subst);
    // variables from 'to' are expressed as next state vars, they must be changed to state
    utils.mapFromPredicate(this->getNextStateVersion(edge.to), this->getStateVersion(edge.to), subst);
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
    utils.mapFromPredicate(getNextStateVersion(incoming.to), getStateVersion(outgoing.from), subMap);
    PTRef updatedIncomingLabel = utils.varSubstitute(incomingLabel, subMap);
    PTRef combinedLabel = logic.mkAnd(updatedIncomingLabel, outgoingLabel);
//    std::cout << logic.pp(combinedLabel) << '\n';
    PTRef simplifiedLabel = TrivialQuantifierElimination(logic).tryEliminateVars(utils.predicateArgsInOrder(
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
        std::vector<PTRef> vars = utils.predicateArgsInOrder(originalTerm);
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
            auto sourceVars = utils.predicateArgsInOrder(getStateVersion(source));
            for (PTRef sourceVar : sourceVars) {
                assert(timeMachine.isVersioned(sourceVar));
                PTRef newVar = manager.toSource(timeMachine.getUnversioned(sourceVar));
                subst.insert({sourceVar, newVar});
            }
        }
        {
            auto targetVars = utils.predicateArgsInOrder(getNextStateVersion(target));
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

DirectedHyperEdge ChcDirectedHyperGraph::mergeEdgePair(EId incoming, EId outgoing) {
    assert(getSources(incoming).size() == 1); // Incoming must be a simple edge
    if (getSources(outgoing).size() == 1) { // Outgoing is a simple edge
        return mergeEdges({incoming, outgoing});
    }
    TermUtils utils(logic);
    auto common = getTarget(incoming);
    auto source = getSources(incoming)[0];
    auto target = getTarget(outgoing);
    // Special handling of outgoing hyperedge
    auto sources = getSources(outgoing);
    assert(std::count(sources.begin(), sources.end(), common) == 1);
    TermUtils::substitutions_map substitutionsMap;
    utils.mapFromPredicate(getNextStateVersion(common), getStateVersion(common, 0), substitutionsMap);
    PTRef renamedLabel = utils.varSubstitute(getEdgeLabel(incoming), substitutionsMap);

    PTRef newLabel = logic.mkAnd(renamedLabel, getEdgeLabel(outgoing));
    PTRef simplifiedLabel = TrivialQuantifierElimination(logic).tryEliminateVars(
        utils.predicateArgsInOrder(getStateVersion(common)), newLabel
    );

    for (auto & v : sources) {
        if (v == common) { v = source; }
    }
    if (source == getEntry()) {
        sources.erase(std::remove(sources.begin(), sources.end(), getEntry()), sources.end());
        if (sources.empty()) { sources.push_back(getEntry()); }
    }
    auto eid = newEdge(std::move(sources), target, InterpretedFla{simplifiedLabel});
    return getEdge(eid);

}

DirectedHyperEdge ChcDirectedHyperGraph::mergeEdges(std::vector<EId> const & chain) {
    assert(getSources(chain.front()).size() == 1);
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
    for (EId eid : chain) {
        labels.push(getEdgeLabel(eid));
    }
    for (auto incomingIt = chain.begin(), outgoingIt = chain.begin() + 1; outgoingIt != chain.end(); ++incomingIt, ++outgoingIt) {
        EId incoming = *incomingIt;
        EId outgoing = *outgoingIt; (void)outgoing;
        auto common = getTarget(incoming);
        assert(getSources(outgoing).size() == 1 and getSources(outgoing).front() == common);
        // MB: Simply casting the target variables to current state from next state is only possible because this is trivial chain
        utils.mapFromPredicate(getNextStateVersion(common), getStateVersion(common), subMap);
    }
    PTRef combinedLabel = logic.mkAnd(std::move(labels));
//    std::cout << "Original labels: " << logic.pp(combinedLabel) << '\n';
    PTRef updatedLabel = utils.varSubstitute(combinedLabel, subMap);
//    std::cout << "After substitution: " << logic.pp(updatedLabel) << '\n';
    PTRef simplifiedLabel = TrivialQuantifierElimination(logic).tryEliminateVarsExcept(utils.predicateArgsInOrder(
        getStateVersion(source)) + utils.predicateArgsInOrder(getNextStateVersion(target)), updatedLabel);
//    std::cout << "After simplification: " << logic.pp(simplifiedLabel) << std::endl;
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

std::vector<EId> ChcDirectedGraph::getEdges() const {
    std::vector<EId> retEdges;
    forEachEdge([&](DirectedEdge const & edge){
        retEdges.push_back(edge.id);
    });
    return retEdges;
}

std::vector<SymRef> ChcDirectedHyperGraph::getVertices() const {
    std::unordered_set<SymRef, SymRefHash> vertices;
    forEachEdge([&](DirectedHyperEdge const & edge){
        vertices.insert(edge.to);
    });
    vertices.insert(getEntry());
    return std::vector<SymRef>(vertices.begin(), vertices.end());
}

std::vector<DirectedHyperEdge> ChcDirectedHyperGraph::getEdges() const {
    std::vector<DirectedHyperEdge> retEdges;
    forEachEdge([&](DirectedHyperEdge const & edge){
        retEdges.push_back(edge);
    });
    return retEdges;
}

ChcDirectedHyperGraph::VertexContractionResult ChcDirectedHyperGraph::contractVertex(SymRef sym) {
    VertexContractionResult result;
    auto adjacencyList = AdjacencyListsGraphRepresentation::from(*this);
    auto const & incomingEdges = adjacencyList.getIncomingEdgesFor(sym);
    auto const & outgoingEdges = adjacencyList.getOutgoingEdgesFor(sym);
    std::transform(incomingEdges.begin(), incomingEdges.end(), std::back_inserter(result.incoming), [this](EId eid) {
        return this->getEdge(eid);
    });
    std::transform(outgoingEdges.begin(), outgoingEdges.end(), std::back_inserter(result.outgoing), [this](EId eid) {
        return this->getEdge(eid);
    });
    for (std::size_t incomingIndex = 0; incomingIndex < incomingEdges.size(); ++incomingIndex) {
        EId incomingId = incomingEdges[incomingIndex];
        if (getSources(incomingId).size() > 1) { throw std::logic_error("Unable to contract vertex with incoming hyperedge!"); }

        for (std::size_t outgoingIndex = 0; outgoingIndex < outgoingEdges.size(); ++outgoingIndex) {
            EId outgoingId = outgoingEdges[outgoingIndex];
            if (getSources(outgoingId).size() > 1 and incomingEdges.size() > 1) { throw std::logic_error("Unable to contract vertex with outgoing hyperedge!"); }
            auto replacingEdge = mergeEdgePair(incomingId, outgoingId);
            result.replacing.emplace_back(std::move(replacingEdge), std::make_pair(incomingIndex, outgoingIndex));
        }
    }
    deleteNode(sym);
    return result;
}

ChcDirectedHyperGraph::MergedEdges ChcDirectedHyperGraph::mergeMultiEdges() {
    ChcDirectedHyperGraph::MergedEdges mergedEdges;
    std::unordered_map<std::pair<SymRef, SymRef>, std::vector<EId>, EdgeHasher> buckets;
    forEachEdge([&](auto const & edge) {
        auto const & sources = edge.from;
        if (sources.size() != 1) { return; } // TODO: enable also merging hyperedges
        auto pair = std::make_pair(sources[0], edge.to);
        buckets[pair].push_back(edge.id);
    });
    for (auto const & bucketEntry : buckets) {
        auto const & bucket = bucketEntry.second;
        if (bucket.size() < 2) { continue; }
        auto & currentRecord = mergedEdges.emplace_back();
        vec<PTRef> labels;
        labels.capacity(bucket.size());
        for (auto index : bucket) {
            labels.push(edges.at(index).fla.fla);
            currentRecord.first.push_back(getEdge(index));
        }
        edges.at(bucket[0]).fla = InterpretedFla{logic.mkOr(std::move(labels))};
        std::for_each(bucket.begin() + 1, bucket.end(), [this](EId eid) { edges.erase(eid); });
        currentRecord.second = getEdge(bucket[0]);
    }
    return mergedEdges;
}

void ChcDirectedHyperGraph::deleteFalseEdges() {
    deleteMatchingEdges([this](auto const & edge) { return edge.fla.fla == logic.getTerm_false(); });
}

void ChcDirectedHyperGraph::deleteEdges(std::vector<EId> const & edgesToDelete) {
    for (EId eid : edgesToDelete) {
        auto it = edges.find(eid);
        assert(it != edges.end());
        edges.erase(it);
    }
}

ChcDirectedHyperGraph::VertexInstances::VertexInstances(ChcDirectedHyperGraph const & graph) {
    graph.forEachEdge([&](DirectedHyperEdge const & edge) {
        auto const & sources = edge.from;
        instanceCounter[edge.id].resize(sources.size());
        std::unordered_map<SymRef, unsigned, SymRefHash> edgeCounter;
        for (unsigned sourceIndex = 0; sourceIndex < sources.size(); ++sourceIndex) {
            auto source = sources[sourceIndex];
            unsigned instance = edgeCounter[source]++;
            instanceCounter.at(edge.id)[sourceIndex] = instance;
        }
    });
}

bool hasHyperEdge(
    SymRef vertex,
    AdjacencyListsGraphRepresentation const & adjacencyRepresentation,
    ChcDirectedHyperGraph const & graph
) {
    auto const & incoming = adjacencyRepresentation.getIncomingEdgesFor(vertex);
    auto const & outgoing = adjacencyRepresentation.getOutgoingEdgesFor(vertex);
    return std::any_of(incoming.begin(), incoming.end(), [&](EId eid){ return graph.getSources(eid).size() > 1; }) or
           std::any_of(outgoing.begin(), outgoing.end(), [&](EId eid){ return graph.getSources(eid).size() > 1; });
}

bool isNonLoopNode(
    SymRef vertex,
    AdjacencyListsGraphRepresentation const & adjacencyRepresentation,
    ChcDirectedHyperGraph const & graph
) {
    auto const & outgoing = adjacencyRepresentation.getOutgoingEdgesFor(vertex);
    return std::none_of(outgoing.begin(), outgoing.end(), [&](EId eid){ return graph.getTarget(eid) == vertex; });
}

bool isSimpleNode(
    SymRef vertex,
    AdjacencyListsGraphRepresentation const & adjacencyRepresentation
) {
    auto const & outgoing = adjacencyRepresentation.getOutgoingEdgesFor(vertex);
    auto const & incoming = adjacencyRepresentation.getIncomingEdgesFor(vertex);
    return incoming.size() == 1 or outgoing.size() == 1;
}

std::unique_ptr<ChcDirectedHyperGraph> ChcDirectedHyperGraph::makeEmpty(Logic & logic) {
    NonlinearCanonicalPredicateRepresentation predicateRepresentation(logic);
    predicateRepresentation.addRepresentation(logic.getSym_true(), {});
    predicateRepresentation.addRepresentation(logic.getSym_false(), {});
    return std::make_unique<ChcDirectedHyperGraph>(
        std::vector<DirectedHyperEdge>{},
        std::move(predicateRepresentation),
        logic
        );
}