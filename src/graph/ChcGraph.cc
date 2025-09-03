/*
 * Copyright (c) 2020-2025, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "ChcGraph.h"

#include "TransformationUtils.h"
#include "transformers/CommonUtils.h"

#include <algorithm>
#include <iostream>
#include <map>
#include <set>

namespace golem {
namespace {

class DFS {
    ChcDirectedGraph const & graph;
    AdjacencyListsGraphRepresentation const & adjacencyRepresentation;
    std::unordered_set<SymRef, SymRefHash> marked;

    [[nodiscard]] bool isMarked(SymRef sym) const { return marked.find(sym) != marked.end(); }
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
    DFS(ChcDirectedGraph const & graph, AdjacencyListsGraphRepresentation const & adjacencyRepresentation)
        : graph(graph), adjacencyRepresentation(adjacencyRepresentation) {}

    template<typename TPreorderAction, typename TPostorderAction>
    void run(TPreorderAction const & preorder, TPostorderAction const & postorder) && {
        runOnVertex(graph.getEntry(), preorder, postorder);
    }
};
} // namespace

std::vector<SymRef> reversePostOrder(ChcDirectedGraph const & graph,
                                     AdjacencyListsGraphRepresentation const & adjacencyRepresentation) {
    std::vector<SymRef> order = postOrder(graph, adjacencyRepresentation);
    std::reverse(order.begin(), order.end());
    return order;
}

std::vector<SymRef> postOrder(ChcDirectedGraph const & graph,
                              AdjacencyListsGraphRepresentation const & adjacencyRepresentation) {
    std::vector<SymRef> order;
    DFS(graph, adjacencyRepresentation).run([](SymRef) {}, [&order](SymRef v) { order.push_back(v); });
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
        std::transform(vars.begin(), vars.end(), vars.begin(), [&](PTRef var) { return manager.toBase(var); });
        newPredicates.addRepresentation(sym, std::move(vars));
    }

    std::vector<DirectedEdge> normalEdges;
    forEachEdge([&](DirectedHyperEdge const & edge) {
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
                PTRef newVar =
                    timeMachine.sendVarThroughTime(timeMachine.getVarVersionZero(manager.toBase(targetVar)), 1);
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
        out << dotIds[edge.from] << " -> " << dotIds[edge.to] << " [label = \""
            << (full ? logic.printTerm(edge.fla.fla) : "") << "\"];\n";
    });

    out << "}" << std::endl;
}

DirectedEdge ChcDirectedGraph::reverseEdge(DirectedEdge const & edge, TermUtils const & utils) const {
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

void ChcDirectedGraph::toSafetyGraph() {
    auto vertices = this->getVertices();
    auto edges = this->getEdges();
    std::unordered_set<SymRef, SymRefHash> nonexiting_vertices;
    std::unordered_map<SymRef, EId, SymRefHash> cycle_edges;
    for (auto v : vertices) {
        if (v!=getExit()) nonexiting_vertices.emplace(v);
    }
    for (auto e : edges) {
        if (this->getSource(e) != this->getTarget(e)) {
            nonexiting_vertices.erase(this->getSource(e));
        } else {
            cycle_edges.emplace(this->getSource(e), e);
        }
    }
    for (auto v: nonexiting_vertices) {
        if (cycle_edges.find(v) == cycle_edges.end()) {
            newEdge(v, getExit(),InterpretedFla(logic.getTerm_true()));
        } else {
            PTRef constr = getEdgeLabel(cycle_edges[v]);
            auto vars = getVariablesFromEdge(logic, *this, cycle_edges[v]);
            constr = QuantifierElimination(logic).keepOnly(constr, vars.stateVars);
            newEdge(v, getExit(),InterpretedFla(logic.mkNot(constr)));
        }
    }
}

ChcDirectedGraph ChcDirectedGraph::reverse() const {
    // same vertices, same canonical representation, switch entry and exit and reverse edges
    // NOTE: reversing edge means flipping state and next state variables
    TermUtils utils(logic);
    std::vector<DirectedEdge> redges;
    auto swapTrueFalse = [&](SymRef sym) {
        return sym == logic.getSym_false()  ? logic.getSym_true()
               : sym == logic.getSym_true() ? logic.getSym_false()
                                            : sym;
    };
    forEachEdge([&](auto const & edge) {
        auto reversed = reverseEdge(edge, utils);
        swapTrueFalse(reversed.from);
        swapTrueFalse(reversed.to);
        redges.push_back(reversed);
    });
    return {redges, this->predicates, logic};
}

AdjacencyListsGraphRepresentation AdjacencyListsGraphRepresentation::from(const ChcDirectedGraph & graph) {
    AdjacencyList incoming;
    AdjacencyList outgoing;
    incoming.insert({graph.getEntry(), {}});
    incoming.insert({graph.getExit(), {}});
    outgoing.insert({graph.getEntry(), {}});
    outgoing.insert({graph.getExit(), {}});
    graph.forEachEdge([&](DirectedEdge const & edge) {
        incoming[edge.to].push_back(edge.id);
        outgoing[edge.from].push_back(edge.id);
        // TODO: figure out a better way to ensure that all vertices are present in both lists
        incoming[edge.from];
        outgoing[edge.to];
    });
    return {std::move(incoming), std::move(outgoing)};
}

AdjacencyListsGraphRepresentation AdjacencyListsGraphRepresentation::from(const ChcDirectedHyperGraph & graph) {
    AdjacencyList incoming;
    AdjacencyList outgoing;
    incoming.insert({graph.getEntry(), {}});
    incoming.insert({graph.getExit(), {}});
    outgoing.insert({graph.getEntry(), {}});
    outgoing.insert({graph.getExit(), {}});
    graph.forEachEdge([&](DirectedHyperEdge const & edge) {
        // TODO: figure out a better way to ensure that all vertices are present in both lists
        incoming[edge.to].push_back(edge.id);
        for (SymRef sym : edge.from) {
            incoming[sym];
            auto & out = outgoing[sym];
            // We do not want to add this edge more than once (if the same source node is present more than once)
            if (out.empty() or out.back() != edge.id) { out.push_back(edge.id); }
        }
        outgoing[edge.to];
    });
    return {std::move(incoming), std::move(outgoing)};
}

std::unique_ptr<ChcDirectedHyperGraph> ChcDirectedGraph::toHyperGraph() const {
    TimeMachine timeMachine(logic);
    VersionManager manager(logic);
    TermUtils utils(logic);
    NonlinearCanonicalPredicateRepresentation newPredicates(logic);
    for (SymRef sym : getVertices()) {
        PTRef originalTerm = predicates.getSourceTermFor(sym);
        std::vector<PTRef> vars = utils.predicateArgsInOrder(originalTerm);
        std::transform(vars.begin(), vars.end(), vars.begin(),
                       [&](PTRef var) { return timeMachine.getUnversioned(var); });
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

std::optional<EId> getSelfLoopFor(SymRef sym, ChcDirectedGraph const & graph,
                                  AdjacencyListsGraphRepresentation const & adjacencyRepresentation) {
    auto const & outEdges = adjacencyRepresentation.getOutgoingEdgesFor(sym);
    auto it = std::find_if(outEdges.begin(), outEdges.end(), [&](EId eid) { return graph.getTarget(eid) == sym; });
    return it != outEdges.end() ? *it : std::optional<EId>{};
}

DirectedHyperEdge ChcDirectedHyperGraph::contractTrivialChain(std::vector<EId> const & trivialChain) {
    assert(trivialChain.size() >= 2);
    auto summaryEdge = mergeTrivialChain(trivialChain);
    std::vector<SymRef> vertices;
    vertices.reserve(trivialChain.size());
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

namespace {
std::vector<PTRef> getAuxiliaryVariablesFromEdge(ChcDirectedHyperGraph const & graph, EId eid) {
    Logic & logic = graph.getLogic();
    PTRef label = graph.getEdgeLabel(eid);
    TermUtils utils(logic);
    auto allVars = utils.getVars(label);
    auto nonAuxVars = [&] {
        std::unordered_set<PTRef, PTRefHash> acc;
        std::unordered_map<SymRef, unsigned, SymRefHash> instanceCount;
        auto targetVars = utils.predicateArgsInOrder(graph.getNextStateVersion(graph.getTarget(eid)));
        acc.insert(targetVars.begin(), targetVars.end());
        for (auto source : graph.getSources(eid)) {
            auto instance = instanceCount[source]++;
            auto sourceVars = utils.predicateArgsInOrder(graph.getStateVersion(source, instance));
            acc.insert(sourceVars.begin(), sourceVars.end());
        }
        return acc;
    }();

    std::vector<PTRef> auxVars;
    for (PTRef var : allVars) {
        if (nonAuxVars.count(var) == 0) { auxVars.push_back(var); }
    }
    return auxVars;
}

PTRef renameAuxiliaries(ChcDirectedHyperGraph const & graph, EId incoming) {
    PTRef incomingLabel = graph.getEdgeLabel(incoming);
    auto incomingAuxVars = getAuxiliaryVariablesFromEdge(graph, incoming);
    if (incomingAuxVars.empty()) { return incomingLabel; }
    static std::size_t counter = 0;
    Logic & logic = graph.getLogic();
    TermUtils::substitutions_map substitutionsMap;
    TimeMachine tm(logic);
    for (PTRef var : incomingAuxVars) {
        std::string newName = "gaux#" + std::to_string(counter++);
        PTRef newVar = tm.getVarVersionZero(newName, logic.getSortRef(var));
        substitutionsMap.insert({var, newVar});
    }
    PTRef newLabel = TermUtils(logic).varSubstitute(incomingLabel, substitutionsMap);
    return newLabel;
}
} // namespace

DirectedHyperEdge ChcDirectedHyperGraph::mergeEdgePair(EId incoming, EId outgoing) {
    assert(getSources(incoming).size() == 1); // Incoming must be a simple edge
    auto source = getSources(incoming)[0];
    auto common = getTarget(incoming);
    assert(source != common);
    auto target = getTarget(outgoing);
    if (getSources(outgoing).size() == 1 and target != common) { // Outgoing is a simple edge
        auto edge = mergeTrivialChain({incoming, outgoing});
        auto eid = edge.id;
        PTRef cleanedLabel = renameAuxiliaries(*this, eid);
        edges.at(eid).fla.fla = cleanedLabel;
        return getEdge(eid);
    }
    TermUtils utils(logic);
    // Special handling of outgoing hyperedge
    auto sources = getSources(outgoing);
    assert(std::count(sources.begin(), sources.end(), common) == 1);

    PTRef incomingLabel = getEdgeLabel(incoming);
    TermUtils::substitutions_map substitutionsMap;
    utils.mapFromPredicate(getNextStateVersion(common), getStateVersion(common, 0), substitutionsMap);
    PTRef renamedLabel = utils.varSubstitute(incomingLabel, substitutionsMap);

    PTRef newLabel = logic.mkAnd(renamedLabel, getEdgeLabel(outgoing));
    PTRef simplifiedLabel = TrivialQuantifierElimination(logic).tryEliminateVars(
        utils.predicateArgsInOrder(getStateVersion(common)), newLabel);

    for (auto & v : sources) {
        if (v == common) { v = source; }
    }
    if (source == getEntry()) {
        sources.erase(std::remove(sources.begin(), sources.end(), getEntry()), sources.end());
        if (sources.empty()) { sources.push_back(getEntry()); }
    }
    if (target == common) {
        // outgoing is self loop, we need to make former state variables auxiliary (if any are left after QE)
        substitutionsMap.clear();
        for (PTRef stateVar : utils.predicateArgsInOrder(getStateVersion(common))) {
            PTRef auxVar = createAuxiliaryVariable(logic.getSortRef(stateVar));
            substitutionsMap.insert({stateVar, auxVar});
        }
        simplifiedLabel = utils.varSubstitute(simplifiedLabel, substitutionsMap);
    }
    auto const eid = newEdge(std::move(sources), target, InterpretedFla{simplifiedLabel});
    PTRef const cleanedLabel = renameAuxiliaries(*this, eid);
    edges.at(eid).fla.fla = cleanedLabel;
    return getEdge(eid);
}

DirectedHyperEdge ChcDirectedHyperGraph::mergeTrivialChain(std::vector<EId> const & chain) {
    assert(std::all_of(chain.begin(), chain.end(), [this](EId eid) { return not isHyperEdge(eid); }));
    auto source = getSources(chain.front()).front();
    auto target = getTarget(chain.back());
    PTRef mergedLabel = mergeTrivialChainLabels(chain);
    auto eid = newEdge({source}, target, InterpretedFla{mergedLabel});
    return getEdge(eid);
}

/**
 * Computes a merged label of a chain of simple non-looping edges.
 * It relies on the fact that the edges are simple and non-looping to avoid introducing new auxiliary variables.
 * Instead, it just renames the source variables from successor to the target variables of predecessor.
 *
 * TODO: Is it sound to keep the intermediate variables without renaming them?
 * Probably only if there are no other edges related to the intermediate nodes.
 */
PTRef ChcDirectedHyperGraph::mergeTrivialChainLabels(std::vector<EId> const & chain) const {
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
    for (auto incomingIt = chain.begin(), outgoingIt = chain.begin() + 1; outgoingIt != chain.end();
         ++incomingIt, ++outgoingIt) {
        EId incoming = *incomingIt;
        EId outgoing = *outgoingIt;
        (void)outgoing;
        auto common = getTarget(incoming);
        assert(getSources(outgoing).size() == 1 and getSources(outgoing).front() == common and
               getTarget(outgoing) != common);
        // MB: Simply casting the target variables to current state from next state is only possible because this is trivial chain
        utils.mapFromPredicate(getNextStateVersion(common), getStateVersion(common), subMap);
    }
    PTRef combinedLabel = logic.mkAnd(std::move(labels));
    // std::cout << "Original labels: " << logic.pp(combinedLabel) << '\n';
    PTRef updatedLabel = utils.varSubstitute(combinedLabel, subMap);
    // std::cout << "After substitution: " << logic.pp(updatedLabel) << '\n';
    PTRef simplifiedLabel = TrivialQuantifierElimination(logic).tryEliminateVarsExcept(
        utils.predicateArgsInOrder(getStateVersion(source)) + utils.predicateArgsInOrder(getNextStateVersion(target)),
        updatedLabel);
    // std::cout << "After simplification: " << logic.pp(simplifiedLabel) << std::endl;
    return simplifiedLabel;
}

std::vector<SymRef> ChcDirectedGraph::getVertices() const {
    struct Comp {
        bool operator()(SymRef first, SymRef second) const { return first.x < second.x; }
    };
    std::set<SymRef, Comp> vertices;
    forEachEdge([&](DirectedEdge const & edge) {
        vertices.insert(edge.from);
        vertices.insert(edge.to);
    });
    vertices.insert(getEntry());
    vertices.insert(getExit());
    return {vertices.begin(), vertices.end()};
}

std::vector<EId> ChcDirectedGraph::getEdges() const {
    std::vector<EId> retEdges;
    forEachEdge([&](DirectedEdge const & edge) { retEdges.push_back(edge.id); });
    return retEdges;
}

std::vector<SymRef> ChcDirectedHyperGraph::getVertices() const {
    std::unordered_set<SymRef, SymRefHash> vertices;
    forEachEdge([&](DirectedHyperEdge const & edge) {
        vertices.insert(edge.to);
        for (auto source : edge.from) {
            vertices.insert(source);
        }
    });
    vertices.insert(getEntry());
    vertices.insert(getExit());
    return {vertices.begin(), vertices.end()};
}

std::vector<DirectedHyperEdge> ChcDirectedHyperGraph::getEdges() const {
    std::vector<DirectedHyperEdge> retEdges;
    forEachEdge([&](DirectedHyperEdge const & edge) { retEdges.push_back(edge); });
    return retEdges;
}

std::vector<PTRef> ChcDirectedHyperGraph::getSourceTerms(EId eid) const {
    auto const & sources = getSources(eid);
    std::vector<PTRef> sourceTerms;
    sourceTerms.reserve(sources.size());
    NonlinearCanonicalPredicateRepresentation::CountingProxy proxy = predicateRepresentation().createCountingProxy();
    for (auto source : sources) {
        sourceTerms.push_back(proxy.getSourceTermFor(source));
    }
    return sourceTerms;
}

ChcDirectedHyperGraph::VertexContractionResult ChcDirectedHyperGraph::contractVertex(SymRef sym) {
    VertexContractionResult result;
    auto adjacencyList = AdjacencyListsGraphRepresentation::from(*this);
    auto const & incomingEdges = adjacencyList.getIncomingEdgesFor(sym);
    auto const & outgoingEdges = adjacencyList.getOutgoingEdgesFor(sym);
    std::transform(incomingEdges.begin(), incomingEdges.end(), std::back_inserter(result.incoming),
                   [this](EId eid) { return this->getEdge(eid); });
    std::transform(outgoingEdges.begin(), outgoingEdges.end(), std::back_inserter(result.outgoing),
                   [this](EId eid) { return this->getEdge(eid); });
    for (std::size_t incomingIndex = 0; incomingIndex < incomingEdges.size(); ++incomingIndex) {
        EId incomingId = incomingEdges[incomingIndex];
        if (getSources(incomingId).size() > 1) {
            throw std::logic_error("Unable to contract vertex with incoming hyperedge!");
        }

        for (std::size_t outgoingIndex = 0; outgoingIndex < outgoingEdges.size(); ++outgoingIndex) {
            EId outgoingId = outgoingEdges[outgoingIndex];
            if (getSources(outgoingId).size() > 1 and incomingEdges.size() > 1) {
                throw std::logic_error("Unable to contract vertex with outgoing hyperedge!");
            }
            auto replacingEdge = mergeEdgePair(incomingId, outgoingId);
            result.replacing.emplace_back(std::move(replacingEdge), std::make_pair(incomingIndex, outgoingIndex));
        }
    }
    deleteNode(sym);
    return result;
}

DirectedHyperEdge ChcDirectedHyperGraph::inlineEdge(EId edge, EId predecessor) {
    if (getSources(predecessor).size() > 1) { throw std::logic_error("TODO: Implement this also for hyperedge"); }
    assert(getSources(predecessor).front() != getTarget(predecessor));
    auto replacingEdge = mergeEdgePair(predecessor, edge);
    deleteEdges({edge});
    return replacingEdge;
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

bool hasHyperEdge(SymRef vertex, AdjacencyListsGraphRepresentation const & adjacencyRepresentation,
                  ChcDirectedHyperGraph const & graph) {
    auto const & incoming = adjacencyRepresentation.getIncomingEdgesFor(vertex);
    auto const & outgoing = adjacencyRepresentation.getOutgoingEdgesFor(vertex);
    return std::any_of(incoming.begin(), incoming.end(), [&](EId eid) { return graph.getSources(eid).size() > 1; }) or
           std::any_of(outgoing.begin(), outgoing.end(), [&](EId eid) { return graph.getSources(eid).size() > 1; });
}

bool isNonLoopNode(SymRef vertex, AdjacencyListsGraphRepresentation const & adjacencyRepresentation,
                   ChcDirectedHyperGraph const & graph) {
    auto const & outgoing = adjacencyRepresentation.getOutgoingEdgesFor(vertex);
    return std::none_of(outgoing.begin(), outgoing.end(), [&](EId eid) { return graph.getTarget(eid) == vertex; });
}

bool isSimpleNode(SymRef vertex, AdjacencyListsGraphRepresentation const & adjacencyRepresentation) {
    auto const & outgoing = adjacencyRepresentation.getOutgoingEdgesFor(vertex);
    auto const & incoming = adjacencyRepresentation.getIncomingEdgesFor(vertex);
    return incoming.size() == 1 or outgoing.size() == 1;
}

std::unique_ptr<ChcDirectedHyperGraph> ChcDirectedHyperGraph::makeEmpty(Logic & logic) {
    NonlinearCanonicalPredicateRepresentation predicateRepresentation(logic);
    predicateRepresentation.addRepresentation(logic.getSym_true(), {});
    predicateRepresentation.addRepresentation(logic.getSym_false(), {});
    return std::make_unique<ChcDirectedHyperGraph>(std::vector<DirectedHyperEdge>{}, std::move(predicateRepresentation),
                                                   logic);
}

WitnessInfo ChcDirectedGraph::contractConnectedVertices(std::vector<EId> edges) {
    assert(edges.size() >= 2);
    assert(getSource(edges[0]) == getTarget(edges[edges.size() - 1]));
    TimeMachine timeMachine(logic);
    TermUtils utils(logic);
    std::vector<SymRef> vertices;
    vertices.reserve(edges.size());
    assert(std::adjacent_find(edges.begin(), edges.end(), [&](auto first, auto second) {
               return getTarget(first) != getSource(second);
           }) == edges.end());
    for (EId edge : edges) {
        vertices.push_back(getSource(edge));
    }

    LocationVarMap locationVars;
    PositionVarMap argVars;
    locationVars.reserve(vertices.size());
    for (auto vertex : vertices) {
        auto varName = std::string(".loc_") + std::to_string(vertex.x);
        locationVars.insert({vertex, timeMachine.getVarVersionZero(varName, logic.getSort_bool())});
    }

    for (auto vertex : vertices) {
        auto args_count = logic.getSym(vertex).nargs();
        for (uint32_t i = 0; i < args_count; ++i) {
            VarPosition pos = {vertex, i};
            auto varName = std::string(".arg_") + std::to_string(vertex.x) + '_' + std::to_string(i);
            PTRef var = timeMachine.getVarVersionZero(varName, logic.getSym(vertex)[i]);
            argVars.insert({pos, var});
        }
    }

    vec<PTRef> transitionRelationComponent;

    // KB: creation of the location variables for nodes and argument variables (params of predicates)
    std::vector<EId> allEdges = getEdges();
    EdgeTranslator edgeTranslator{*this, locationVars, argVars, {}};
    // KB: Translation of self-loop edges for the edges vertices
    //     and edges between vertices in DAG
    for (auto edge : allEdges) {
        if (std::find(vertices.begin(), vertices.end(), getSource(edge)) != vertices.end() &&
            std::find(vertices.begin(), vertices.end(), getTarget(edge)) != vertices.end()) {
            transitionRelationComponent.push(edgeTranslator.translateEdge(getEdge(edge)));
            removeEdge(edge);
        }
    };
    PTRef transitionRelation = logic.mkOr(std::move(transitionRelationComponent));

    // KB: Extraction of the state variables of the nested loop nodes, creation of new predicate to replace node with
    //     nested loops
    std::vector<PTRef> stateVars = [&locationVars, &argVars]() {
        std::vector<PTRef> ret;
        for (auto && entry : locationVars) {
            ret.push_back(entry.second);
        }
        for (auto && entry : argVars) {
            ret.push_back(entry.second);
        }
        return ret;
    }();

    vec<SRef> argSorts;
    std::vector<PTRef> vars;
    for (auto arg : stateVars) {
        argSorts.push(logic.getSortRef(arg));
        vars.push_back(timeMachine.getUnversioned(arg));
    }

    std::string name;
    for (auto vertex : vertices) {
        name += logic.getSymName(vertex);
    }

    SymRef newRef = logic.declareFun(name, logic.getSort_bool(), argSorts);
    predicates.addRepresentation(newRef, std::move(vars));

    // KB: Changing input and output edges to and from the loop in the graph with new state and loc variables
    //     Redirecting edges to the newly created vertice
    allEdges = getEdges();
    for (auto edge : allEdges) {
        if (std::find(vertices.begin(), vertices.end(), getSource(edge)) != vertices.end()) {
            PTRef newSourceLoc = locationVars.at(getSource(edge));
            auto oldEdgeVars = getVariablesFromEdge(logic, *this, edge);
            std::unordered_map<PTRef, PTRef, PTRefHash> subMap;
            for (uint i = 0; i < oldEdgeVars.stateVars.size(); i++) {
                subMap.insert(std::make_pair(oldEdgeVars.stateVars[i], argVars[{getSource(edge), i}]));
            }
            updateEdgeSource(edge, newRef);
            PTRef label = utils.varSubstitute(logic.mkAnd(getEdgeLabel(edge), newSourceLoc), subMap);

            updateEdgeLabel(edge, InterpretedFla{label});
        }
        if (std::find(vertices.begin(), vertices.end(), getTarget(edge)) != vertices.end()) {

            PTRef newTargetLoc = [&]() -> PTRef {
                vec<PTRef> negatedLocations;
                negatedLocations.capacity(locationVars.size());
                for (auto && entry : locationVars) {
                    if (entry.first != getTarget(edge)) {
                        negatedLocations.push(logic.mkNot(timeMachine.sendVarThroughTime(entry.second, 1)));
                    }
                }
                return logic.mkAnd(std::move(negatedLocations));
            }();
            PTRef destination = timeMachine.sendVarThroughTime(locationVars.at(getTarget(edge)), 1);

            auto oldEdgeVars = getVariablesFromEdge(logic, *this, edge);
            std::unordered_map<PTRef, PTRef, PTRefHash> subMap;
            for (uint i = 0; i < oldEdgeVars.nextStateVars.size(); i++) {
                subMap.insert(std::make_pair(oldEdgeVars.nextStateVars[i],
                                             timeMachine.sendVarThroughTime(argVars[{getTarget(edge), i}], 1)));
            }
            updateEdgeTarget(edge, newRef);
            PTRef label = utils.varSubstitute(getEdgeLabel(edge), subMap);

            updateEdgeLabel(
                edge, InterpretedFla{rewriteMaxArityClassic(logic, logic.mkAnd({newTargetLoc, destination, label}))});
        }
    }

    // KB: Creating new self-looping edge (which represents all the transitions in the outer loop)
    newEdge(newRef, newRef, InterpretedFla{transitionRelation});
    return {newRef, locationVars, argVars};
}
} // namespace golem
