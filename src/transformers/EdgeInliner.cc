/*
 * Copyright (c) 2024, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "EdgeInliner.h"

#include "transformers/CommonUtils.h"

namespace {
using KnownValues = std::vector<PTRef>;
using IndexMap = std::unordered_map<PTRef, unsigned, PTRefHash>;

KnownValues computeKnownValues(PTRef fla, IndexMap const & varToIndex, Logic & logic) {
    std::vector<PTRef> values(varToIndex.size(), PTRef_Undef);
    auto conjuncts = TermUtils(logic).getTopLevelConjuncts(fla);
    for (PTRef conjunct : conjuncts) {
        if (logic.isEquality(conjunct)) {
            PTRef lhs = logic.getPterm(conjunct)[0];
            PTRef rhs = logic.getPterm(conjunct)[1];
            if (logic.isConstant(lhs) or logic.isConstant(rhs)) {
                PTRef var = logic.isConstant(lhs) ? rhs : lhs;
                if (logic.isVar(var) and varToIndex.find(var) != varToIndex.end()) {
                    values[varToIndex.at(var)] = logic.isConstant(lhs) ? lhs : rhs;
                }
            }
        } else {
            if (logic.isVar(conjunct) or (logic.isNot(conjunct) and logic.isVar(logic.getPterm(conjunct)[0]))) {
                PTRef var = logic.isVar(conjunct) ? conjunct : logic.getPterm(conjunct)[0];
                if (varToIndex.find(var) != varToIndex.end()) {
                    values[varToIndex.at(var)] = logic.isVar(conjunct) ? logic.getTerm_true() : logic.getTerm_false();
                }
            }
        }
    }
    return values;
}
}

std::vector<EId> computeFeasibleTransitions(ChcDirectedHyperGraph const & graph, std::vector<EId> const & incomingEdges, EId outgoingEdge) {
    std::vector<EId> feasibleTransitions;
    if (incomingEdges.empty()) { return feasibleTransitions; }
    auto & logic = graph.getLogic();
    if (incomingEdges.size() == 1) {
        if (graph.getEdgeLabel(incomingEdges.front()) != logic.getTerm_false()) {
            feasibleTransitions.push_back(incomingEdges.front());
        }
        return feasibleTransitions;
    }
    assert(graph.getSources(outgoingEdge).size() == 1);
    auto vertex = graph.getSources(outgoingEdge).front();
    assert(std::all_of(incomingEdges.begin(), incomingEdges.end(), [&](EId eid){ return graph.getTarget(eid) == vertex; }));
    TermUtils utils(logic);
    auto sourceVars = utils.predicateArgsInOrder(graph.getStateVersion(vertex));
    std::unordered_map<PTRef, unsigned, PTRefHash> varToIndex;
    for (auto i = 0u; i < sourceVars.size(); ++i) {
        varToIndex.insert({sourceVars[i], i});
    }
    auto sourceValues = computeKnownValues(graph.getEdgeLabel(outgoingEdge), varToIndex, logic);
    assert(sourceValues.size() == sourceVars.size());
    // for (auto i = 0u; i < sourceVars.size(); ++i) {
    //     if (sourceValues[i] != PTRef_Undef) {
    //         std::cout << logic.pp(sourceVars[i]) << " -> " << logic.pp(sourceValues[i]) << '\n';
    //     }
    // }
    // std::cout << std::endl;

    for (EId incomingEdge : incomingEdges) {
        if (graph.getEdgeLabel(incomingEdge) == logic.getTerm_false()) { continue; }
        varToIndex.clear();
        auto targetVars = utils.predicateArgsInOrder(graph.getNextStateVersion(vertex));
        for (auto i = 0u; i < targetVars.size(); ++i) {
            varToIndex.insert({targetVars[i], i});
        }
        auto targetValues = computeKnownValues(graph.getEdgeLabel(incomingEdge), varToIndex, logic);
        assert(targetValues.size() == sourceValues.size());
        bool feasible = true;
        for (auto i = 0u; i < sourceValues.size(); ++i) {
            feasible &= sourceValues[i] == PTRef_Undef or targetValues[i] == PTRef_Undef or sourceValues[i] == targetValues[i];
        }
        if (feasible) { feasibleTransitions.push_back(incomingEdge); }
        // for (auto i = 0u; i < targetValues.size(); ++i) {
        //     if (targetValues[i] != PTRef_Undef) {
        //         std::cout << logic.pp(targetVars[i]) << " -> " << logic.pp(targetValues[i]) << '\n';
        //     }
        // }
        // std::cout << std::endl;
        // std::cout << "Pair " << incomingEdge.id << " and " << outgoingEdge.id << " is " << (feasible ? "feasible" : "infeasible") << '\n' << '\n';
    }
    return feasibleTransitions;

}

Transformer::TransformationResult EdgeInliner::transform(std::unique_ptr<ChcDirectedHyperGraph> graph) {
    auto backtranslator = std::make_unique<BackTranslator>(graph->getLogic(), graph->predicateRepresentation());
    bool somethingChanged = true;
    while (somethingChanged) {
        somethingChanged = false;
        auto adjacencyLists = AdjacencyListsGraphRepresentation::from(*graph);
        auto edges = graph->getEdges();
        for (auto i = 0u; i < edges.size(); ++i) {
            auto const & edge = edges[i];
            auto const & sources = edge.from;
            if (sources.size() == 1 and sources.front() != graph->getEntry()) {
                auto source = sources.front();
                // std::cout << "Checking edge " << edge.id.id << std::endl;
                auto const & incoming = adjacencyLists.getIncomingEdgesFor(source);
                auto feasibleTransitions = computeFeasibleTransitions(*graph, incoming, edge.id);
                // std::cout << "Number of feasible transitions: " << feasibleTransitions.size() << std::endl;
                if (feasibleTransitions.size() >= 2) { continue; }
                if (feasibleTransitions.empty()) {
                    // This edge can never be taken
                    // std::cout << "This edge can never be taken!" << std::endl;
                    graph->deleteEdges({edge.id});
                } else if (feasibleTransitions.size() == 1) {
                    auto predecessor = feasibleTransitions[0];
                    if (graph->getSources(predecessor).size() != 1 or graph->getSources(predecessor).front() == graph->getTarget(predecessor)) { continue; }
                    // Only one way how to get here, combine the two edge and remove this one
                    // std::cout << "Only one feasible input! This edge can be removed!" << std::endl;
                    // std::cout << "Inlining edge " << edge.id.id << ": " << edge.from.front().x << " -> " << edge.to.x << '\n';
                    // std::cout << "Predecessor is " << feasibleTransitions[0].id << ": " << (graph->getSources(feasibleTransitions[0]).empty() ? " " : std::to_string(graph->getSources(feasibleTransitions[0]).front().x)) << " -> " << graph->getTarget(feasibleTransitions[0]).x << '\n';
                    auto newEdge = graph->inlineEdge(edge.id, predecessor);
                    backtranslator->replacementInfo.emplace_back(std::move(newEdge), std::make_pair(graph->getEdge(predecessor), edge));
                }
                somethingChanged = true;
                // recompute necessary information
                adjacencyLists = AdjacencyListsGraphRepresentation::from(*graph);
            }
        }
    }
    return std::make_pair(std::move(graph), std::move(backtranslator));
}

InvalidityWitness EdgeInliner::BackTranslator::translate(InvalidityWitness witness) {
    for (auto rit = replacementInfo.rbegin(); rit != replacementInfo.rend(); ++rit) {
        auto const & entry = *rit;
        bool replacementUsed = true;
        while(replacementUsed) {
            replacementUsed = false;
            auto & derivation = witness.getDerivation();
            for (auto it = derivation.begin(); it != derivation.end(); ++it) {
                if (it->clauseId == entry.first.id) {
                    assert(entry.second.second.from.size() == 1);
                    std::size_t index = it - derivation.begin();
                    auto newDerivation = replaceSummarizingStep(derivation, index, {entry.second.first, entry.second.second}, entry.first, predicateRepresentation, logic);
                    witness.setDerivation(std::move(newDerivation));
                    replacementUsed = true;
                    break;
                }
            }
        }
    }
    return witness;
}

