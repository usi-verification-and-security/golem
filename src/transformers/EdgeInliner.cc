/*
 * Copyright (c) 2024, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "EdgeInliner.h"

#include "transformers/CommonUtils.h"
#include "utils/SmtSolver.h"

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
                auto computePredecessors = [&](SymRef node) {
                    auto const & predecessorsIds = adjacencyLists.getIncomingEdgesFor(node);
                    std::vector<DirectedHyperEdge> predecessors;
                    std::transform(predecessorsIds.begin(), predecessorsIds.end(), std::back_inserter(predecessors), [&](EId eid) {
                        return graph->getEdge(eid);
                    });
                    return predecessors;
                };
                if (feasibleTransitions.empty()) {
                    // This edge can never be taken
                    // std::cout << "This edge can never be taken!" << std::endl;
                    backtranslator->notifyEdgeDeleted(edge, computePredecessors(source));
                    graph->deleteEdges({edge.id});
                } else if (feasibleTransitions.size() == 1) {
                    auto predecessor = feasibleTransitions[0];
                    if (graph->getSources(predecessor).size() != 1 or graph->getSources(predecessor).front() == graph->getTarget(predecessor)) { continue; }
                    // Only one way how to get here, combine the two edge and remove this one
                    // std::cout << "Only one feasible input! This edge can be removed!" << std::endl;
                    // std::cout << "Inlining edge " << edge.id.id << ": " << edge.from.front().x << " -> " << edge.to.x << '\n';
                    // std::cout << "Predecessor is " << feasibleTransitions[0].id << ": " << (graph->getSources(feasibleTransitions[0]).empty() ? " " : std::to_string(graph->getSources(feasibleTransitions[0]).front().x)) << " -> " << graph->getTarget(feasibleTransitions[0]).x << '\n';
                    auto predecessors = computePredecessors(source);
                    auto newEdge = graph->inlineEdge(edge.id, predecessor);
                    backtranslator->notifyEdgeReplaced(newEdge, edge, graph->getEdge(predecessor), std::move(predecessors));
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
    for (auto rit = entries.rbegin(); rit != entries.rend(); ++rit) {
        auto const & entry = *rit;
        if (std::holds_alternative<Deletion>(entry)) { continue; }
        auto const & replacementInfo = std::get<Replacement>(entry);
        bool replacementUsed = true;
        while(replacementUsed) {
            replacementUsed = false;
            auto & derivation = witness.getDerivation();
            for (auto it = derivation.begin(); it != derivation.end(); ++it) {
                if (it->clauseId == replacementInfo.addedEdge.id) {
                    assert(replacementInfo.removedEdge.from.size() == 1);
                    std::size_t index = it - derivation.begin();
                    auto newDerivation = replaceSummarizingStep(
                        derivation, index, {replacementInfo.predecessor, replacementInfo.removedEdge},
                        replacementInfo.addedEdge, predicateRepresentation, logic
                    );
                    witness.setDerivation(std::move(newDerivation));
                    replacementUsed = true;
                    break;
                }
            }
        }
    }
    return witness;
}

#define SANITY_CHECK(cond) if (not (cond)) { assert(false); return ValidityWitness{}; }
ValidityWitness EdgeInliner::BackTranslator::translate(ValidityWitness witness) {
    if (entries.empty()) { return witness; }
    auto definitions = witness.getDefinitions();
    VersionManager manager(logic);
    for (auto rit = entries.rbegin(); rit != entries.rend(); ++rit) {
        auto const & entry = *rit;
        if (std::holds_alternative<Deletion>(entry)) {
            auto const & deletedEdge = std::get<Deletion>(entry).deletedEdge;
            SANITY_CHECK(deletedEdge.from.size() == 1);
            auto source = deletedEdge.from.front();
            auto target = deletedEdge.to;
            SANITY_CHECK(predecessors.count(deletedEdge.id) > 0);
            if (definitions.find(source) == definitions.end()) {
                definitions.insert({source, logic.getTerm_true()});
            }
            // Compute an interpolant between the predecessors and the edge, conjoin to existing interpretation
            if (predecessors.at(deletedEdge.id).empty()) {
                definitions.at(source) = logic.getTerm_false();
            } else if (definitions.at(source) != logic.getTerm_false()) {
                vec<PTRef> incoming;
                for (auto const & predecessor : predecessors.at(deletedEdge.id)) {
                    incoming.push(predecessor.fla.fla);
                }
                PTRef incomingConstraint = logic.mkOr(std::move(incoming));
                PTRef outgoingConstraint = deletedEdge.fla.fla;
                PTRef interpolant = computeInterpolantFor(source, incomingConstraint, outgoingConstraint);
                PTRef & currentInterpretation = definitions.at(source);
                currentInterpretation = logic.mkAnd(currentInterpretation, interpolant);
            }
            if (definitions.find(target) == definitions.end()) {
                definitions.insert({target, logic.getTerm_true()});
            }
            continue;
        }
        assert(std::holds_alternative<Replacement>(entry));
        auto const & replacementInfo = std::get<Replacement>(entry);
        SANITY_CHECK(replacementInfo.predecessor.from.size() == 1 and replacementInfo.removedEdge.from.size() == 1);
        SymRef source = replacementInfo.predecessor.from.front();
        SymRef mid = replacementInfo.predecessor.to;
        SymRef target = replacementInfo.removedEdge.to;
        SANITY_CHECK(definitions.find(source) != definitions.end());
        SANITY_CHECK(definitions.find(mid) != definitions.end());
        SANITY_CHECK(definitions.find(target) != definitions.end());
        SANITY_CHECK(replacementInfo.predecessor.from.front() != replacementInfo.predecessor.to); // not a loop
        SANITY_CHECK(replacementInfo.removedEdge.from.size() == 1);
        // Compute an interpolant for mid between all predecessors and the removed edge
        SANITY_CHECK(predecessors.count(replacementInfo.removedEdge.id) > 0);
        vec<PTRef> incoming;
        for (auto const & predecessor : predecessors.at(replacementInfo.removedEdge.id)) {
            if (predecessor.id == replacementInfo.predecessor.id) {
                PTRef sourceInterpretation = manager.baseFormulaToSource(definitions.at(source));
                incoming.push(logic.mkAnd(sourceInterpretation, replacementInfo.predecessor.fla.fla));
            } else {
                incoming.push(predecessor.fla.fla);
            }
        }
        PTRef incomingConstraint = logic.mkOr(std::move(incoming));
        PTRef outgoingConstraint = logic.mkAnd(replacementInfo.removedEdge.fla.fla, logic.mkNot(manager.baseFormulaToTarget(definitions.at(target))));
        PTRef interpolant = computeInterpolantFor(mid, incomingConstraint, outgoingConstraint);
        PTRef & existingInterpretation = definitions.at(mid);
        existingInterpretation = logic.mkAnd(existingInterpretation, interpolant);
    }
    return ValidityWitness(std::move(definitions));
}

void EdgeInliner::BackTranslator::notifyEdgeDeleted(DirectedHyperEdge const & deletedEdge, Predecessors predecessors) {
    entries.emplace_back(Deletion{deletedEdge});
    assert(this->predecessors.find(deletedEdge.id) == this->predecessors.end());
    this->predecessors.insert({deletedEdge.id, std::move(predecessors)});
}

void EdgeInliner::BackTranslator::notifyEdgeReplaced(DirectedHyperEdge const & newEdge,
                                                     DirectedHyperEdge const & removedEdge,
                                                     DirectedHyperEdge const & predecessor,
                                                     Predecessors predecessors) {
    entries.emplace_back(Replacement{.addedEdge = newEdge, .removedEdge = removedEdge, .predecessor = predecessor});
    assert(this->predecessors.find(removedEdge.id) == this->predecessors.end());
    this->predecessors.insert({removedEdge.id, std::move(predecessors)});
}

std::vector<PTRef> EdgeInliner::BackTranslator::getAuxiliaryVarsFor(SymRef node) {
    PTRef sourceTerm = predicateRepresentation.getSourceTermFor(node);
    auto vars = TermUtils(logic).predicateArgsInOrder(sourceTerm);
    for (auto i = 0u; i < vars.size(); ++i) {
        PTRef & var = vars[i];
        auto sort = logic.getSortRef(var);
        std::string name = "$ei" + std::to_string(i);
        var = logic.mkVar(sort, name.c_str());
    }
    return vars;
}

PTRef EdgeInliner::BackTranslator::computeInterpolantFor(SymRef node, PTRef incoming, PTRef outgoing) {
    TermUtils utils(logic);
    SMTSolver solver(logic, SMTSolver::WitnessProduction::ONLY_INTERPOLANTS);
    solver.getConfig().setSimplifyInterpolant(4);
    TermUtils::substitutions_map substitutionsMap;
    auto auxiliaryVars = getAuxiliaryVarsFor(node);
    auto targetVars = utils.predicateArgsInOrder(predicateRepresentation.getTargetTermFor(node));
    assert(targetVars.size() == auxiliaryVars.size());
    for (auto i = 0u; i < targetVars.size(); ++i) {
        substitutionsMap.insert({targetVars[i], auxiliaryVars[i]});
    }
    PTRef incomingConstraintRenamed = utils.varSubstitute(incoming, substitutionsMap);
    // A part
    solver.assertProp(incomingConstraintRenamed);

    substitutionsMap.clear();
    auto sourceVars = utils.predicateArgsInOrder(predicateRepresentation.getSourceTermFor(node));
    assert(sourceVars.size() == auxiliaryVars.size());
    for (auto i = 0u; i < sourceVars.size(); ++i) {
        substitutionsMap.insert({sourceVars[i], auxiliaryVars[i]});
    }
    // B part
    PTRef outgoingConstraintRenamed = utils.varSubstitute(outgoing, substitutionsMap);
    solver.assertProp(outgoingConstraintRenamed);
    auto res = solver.check();
    if (res != SMTSolver::Answer::UNSAT) {
        std::cout << logic.pp(incomingConstraintRenamed) << '\n';
        std::cout << '\n' << logic.pp(outgoingConstraintRenamed) << '\n';
        throw std::logic_error("Error in backtranslating of edge inliner");
    }
    auto itpContext = solver.getInterpolationContext();
    vec<PTRef> itps;
    ipartitions_t Amask = 1;
    itpContext->getSingleInterpolant(itps, Amask);
    PTRef interpolant = itps[0];
    substitutionsMap.clear();
    auto const & baseVars = predicateRepresentation.getRepresentation(node);
    assert(baseVars.size() == auxiliaryVars.size());
    for (auto i = 0u; i < auxiliaryVars.size(); ++i) {
        substitutionsMap.insert({auxiliaryVars[i], baseVars[i]});
    }
    PTRef renamedInterpolant = utils.varSubstitute(interpolant, substitutionsMap);
    return renamedInterpolant;
}

