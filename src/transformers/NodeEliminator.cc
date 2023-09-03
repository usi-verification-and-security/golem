/*
 * Copyright (c) 2022-2023, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "NodeEliminator.h"

#include "CommonUtils.h"
#include "utils/SmtSolver.h"

void NodeEliminator::BackTranslator::notifyRemovedVertex(SymRef sym, ContractionResult && contractionResult) {
    assert(nodeInfo.count(sym) == 0);
    removedNodes.push_back(sym);
    nodeInfo.insert({sym, std::move(contractionResult)});
}

Transformer::TransformationResult NodeEliminator::transform(std::unique_ptr<ChcDirectedHyperGraph> graph) {
    auto backTranslator = std::make_unique<BackTranslator>(graph->getLogic(), graph->predicateRepresentation());
    while(true) {
        auto adjancencyRepresentation = AdjacencyListsGraphRepresentation::from(*graph);
        auto vertices = adjancencyRepresentation.getNodes();
        // ignore entry and exit, those should never be removed
        vertices.erase(std::remove_if(vertices.begin(), vertices.end(),[&graph](SymRef vertex) {
            return vertex == graph->getEntry() or vertex == graph->getExit();
        }), vertices.end());
        auto predicateWrapper = [&](SymRef vertex) {
            return this->shouldEliminateNode(vertex, adjancencyRepresentation, *graph);
        };
        auto candidateForRemovalIt = std::find_if(vertices.begin(), vertices.end(), predicateWrapper);
        if (candidateForRemovalIt == vertices.end()) { break; }
        auto vertexToRemove = *candidateForRemovalIt;
        auto contractionResult = graph->contractVertex(vertexToRemove);
        backTranslator->notifyRemovedVertex(vertexToRemove, std::move(contractionResult));
    }
    return {std::move(graph), std::move(backTranslator)};
}

bool NonLoopEliminatorPredicate::operator()(
    SymRef vertex,
    AdjacencyListsGraphRepresentation const & ar,
    ChcDirectedHyperGraph const & graph) const {
    // TODO: Remove the constraint about hyperEdge
    return not hasHyperEdge(vertex, ar, graph) and isNonLoopNode(vertex, ar, graph);
}

bool SimpleNodeEliminatorPredicate::operator()(
    SymRef vertex,
    AdjacencyListsGraphRepresentation const & ar,
    ChcDirectedHyperGraph const & graph) const {
    if (isSimpleNode(vertex, ar) and isNonLoopNode(vertex, ar, graph)) {
        if (not hasHyperEdge(vertex, ar, graph)) { return true; }
        // We eliminate the node also if it has outgoing hyperedges,
        // under the condition that it has only a single incoming edge, which is simple,
        // and it occurs only once as a source in each outgoing hyperedge
        // TODO: Relax also this constraint
        auto const & incoming = ar.getIncomingEdgesFor(vertex);
        if (not (incoming.size() == 1 and graph.getSources(incoming[0]).size() == 1)) { return false; }
        auto const & outgoing = ar.getOutgoingEdgesFor(vertex);
        return std::all_of(outgoing.begin(), outgoing.end(), [&](EId edge) {
            auto const & sources = graph.getSources(edge);
           return std::count(sources.begin(), sources.end(), vertex) == 1;
        });
    }
    return false;
}
InvalidityWitness NodeEliminator::BackTranslator::translate(InvalidityWitness witness) {
    if (this->removedNodes.empty()) { return witness; }

    using ContractionInfo = std::pair<DirectedHyperEdge, std::pair<DirectedHyperEdge, DirectedHyperEdge>>;
    auto findContractionInfo = [&](EId eid) -> std::optional<ContractionInfo> {
        for (auto && [node, contractionResult] : nodeInfo) {
            for (auto const & [replacing, inout] : contractionResult.replacing) {
                if (replacing.id == eid) {
                    return std::make_pair(replacing,
                                          std::make_pair(contractionResult.incoming[inout.first],
                                                         contractionResult.outgoing[inout.second])
                                         );
                }
            }
        }
        return std::nullopt;
    };
    while(true) {
        auto & derivation = witness.getDerivation();
        // For each step, check if it uses one of the newly created edges
        bool stepReplaced = false;
        for (auto it = derivation.begin(); it != derivation.end(); ++it) {
            auto eid = it->clauseId;
            if (auto possibleContractInfo = findContractionInfo(eid); possibleContractInfo.has_value()) {
                auto const & contractionInfo = possibleContractInfo.value();
                // Incoming edge cannot be a hyperedge, but outgoing can!
                assert(contractionInfo.second.first.from.size() == 1);
                // TODO: Unify handling of hyperedges with summarized chains
                if (contractionInfo.second.second.from.size() == 1) {
                    std::vector<DirectedHyperEdge> chain = {contractionInfo.second.first,
                                                            contractionInfo.second.second};
                    auto const & replacingEdge = contractionInfo.first;
                    std::size_t index = it - derivation.begin();
                    auto newDerivation =
                        replaceSummarizingStep(derivation, index, chain, replacingEdge, predicateRepresentation, logic);
                    witness.setDerivation(std::move(newDerivation));
                } else { // outgoing is a hyperedge
                    std::size_t index = it - derivation.begin();
                    auto newDerivation =
                        expandStepWithHyperEdge(derivation, index, contractionInfo, predicateRepresentation, logic);
                    witness.setDerivation(std::move(newDerivation));
                }
                stepReplaced = true;
                break;
            }
        }
        if (not stepReplaced) {
            break;
        }
    }
    return witness;
}

#define SANITY_CHECK(cond) if (not (cond)) { assert(false); return ValidityWitness{}; }
ValidityWitness NodeEliminator::BackTranslator::translate(ValidityWitness witness) {
    if (this->removedNodes.empty()) { return witness; }
    auto definitions = witness.getDefinitions();

    auto definitionFor = [&](SymRef vertex) {
        if (vertex == logic.getSym_false()) { return logic.getTerm_false(); }
        if (vertex == logic.getSym_true()) { return logic.getTerm_true(); }
        auto it = std::find_if(definitions.begin(), definitions.end(), [&](auto const & entry){
            return logic.getSymRef(entry.first) == vertex;
        });
        return it != definitions.end() ? it->second : PTRef_Undef;
    };
    VersionManager manager(logic);
    TermUtils utils(logic);
    // Removed vertices must be iterated in reversed order
    for (auto rit = removedNodes.rbegin(); rit != removedNodes.rend(); ++rit) {
        auto vertex = *rit;
        auto const & info = nodeInfo.at(vertex);
        vec<PTRef> incomingFormulas;
        for (auto const & edge : info.incoming) {
            if (edge.from.size() != 1) { throw std::logic_error("NonLoopEliminator should not have processed hyperEdges!"); }
            PTRef sourceDef = definitionFor(edge.from[0]);
            SANITY_CHECK(sourceDef != PTRef_Undef); // Missing definition, cannot backtranslate
            sourceDef = manager.baseFormulaToSource(sourceDef);
            incomingFormulas.push(logic.mkAnd(sourceDef, edge.fla.fla));
        }
        vec<PTRef> outgoingFormulas;
        for (auto const & edge : info.outgoing) {
            vec<PTRef> components;
            components.push(edge.fla.fla);
            PTRef targetDef = definitionFor(edge.to);
            SANITY_CHECK(targetDef != PTRef_Undef); // Missing definition, cannot backtranslate
            targetDef = manager.baseFormulaToTarget(targetDef);
            components.push(logic.mkNot(targetDef));
            if (edge.from.size() > 1) { // HyperEdge
                auto sources = edge.from;
                auto vertexOccurences = std::count(sources.begin(), sources.end(), vertex);
                SANITY_CHECK(vertexOccurences == 1);
                sources.erase(std::remove(sources.begin(), sources.end(), vertex), sources.end());
                std::unordered_map<SymRef, std::size_t, SymRefHash> instances;
                for (auto otherSource : sources) {
                    auto instance = instances[otherSource]++;
                    PTRef sourceDef = definitionFor(otherSource);
                    SANITY_CHECK(sourceDef != PTRef_Undef); // Missing definition, cannot backtranslate
                    sourceDef = manager.baseFormulaToSource(sourceDef, instance);
                    components.push(sourceDef);
                }
            }
            outgoingFormulas.push(logic.mkAnd(std::move(components)));
        }
        TermUtils::substitutions_map substitutionsMap;
        utils.mapFromPredicate(predicateRepresentation.getSourceTermFor(vertex), predicateRepresentation.getTargetTermFor(vertex), substitutionsMap);
        PTRef incomingPart = logic.mkOr(std::move(incomingFormulas));
        PTRef outgoingPart = logic.mkOr(std::move(outgoingFormulas));
        outgoingPart = utils.varSubstitute(outgoingPart, substitutionsMap);
        SMTSolver solverWrapper(logic, SMTSolver::WitnessProduction::ONLY_INTERPOLANTS);
        auto & solver = solverWrapper.getCoreSolver();
        solver.insertFormula(incomingPart);
        solver.insertFormula(outgoingPart);
        auto res = solver.check();
        if (res != s_False) {
            throw std::logic_error("Error in backtranslating of nonloop elimination");
        }
        auto itpContext = solver.getInterpolationContext();
        vec<PTRef> itps;
        ipartitions_t Amask = 1;
        itpContext->getSingleInterpolant(itps, Amask);
        PTRef vertexSolution = manager.targetFormulaToBase(itps[0]);
        PTRef predicateSourceRepresentation = predicateRepresentation.getSourceTermFor(vertex);
        // TODO: Fix handling of 0-ary predicates
        PTRef predicate = logic.isVar(predicateSourceRepresentation) ? predicateSourceRepresentation : manager.sourceFormulaToBase(predicateSourceRepresentation);
        assert(definitions.count(predicate) == 0);
        definitions.insert({predicate, vertexSolution});
    }
    return ValidityWitness(std::move(definitions));
}