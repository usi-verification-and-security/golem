/*
 * Copyright (c) 2022, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "NonLoopEliminator.h"

void NonLoopEliminator::BackTranslator::notifyRemovedVertex(SymRef sym, Entry edges) {
    assert(removedNodes.count(sym) == 0);
    removedNodes.insert({sym, std::move(edges)});
}

Transformer::TransformationResult NonLoopEliminator::transform(std::unique_ptr<ChcDirectedHyperGraph> graph) {
    auto backTranslator = std::make_unique<BackTranslator>(graph->getLogic(), graph->predicateRepresentation());
    while(true) {
        auto adjancencyRepresentation = AdjacencyListsGraphRepresentation::from(*graph);
        auto nonLoopingVertices = this->nonloopingVertices(*graph, adjancencyRepresentation);
        auto candidateForRemovalIt = std::find_if(nonLoopingVertices.begin(), nonLoopingVertices.end(), [&](SymRef vertex){
            // Vertex can be contracted if
            // 1. It does not have a self-loop
            // 2. If it does not have a hyperedge; TODO: Remove this constraint
            auto const & outgoing = adjancencyRepresentation.getOutgoingEdgesFor(vertex);
            if (std::any_of(outgoing.begin(), outgoing.end(), [&](EId eid){ return graph->getTarget(eid) == vertex or graph->getSources(eid).size() > 1; })) {
                return false;
            }
            auto const & incoming = adjancencyRepresentation.getIncomingEdgesFor(vertex);
            return std::none_of(incoming.begin(), incoming.end(), [&](EId eid){ return graph->getSources(eid).size() > 1; });
        });
        if (candidateForRemovalIt == nonLoopingVertices.end()) { break; }
        auto vertexToRemove = *candidateForRemovalIt;
        BackTranslator::Entry removedEdges;
        auto getEdge = [&](EId eid) { return graph->getEdge(eid); };
        auto const & incomingEdges = adjancencyRepresentation.getIncomingEdgesFor(vertexToRemove);
        std::transform(incomingEdges.begin(), incomingEdges.end(), std::back_inserter(removedEdges.incoming), getEdge);
        auto const & outgoingEdges = adjancencyRepresentation.getOutgoingEdgesFor(vertexToRemove);
        std::transform(outgoingEdges.begin(), outgoingEdges.end(), std::back_inserter(removedEdges.outgoing), getEdge);
        backTranslator->notifyRemovedVertex(vertexToRemove, std::move(removedEdges));
        graph->contractVertex(vertexToRemove);
    }
    return {std::move(graph), std::move(backTranslator)};
}

InvalidityWitness NonLoopEliminator::BackTranslator::translate(InvalidityWitness witness) {
    if (this->removedNodes.empty()) { return witness; }
    return InvalidityWitness{};
}

ValidityWitness NonLoopEliminator::BackTranslator::translate(ValidityWitness witness) {
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
    for (auto && [vertex, entry] : this->removedNodes) {
        vec<PTRef> incomingFormulas;
        for (auto const & edge : entry.incoming) {
            if (edge.from.size() != 1) { throw std::logic_error("NonLoopEliminator should not have processed hyperEdges!"); }
            PTRef sourceDef = definitionFor(edge.from[0]);
            sourceDef = manager.baseFormulaToSource(sourceDef);
            incomingFormulas.push(logic.mkAnd(sourceDef, edge.fla.fla));
        }
        vec<PTRef> outgoingFormulas;
        for (auto const & edge : entry.outgoing) {
            if (edge.from.size() != 1) { throw std::logic_error("NonLoopEliminator should not have processed hyperEdges!"); }
            PTRef targetDef = definitionFor(edge.to);
            if (targetDef == PTRef_Undef) { // Missing definition, cannot backtranslate
                return ValidityWitness{};
            }
            targetDef = manager.baseFormulaToTarget(targetDef);
            outgoingFormulas.push(logic.mkAnd(edge.fla.fla, logic.mkNot(targetDef)));
        }
        TermUtils::substitutions_map substitutionsMap;
        utils.insertVarPairsFromPredicates(predicateRepresentation.getSourceTermFor(vertex), predicateRepresentation.getTargetTermFor(vertex), substitutionsMap);
        PTRef incomingPart = logic.mkOr(std::move(incomingFormulas));
        PTRef outgoingPart = logic.mkOr(std::move(outgoingFormulas));
        outgoingPart = utils.varSubstitute(outgoingPart, substitutionsMap);
        SMTConfig config;
        const char * msg;
        config.setOption(SMTConfig::o_produce_models, SMTOption(false), msg);
        config.setOption(SMTConfig::o_produce_inter, SMTOption(true), msg);
        MainSolver solver(logic, config, "solver");
        solver.insertFormula(incomingPart);
        solver.insertFormula(outgoingPart);
        auto res = solver.check();
        if (res != s_False) {
            throw std::logic_error("Error in backtranslating of nonloops elimination");
        }
        auto itpContext = solver.getInterpolationContext();
        vec<PTRef> itps;
        ipartitions_t Amask = 1;
        itpContext->getSingleInterpolant(itps, Amask);
        PTRef vertexSolution = manager.targetFormulaToBase(itps[0]);
        PTRef predicate = manager.sourceFormulaToBase(predicateRepresentation.getSourceTermFor(vertex));
        assert(definitions.count(predicate) == 0);
        definitions.insert({predicate, vertexSolution});
    }
    return ValidityWitness(std::move(definitions));
}

std::vector<SymRef> NonLoopEliminator::nonloopingVertices(ChcDirectedHyperGraph const & graph, AdjacencyListsGraphRepresentation const & adjancencyRepresentation) {
    std::vector<SymRef> nonLoopingVertices;
    ReverseDFS(graph, adjancencyRepresentation).run([&](SymRef vertex){
        if (vertex == graph.getEntry() or vertex == graph.getExit()) { return; }
        auto const & outgoing = adjancencyRepresentation.getOutgoingEdgesFor(vertex);
        if (std::none_of(outgoing.begin(), outgoing.end(), [&](EId eid) { return graph.getTarget(eid) == vertex; })) {
            nonLoopingVertices.push_back(vertex);
        }
    }, [](SymRef){});
    return nonLoopingVertices;
}