/*
 * Copyright (c) 2022-2023, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "SimpleChainSummarizer.h"

#include "CommonUtils.h"

#include "utils/SmtSolver.h"

Transformer::TransformationResult SimpleChainSummarizer::transform(std::unique_ptr<ChcDirectedHyperGraph> graph) {
    auto translator = std::make_unique<BackTranslator>(graph->getLogic(), graph->predicateRepresentation());
    while(true) {
        AdjacencyListsGraphRepresentation adjacencyList = AdjacencyListsGraphRepresentation::from(*graph);
        auto isTrivial = [&](SymRef sym) {
            auto const & incoming = adjacencyList.getIncomingEdgesFor(sym);
            if (incoming.size() != 1) { return false; }
            auto const & outgoing = adjacencyList.getOutgoingEdgesFor(sym);
            if (outgoing.size() != 1) { return false; }
            EId in = incoming[0];
            EId out = outgoing[0];
            return in != out and graph->getSources(in).size() == 1 and graph->getSources(out).size() == 1;
        };
        auto vertices = graph->getVertices();
        auto it = std::find_if(vertices.begin(), vertices.end(), isTrivial);
        if (it == vertices.end()) { break; }
        auto trivialVertex = *it;
        auto trivialChain = [&](SymRef vertex) {
            std::vector<EId> edges;
            auto current = vertex;
            do {
                auto const & outgoing = adjacencyList.getOutgoingEdgesFor(current);
                assert(outgoing.size() == 1);
                edges.push_back(outgoing[0]);
                current = graph->getTarget(outgoing[0]);
            } while (isTrivial(current));
            current = vertex;
            do {
                auto const & incoming = adjacencyList.getIncomingEdgesFor(current);
                assert(incoming.size() == 1);
                edges.insert(edges.begin(), incoming[0]);
                auto const & sources = graph->getSources(incoming[0]);
                assert(sources.size() == 1);
                current = sources[0];
            } while (isTrivial(current));
            return edges;
        }(trivialVertex);
        std::vector<DirectedHyperEdge> summarizedChain;
        std::transform(trivialChain.begin(), trivialChain.end(), std::back_inserter(summarizedChain), [&](EId eid) {
//            std::cout << "Edge in chain: " << logic.pp(graph->getEdgeLabel(eid)) << std::endl;
            return graph->getEdge(eid);
        });
        auto summaryEdge = graph->contractTrivialChain(trivialChain);
//        std::cout << "Summary edge: " << logic.pp(summaryEdge.fla.fla) << std::endl;
        translator->addSummarizedChain({summarizedChain, summaryEdge});
    }
    return {std::move(graph), std::move(translator)};
}

InvalidityWitness SimpleChainSummarizer::BackTranslator::translate(InvalidityWitness witness) {
    if (summarizedChains.empty()) { return witness; }

    for (auto const & [chain, replacingEdge] : summarizedChains) {
        EId eid = replacingEdge.id;
        // replace all occurrences of this edge
        while(true) {
            auto const & derivation = witness.getDerivation();
            auto it = std::find_if(derivation.begin(), derivation.end(), [eid](auto const & step){ return step.clauseId == eid; });
            if (it == derivation.end()) { break; }
            std::size_t stepIndex = it - derivation.begin();
            auto newDerivation = replaceSummarizingStep(derivation, stepIndex, chain, replacingEdge, predicateRepresentation, logic);
            witness.setDerivation(std::move(newDerivation));
        }
    }
    return witness;
}

ValidityWitness SimpleChainSummarizer::BackTranslator::translate(ValidityWitness witness) {
    if (summarizedChains.empty()) { return witness; }
    auto definitions = witness.getDefinitions();
    // TODO: assert that we have true and false already
    definitions.insert({logic.getTerm_true(), logic.getTerm_true()});
    definitions.insert({logic.getTerm_false(), logic.getTerm_false()});
    std::reverse(summarizedChains.begin(), summarizedChains.end());
    TermUtils utils(logic);
    VersionManager manager(logic);
    for (auto && [chain, summary] : summarizedChains) {
        // Compute definitions for vertices on the chain using path interpolants
        SMTSolver solver(logic, SMTSolver::WitnessProduction::ONLY_INTERPOLANTS);
        assert(summary.from.size() == 1);
        PTRef sourceInterpretation = manager.baseFormulaToSource(
            definitions.at(manager.sourceFormulaToBase(predicateRepresentation.getSourceTermFor(summary.from.front())))
        );
        solver.assertProp(sourceInterpretation);
        for (auto const & edge : chain) {
            TermUtils::substitutions_map substitutionsMap;
            auto target = edge.to;
            utils.mapFromPredicate(predicateRepresentation.getTargetTermFor(target), predicateRepresentation.getSourceTermFor(target), substitutionsMap);
            PTRef updatedLabel = utils.varSubstitute(edge.fla.fla, substitutionsMap);
            solver.assertProp(updatedLabel);
        }
        PTRef predicate = predicateRepresentation.getSourceTermFor(summary.to);
        // MB: We cannot try to rewrite 0-ary predicates
        PTRef targetInterpretation = logic.isVar(predicate) ? definitions.at(predicate) : manager.baseFormulaToSource(
            definitions.at(manager.sourceFormulaToBase(predicate))
        );
        solver.assertProp(logic.mkNot(targetInterpretation));
        auto res = solver.check();
        if (res != SMTSolver::Answer::UNSAT) {
            //throw std::logic_error("SimpleChainBackTranslator could not recompute solution!");
            std::cerr << "; SimpleChainBackTranslator could not recompute solution! Solver could not prove UNSAT!" << std::endl;
            return ValidityWitness();
        }
        auto itpCtx = solver.getInterpolationContext();
        std::vector<ipartitions_t> partitionings;
        ipartitions_t p = 1;
        for (auto i = 0u; i < chain.size() - 1; ++i) {
            opensmt::setbit(p, i + 1); // MB: +1 for the source interpretation
            partitionings.push_back(p);
        }
        vec<PTRef> itps;
        itpCtx->getPathInterpolants(itps, partitionings);
        for (auto i = 0u; i < chain.size() - 1; ++i) {
            auto target = chain[i].to;
            PTRef predicate = predicateRepresentation.getSourceTermFor(target);
            predicate = logic.getPterm(predicate).size() > 0 ? VersionManager(logic).sourceFormulaToBase(predicate) : predicate;
            if (definitions.count(predicate) > 0) {
                std::cerr << "; Unexpected situation in SimpleChainBackTranslator: Predicate already has a solution!" << std::endl;
                return ValidityWitness();
            }
            definitions.insert({predicate, VersionManager(logic).sourceFormulaToBase(itps[i])});
        }
    }
    return ValidityWitness(std::move(definitions));
}
