/*
 * Copyright (c) 2023-2025, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "TrivialEdgePruner.h"

#include "utils/SmtSolver.h"

namespace golem {
Transformer::TransformationResult TrivialEdgePruner::transform(std::unique_ptr<ChcDirectedHyperGraph> graph) {
    std::vector<EId> directEdges;
    graph->forEachEdge([&](auto const & edge) {
        if (edge.to == graph->getExit() and edge.from.size() == 1 and edge.from[0] == graph->getEntry()) {
            directEdges.push_back(edge.id);
        }
    });
    if (directEdges.empty()) { return {std::move(graph), std::make_unique<TrivialEdgePruner::BackTranslator>()}; }
    Logic & logic = graph->getLogic();
    // Test if any edge is satisfiable
    for (EId eid : directEdges) {
        SMTSolver solver(logic, SMTSolver::WitnessProduction::NONE);
        solver.assertProp(graph->getEdgeLabel(eid));
        auto res = solver.check();
        if (res == SMTSolver::Answer::SAT) {
            // satisfiable direct edge, reduce the graph to this edge
            NonlinearCanonicalPredicateRepresentation predicateRepresentation(logic);
            predicateRepresentation.addRepresentation(graph->getEntry(), {});
            predicateRepresentation.addRepresentation(graph->getExit(), {});
            auto singleEdgeGraph = std::make_unique<ChcDirectedHyperGraph>(
                std::vector<DirectedHyperEdge>{graph->getEdge(eid)}, std::move(predicateRepresentation), logic);
            return {std::move(singleEdgeGraph), std::make_unique<TrivialEdgePruner::BackTranslator>(eid)};
        }
        if (res != SMTSolver::Answer::UNSAT) {
            // Something went wrong, bail out without any change
            return {std::move(graph), std::make_unique<TrivialEdgePruner::BackTranslator>()};
        }
    }
    // Here we know that all direct edges from entry to exit are unsatisfiable, we can safely remove them
    graph->deleteEdges(directEdges);
    // Nothing to do during backtranslation
    return {std::move(graph), std::make_unique<TrivialEdgePruner::BackTranslator>()};
}

TrivialEdgePruner::BackTranslator::BackTranslator(EId satisfiableEdge) : satisfiableEdge(satisfiableEdge) {}

InvalidityWitness TrivialEdgePruner::BackTranslator::translate(InvalidityWitness witness) {
    if (not satisfiableEdge) return witness;
    assert(witness.getDerivation().size() == 2);
    witness.getDerivation()[1].clauseId = satisfiableEdge.value();
    return witness;
}
ValidityWitness TrivialEdgePruner::BackTranslator::translate(ValidityWitness witness) {
    assert(not satisfiableEdge);
    return witness;
}
} // namespace golem
