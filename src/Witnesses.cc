/*
 * Copyright (c) 2020-2025, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "Witnesses.h"
#include "TransformationUtils.h"
#include "proofs/ProofSteps.h"
#include "utils/SmtSolver.h"
#include <memory>
#include <utility>

namespace golem {
void VerificationResult::printWitness(std::ostream & out, ArithLogic & logic, const ChcDirectedHyperGraph & originalGraph,
                                       std::vector<std::shared_ptr<Term>> originalAssertions, Normalizer::Equalities const & normalizingEqualities, const std::string& format) const {

    if (not hasWitness()) { return; }
    switch (answer) {
        case VerificationAnswer::SAFE: {
            getValidityWitness().print(out, originalGraph);
            return;
        }
        case VerificationAnswer::UNSAFE: {

            if (format == "legacy") {
                getInvalidityWitness().print(out, logic);
            } else {
                StepHandler stepHandler(getInvalidityWitness().getDerivation(), std::move(originalAssertions),
                                        normalizingEqualities,
                                        logic, originalGraph);
                if (format == "alethe") {
                    AlethePrintObserver observer(out);
                    stepHandler.registerObserver(&observer);
                    stepHandler.buildAletheProof();
                } else if (format == "intermediate") {
                    IntermediatePrintObserver intermediatePrintObserver(out);
                    stepHandler.registerObserver(&intermediatePrintObserver);
                    stepHandler.buildIntermediateProof();
                }
            }
            return;
        }
        default:
            return;
    }
}

InvalidityWitness InvalidityWitness::fromErrorPath(ErrorPath const & errorPath, ChcDirectedGraph const & graph) {
    using Derivation = InvalidityWitness::Derivation;
    Logic & logic = graph.getLogic();
    Derivation derivation;
    using DerivationStep = Derivation::DerivationStep;
    auto const & path = errorPath;
    if (path.isEmpty()) { return {}; }
    auto edgeIds = path.getEdges();
    // Compute model for the error path
    auto model = [&]() {
        SMTSolver solver(logic, SMTSolver::WitnessProduction::ONLY_MODEL);
        for (std::size_t i = 0; i < edgeIds.size(); ++i) {
            PTRef fla = graph.getEdgeLabel(edgeIds[i]);
            fla = TimeMachine(logic).sendFlaThroughTime(fla, i);
            solver.assertProp(fla);
        }
        auto res = solver.check();
        if (res != SMTSolver::Answer::SAT) { throw std::logic_error("Error in computing model for the error path"); }
        return solver.getModel();
    }();

    struct UPHelper {
        int counter = 0;
        ChcDirectedGraph const & graph;
        LinearPredicateVersioning predicateVersioning;

        PTRef operator()(SymRef vertex) {
            PTRef term = graph.getStateVersion(vertex);
            return predicateVersioning.sendPredicateThroughTime(term, counter++);
        }

        UPHelper(ChcDirectedGraph const & graph, Logic & logic) : graph(graph), predicateVersioning(logic) {}
    };
    assert(graph.getSource(edgeIds[0]) == logic.getSym_true());
    std::vector<SymRef> vertices;
    std::transform(edgeIds.begin(), edgeIds.end(), std::back_inserter(vertices),
                   [&graph](EId eid) { return graph.getSource(eid); });
    vertices.push_back(graph.getTarget(edgeIds.back()));
    std::vector<PTRef> vertexPredicates;
    std::transform(vertices.begin(), vertices.end(), std::back_inserter(vertexPredicates), UPHelper(graph, logic));

    auto instantiate = [&](PTRef predicate) {
        TermUtils utils(logic);
        auto vars = utils.predicateArgsInOrder(predicate);
        TermUtils::substitutions_map subst;
        for (PTRef var : vars) {
            subst.insert({var, model->evaluate(var)});
        }
        return utils.varSubstitute(predicate, subst);
    };

    assert(vertexPredicates.size() == edgeIds.size() + 1);
    std::size_t stepCounter = 0;
    // Make the `true` the first step of the derivation
    derivation.addDerivationStep({.index = stepCounter++, .premises = {}, .derivedFact = logic.getTerm_true(), .clauseId = {static_cast<id_t>(-1)}});
    for (std::size_t i = 0; i < edgeIds.size(); ++i) {
        auto id = edgeIds[i];
        DerivationStep step;
        step.index = stepCounter;
        step.clauseId = id;
        step.premises = std::vector<size_t>{stepCounter - 1};
        step.derivedFact = instantiate(vertexPredicates[i + 1]);
        derivation.addDerivationStep(std::move(step));
        ++stepCounter;
    }

    InvalidityWitness witness;
    witness.setDerivation(std::move(derivation));
    return witness;
}

InvalidityWitness InvalidityWitness::fromTransitionSystem(const ChcDirectedGraph & graph, std::size_t unrollings) {
    return fromErrorPath(ErrorPath::fromTransitionSystem(graph, unrollings), graph);
}

void InvalidityWitness::print(std::ostream & out, Logic & logic) const {
    auto derivationSize = derivation.size();
    for (std::size_t i = 0; i < derivationSize; ++i) {
        auto const & step = derivation[i];
        out << i << ":\t";
        out << logic.printTerm(step.derivedFact);
        if (not step.premises.empty()) {
            out << " -> ";
            for (auto index : step.premises) {
                out << ' ' << index;
            }
        }
        out << '\n';
    }
    out << std::endl;
}

void ValidityWitness::print(std::ostream & out, ChcDirectedHyperGraph const & graph) const {
    Logic & logic = graph.getLogic();
    for (auto && [symbol, definition] : interpretations) {
        if (logic.isTrue(symbol) or logic.isFalse(symbol)) { continue; }
        out << "  (define-fun " << logic.protectName(symbol) << " (";
        PTRef const stateVersion = graph.getStateVersion(symbol);
        PTRef const predicate = logic.getSym(symbol).nargs() == 0 ? stateVersion : VersionManager(logic).sourceFormulaToBase(stateVersion);
        const auto & args = TermUtils(logic).predicateArgsInOrder(predicate);
        for (std::size_t i = 0; i < args.size(); ++i) {
            auto sortString = logic.printSort(logic.getSortRef(args[i]));
            out << "(" << logic.protectName(logic.getSymRef(args[i])) << " " << sortString << ")" << (i == args.size()-1 ? "" : " ");
        }
        assert(logic.getSortRef(symbol) == logic.getSort_bool());
        out << ")" << " " << logic.printSort(logic.getSortRef(symbol)) << "\n";
        out << "    ";
        TermUtils(logic).printTermWithLets(out, definition);
        out << ")\n";
    }
}

ErrorPath ErrorPath::fromTransitionSystem(const ChcDirectedGraph & graph, std::size_t unrollings) {
    if (not isTransitionSystem(graph)) { return {}; }
    auto adjacencyList = AdjacencyListsGraphRepresentation::from(graph);
    auto vertices = graph.getVertices();
    assert(vertices.size() == 3);
    auto loopingVertex = *std::find_if(vertices.begin(), vertices.end(), [&](SymRef sym) {
        return sym != graph.getEntry() and sym != graph.getExit();
    });
    auto loopingVertexIncoming = adjacencyList.getIncomingEdgesFor(loopingVertex);
    auto it = std::find_if(loopingVertexIncoming.begin(), loopingVertexIncoming.end(), [&graph](EId eid) {
        return graph.getSource(eid) == graph.getTarget(eid);
    });
    assert(it != loopingVertexIncoming.end());
    EId loopingEdge = *it;
    EId startEdge = adjacencyList.getOutgoingEdgesFor(graph.getEntry())[0];
    EId finalEdge = adjacencyList.getIncomingEdgesFor(graph.getExit())[0];
    std::vector<EId> pathEdges(unrollings, loopingEdge);
    pathEdges.push_back(finalEdge);
    pathEdges.insert(pathEdges.begin(), startEdge);
    return ErrorPath(std::move(pathEdges));
}

ValidityWitness
ValidityWitness::fromTransitionSystem(Logic & logic, ChcDirectedGraph const & graph,
                                      TransitionSystem const & transitionSystem, PTRef inductiveInvariant) {
    if (not isTransitionSystem(graph)) { return {}; }
    auto vertices = graph.getVertices();
    assert(vertices.size() == 3);
    auto vertex = vertices[2];
    assert(vertex != graph.getEntry() and vertex != graph.getExit());
    TermUtils utils(logic);
    TimeMachine timeMachine(logic);
    TermUtils::substitutions_map subs;
    auto const graphVars = utils.predicateArgsInOrder(graph.getStateVersion(vertex));
    auto const systemVars = transitionSystem.getStateVars();
    vec<PTRef> unversionedVars;
    assert(graphVars.size() == systemVars.size());
    for (std::size_t i = 0; i < graphVars.size(); ++i) {
        unversionedVars.push(timeMachine.getUnversioned(graphVars[i]));
        subs.insert({systemVars[i], unversionedVars.last()});
    }
    PTRef graphInvariant = utils.varSubstitute(inductiveInvariant, subs);
    //    std::cout << "Graph invariant: " << logic.printTerm(graphInvariant) << std::endl;
    auto definitions = trivialDefinitions(graph);
    definitions.insert({vertex, graphInvariant});
    return ValidityWitness(std::move(definitions));
}

VerificationResult
translateTransitionSystemResult(TransitionSystemVerificationResult result, ChcDirectedGraph const & graph, TransitionSystem const & transitionSystem) {
    switch (result.answer) {
        case VerificationAnswer::SAFE:
            return {VerificationAnswer::SAFE, ValidityWitness::fromTransitionSystem(graph.getLogic(), graph, transitionSystem, std::get<PTRef>(result.witness))};
        case VerificationAnswer::UNSAFE:
            return {VerificationAnswer::UNSAFE, InvalidityWitness::fromTransitionSystem(graph, std::get<std::size_t>(result.witness))};
        case VerificationAnswer::UNKNOWN:
            return VerificationResult(VerificationAnswer::UNKNOWN);
    }
    assert(false);
    return VerificationResult(VerificationAnswer::UNKNOWN);
}

ValidityWitness ValidityWitness::trivialWitness(ChcDirectedGraph const & graph) {
    return ValidityWitness{trivialDefinitions(graph)};
}

ValidityWitness ValidityWitness::trivialWitness(ChcDirectedHyperGraph const & graph) {
    return ValidityWitness{trivialDefinitions(graph)};
}

ValidityWitness::definitions_t ValidityWitness::trivialDefinitions(ChcDirectedGraph const & graph) {
    return definitions_t{
        std::make_pair(graph.getEntry(), graph.getLogic().getTerm_true()),
        std::make_pair(graph.getExit(), graph.getLogic().getTerm_false())
    };
}

ValidityWitness::definitions_t ValidityWitness::trivialDefinitions(ChcDirectedHyperGraph const & graph) {
    return definitions_t{
        std::make_pair(graph.getEntry(), graph.getLogic().getTerm_true()),
        std::make_pair(graph.getExit(), graph.getLogic().getTerm_false())
    };
}
} // namespace golem

