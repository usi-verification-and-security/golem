/*
 * Copyright (c) 2023-2025, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "SingleLoopTransformation.h"

#include "MultiEdgeMerger.h"
#include "QuantifierElimination.h"
#include "TransformationUtils.h"
#include "utils/SmtSolver.h"

namespace golem {
SingleLoopTransformation::TransformationResult
SingleLoopTransformation::transform(ChcDirectedGraph const & original) const {
    auto graph = std::make_unique<ChcDirectedGraph>(original);
    Logic & logic = graph->getLogic();
    TimeMachine timeMachine(logic);
    auto vertices = graph->getVertices();
    std::erase_if(vertices, [&](auto v) { return v == graph->getEntry() or v == graph->getExit(); });
    auto contractionData = graph->contractVertices(vertices);
    auto finalGraph = [&]() {
        auto result = MultiEdgeMerger().transform(graph->toHyperGraph());
        return result.first->toNormalGraph();
    }();

    auto ts = toTransitionSystem(*finalGraph, true);
    auto backTranslator = std::make_unique<WitnessBackTranslator>(original, *graph, std::move(contractionData));
    return {std::move(ts), std::move(backTranslator)};
}

// Witness backtranslation
VerificationResult
SingleLoopTransformation::WitnessBackTranslator::translate(TransitionSystemVerificationResult result) {
    if (result.answer == VerificationAnswer::UNSAFE) {
        auto witness = translateErrorPath(std::get<std::size_t>(result.witness));
        if (std::holds_alternative<NoWitness>(witness)) {
            return {result.answer, std::get<NoWitness>(std::move(witness))};
        }
        return {VerificationAnswer::UNSAFE, std::get<InvalidityWitness>(std::move(witness))};
    }
    if (result.answer == VerificationAnswer::SAFE) {
        auto witness = translateInvariant(std::get<PTRef>(result.witness));
        if (std::holds_alternative<NoWitness>(witness)) {
            return {result.answer, std::get<NoWitness>(std::move(witness))};
        }
        return {VerificationAnswer::SAFE, std::get<ValidityWitness>(std::move(witness))};
    }
    return VerificationResult(result.answer);
}

SingleLoopTransformation::WitnessBackTranslator::ErrorOr<InvalidityWitness>
SingleLoopTransformation::WitnessBackTranslator::translateErrorPath(std::size_t unrolling) {
    // We need to get the CEX path, which will define the locations in the graph
    Logic & logic = originalGraph.getLogic();
    TimeMachine tm(logic);
    std::vector<PTRef> inputs;
    std::vector<PTRef> outputs;
    PTRef transition = PTRef_Undef;
    contractedGraph.forEachEdge([&](DirectedEdge const & edge) {
        assert(edge.from != contractedGraph.getEntry() or edge.to != contractedGraph.getExit());
        if (edge.from == contractedGraph.getEntry()) {
            inputs.push_back(tm.sendFlaThroughTime(edge.fla.fla, -1));
        } else if (edge.to == contractedGraph.getExit()) {
            outputs.push_back(edge.fla.fla);
        } else {
            assert(edge.from == edge.to);
            assert(transition == PTRef_Undef);
            transition = edge.fla.fla;
        }
    });
    SMTSolver solver(logic, SMTSolver::WitnessProduction::ONLY_MODEL);
    solver.assertProp(logic.mkOr(inputs));
    for (auto i = 0u; i < unrolling; ++i) {
        solver.assertProp(tm.sendFlaThroughTime(transition, i));
    }
    solver.assertProp(tm.sendFlaThroughTime(logic.mkOr(outputs), unrolling));
    auto res = solver.check();
    assert(res == SMTSolver::Answer::SAT);
    if (res != SMTSolver::Answer::SAT) { throw std::logic_error("Unrolling should have been satisfiable"); }
    auto model = solver.getModel();

    std::vector<EId> errorEdges;
    auto adj = AdjacencyListsGraphRepresentation::from(originalGraph);
    auto currentVertex = originalGraph.getEntry();
    for (auto i = 0u; i <= unrolling + 1; ++i) {
        auto canBeTaken = [&](EId eid) {
            // TODO: We should evaluate also the constraint of the edge
            auto target = originalGraph.getTarget(eid);
            if (target == originalGraph.getExit()) { return i == unrolling + 1; }
            if (i == unrolling + 1) { return false; }
            auto locVar = tm.sendVarThroughTime(contractionData.locations.at(target), i);
            return model->evaluate(locVar) == logic.getTerm_true();
        };
        auto const & outgoing = adj.getOutgoingEdgesFor(currentVertex);
        auto it = std::find_if(outgoing.begin(), outgoing.end(), canBeTaken);
        if (it == outgoing.end()) { return NoWitness("SingleLoopTransformation: Could not backtranslate path"); }
        auto next = std::find_if(it + 1, outgoing.end(), canBeTaken);
        if (next != outgoing.end()) { return NoWitness("SingleLoopTransformation: Multiple edges possible"); }
        currentVertex = originalGraph.getTarget(*it);
        errorEdges.push_back(*it);
    }
    assert(errorEdges.size() == unrolling + 2);
    ErrorPath errorPath;
    errorPath.setPath(std::move(errorEdges));
    return InvalidityWitness::fromErrorPath(errorPath, originalGraph);
}

SingleLoopTransformation::WitnessBackTranslator::ErrorOr<ValidityWitness>
SingleLoopTransformation::WitnessBackTranslator::translateInvariant(PTRef inductiveInvariant) {
    Logic & logic = originalGraph.getLogic();
    // std::cout << "Invariant is " << logic.pp(inductiveInvariant) << std::endl;
    auto vertices = originalGraph.getVertices();
    TermUtils utils(logic);
    TermUtils::substitutions_map substitutions;
    for (auto vertex : vertices) {
        if (vertex == originalGraph.getEntry() or vertex == originalGraph.getExit()) { continue; }
        PTRef locationVar = contractionData.locations.at(vertex);
        substitutions.insert({locationVar, logic.getTerm_false()});
    }

    auto vertexInvariants = ValidityWitness::trivialDefinitions(originalGraph);
    for (auto vertex : vertices) {
        if (vertex == originalGraph.getEntry() or vertex == originalGraph.getExit()) { continue; }
        PTRef locationVar = contractionData.locations.at(vertex);
        substitutions.at(locationVar) = logic.getTerm_true();
        auto vertexInvariant = utils.varSubstitute(inductiveInvariant, substitutions);
        substitutions.at(locationVar) = logic.getTerm_false();

        // TODO: Better API from OpenSMT
        if (logic.isBooleanOperator(vertexInvariant)) {
            vertexInvariant = ::rewriteMaxArityAggresive(logic, vertexInvariant);
            // Repeat until fixpoint.
            // TODO: Improve the rewriting in OpenSMT. If child simplifies to atom, it can be used to simplify the
            // remaining children
            while (logic.isAnd(vertexInvariant) or logic.isOr(vertexInvariant)) {
                PTRef before = vertexInvariant;
                vertexInvariant = ::simplifyUnderAssignment_Aggressive(vertexInvariant, logic);
                if (before == vertexInvariant) { break; }
            }
        }
        // Check if all variables are from the current vertex
        auto allVars = variables(logic, vertexInvariant);
        auto vertexVars = getVarsForVertex(vertex);
        bool hasAlienVariable = std::any_of(allVars.begin(), allVars.end(),
                                            [&](PTRef var) { return vertexVars.find(var) == vertexVars.end(); });
        if (hasAlienVariable) {
            vec<PTRef> variablesToKeep;
            for (PTRef var : vertexVars) {
                variablesToKeep.push(var);
            }
            // Universally quantify all alien variables. QE eliminates existential quantifiers, so use double negation
            PTRef negatedInvariant = logic.mkNot(vertexInvariant);
            PTRef cleanNegatedInvariant = QuantifierElimination(logic).keepOnly(negatedInvariant, variablesToKeep);
            vertexInvariant = logic.mkNot(cleanNegatedInvariant);
        }
        // No alien variable, we can translate the invariant using predicate's variables
        TermUtils::substitutions_map varSubstitutions;
        PTRef basePredicate = TimeMachine(logic).versionedFormulaToUnversioned(originalGraph.getStateVersion(vertex));
        auto argsNum = logic.getPterm(basePredicate).nargs();
        for (auto i = 0u; i < argsNum; ++i) {
            PTRef positionVar = contractionData.positions.at(VarPosition{vertex, i});
            varSubstitutions.insert({positionVar, logic.getPterm(basePredicate)[i]});
        }
        vertexInvariant = utils.varSubstitute(vertexInvariant, varSubstitutions);
        vertexInvariants.insert({vertex, vertexInvariant});
        // std::cout << logic.printSym(vertex) << " -> " << logic.pp(vertexInvariant) << std::endl;
    }
    return ValidityWitness(std::move(vertexInvariants));
}

std::unordered_set<PTRef, PTRefHash>
SingleLoopTransformation::WitnessBackTranslator::getVarsForVertex(SymRef vertex) const {
    std::unordered_set<PTRef, PTRefHash> vars;
    for (auto const & entry : contractionData.positions) {
        if (entry.first.vertex == vertex) { vars.insert(entry.second); }
    }
    return vars;
}
} // namespace golem