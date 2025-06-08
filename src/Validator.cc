/*
 * Copyright (c) 2020-2025, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "Validator.h"

#include "utils/SmtSolver.h"
#include "utils/StdUtils.h"

namespace golem {
Validator::Result Validator::validate(ChcDirectedHyperGraph const & graph, VerificationResult const & result) {
    if (not result.hasWitness()) { return Validator::Result::NOT_VALIDATED; }
    switch (result.getAnswer()) {
        case VerificationAnswer::SAFE:
            return validateValidityWitness(graph, result.getValidityWitness());
        case VerificationAnswer::UNSAFE:
            return validateInvalidityWitness(graph, result.getInvalidityWitness());
        default:
            return Validator::Result::NOT_VALIDATED;
    }
    return Validator::Result::NOT_VALIDATED;
}

Validator::Result Validator::validateValidityWitness(ChcDirectedHyperGraph const & graph, ValidityWitness const & witness) const {
    auto definitions = witness.getDefinitions();
    assert(definitions.find(graph.getEntry()) != definitions.end());
    assert(definitions.find(graph.getExit()) != definitions.end());

    VersionManager versionManager(logic);
    // Check that definitions do not contain any auxiliary variables
    for (auto const & [vertex, definition] : definitions) {
        auto defVars = TermUtils(logic).getVars(definition);
        PTRef stateVersion = graph.getStateVersion(vertex);
        if (logic.getPterm(stateVersion).size() == 0) {
            if (defVars.size() > 0) { return Result::NOT_VALIDATED; }
            continue;
        }
        auto predicateVars = TermUtils(logic).predicateArgsInOrder(versionManager.sourceFormulaToBase(stateVersion));
        if (not isSubsetOf(defVars, predicateVars)) { return Result::NOT_VALIDATED; }
    }

    // get correct interpretation for each node
    auto getInterpretation = [&](SymRef symbol) -> PTRef {
        auto const it = definitions.find(symbol);
        if (it == definitions.end()) {
            std::cerr << ";Missing definition of a predicate " << logic.printSym(symbol) << std::endl;
            return PTRef_Undef;
        }
        return it->second;
    };

    ChcDirectedHyperGraph::VertexInstances vertexInstances(graph);
    auto edges = graph.getEdges();
    for (auto const & edge : edges) {
        vec<PTRef> bodyComponents;
        PTRef constraint = edge.fla.fla;
        bodyComponents.push(constraint);
        for (std::size_t i = 0; i < edge.from.size(); ++i) {
            auto source = edge.from[i];
            PTRef interpretation = getInterpretation(source);
            if (interpretation == PTRef_Undef) { return Result::NOT_VALIDATED; }
            PTRef versioned = versionManager.baseFormulaToSource(interpretation, vertexInstances.getInstanceNumber(edge.id, i));
            bodyComponents.push(versioned);
        }
        PTRef interpretedBody = logic.mkAnd(std::move(bodyComponents));
        PTRef interpretedHead = getInterpretation(edge.to);
        if (interpretedHead == PTRef_Undef) { return Result::NOT_VALIDATED; }
        PTRef versionedInterpretedHead = versionManager.baseFormulaToTarget(interpretedHead);
        PTRef query = logic.mkAnd(interpretedBody, logic.mkNot(versionedInterpretedHead));
        {
            SMTSolver solver(logic, SMTSolver::WitnessProduction::NONE);
            solver.assertProp(query);
            auto res = solver.check();
            if (res != SMTSolver::Answer::UNSAT) {
                std::cerr << ";Edge not validated!";
                // TODO: print edge
                return Result::NOT_VALIDATED;
            }
        }
    }
    return Result::VALIDATED;
}


Validator::Result validateStep(
    std::size_t stepIndex,
    InvalidityWitness::Derivation const & derivation,
    ChcDirectedHyperGraph const & graph,
    ChcDirectedHyperGraph::VertexInstances const & vertexInstances
    ) {
    Logic & logic = graph.getLogic();
    auto const & step = derivation[stepIndex];
    EId edge = step.clauseId;
    TermUtils::substitutions_map subst;
    TermUtils utils(logic);
    auto fillVariables = [&](PTRef derivedFact, PTRef normalizedPredicate) {
        assert(logic.getSymRef(derivedFact) == logic.getSymRef(normalizedPredicate));
        auto const & term = logic.getPterm(derivedFact); (void) term;
        assert(std::all_of(term.begin(), term.end(), [&](PTRef arg) { return logic.isConstant(arg); }));
        utils.mapFromPredicate(normalizedPredicate, derivedFact, subst);
    };
    // get values for the variables from predicates
    auto const & sourceNodes = graph.getSources(edge);
    assert(sourceNodes.size() == step.premises.size());
    for (std::size_t i = 0; i < sourceNodes.size(); ++i) {
        auto source = sourceNodes[i];
        auto const & premise = derivation[step.premises[i]];
        fillVariables(premise.derivedFact, graph.getStateVersion(source, vertexInstances.getInstanceNumber(edge, i)));
    }
    auto target = graph.getTarget(edge);
    fillVariables(step.derivedFact, graph.getNextStateVersion(target));
    PTRef constraintAfterSubstitution = utils.varSubstitute(graph.getEdgeLabel(edge), subst);
    if (constraintAfterSubstitution == logic.getTerm_true()) { return Validator::Result::VALIDATED; }
    if (constraintAfterSubstitution == logic.getTerm_false()) { return Validator::Result::NOT_VALIDATED; }
    SMTSolver solver(logic, SMTSolver::WitnessProduction::NONE);
    solver.assertProp(constraintAfterSubstitution);
    auto res = solver.check();
    if (res == SMTSolver::Answer::SAT) { return Validator::Result::VALIDATED; }
    return Validator::Result::NOT_VALIDATED;
}

Validator::Result
Validator::validateInvalidityWitness(ChcDirectedHyperGraph const & graph, InvalidityWitness const & witness) const {
    auto const & derivation = witness.getDerivation();
    auto derivationSize = derivation.size();
    if (derivationSize == 0) { return Result::NOT_VALIDATED; }
    ChcDirectedHyperGraph::VertexInstances vertexInstances(graph);
    if (derivation[0].derivedFact != logic.getTerm_true()) {
        assert(false);
        std::cerr << "; Validator: Invalidity witness does not start with TRUE!\n";
        return Result::NOT_VALIDATED;
    }
    if (derivation.last().derivedFact != logic.getTerm_false()) {
        std::cerr << "; Validator: Root of the invalidity witness is not FALSE!\n";
        return Result::NOT_VALIDATED;
    }
    for (std::size_t i = 1; i < derivationSize; ++i) {
        auto result = validateStep(i, derivation, graph, vertexInstances);
        if (result == Validator::Result::NOT_VALIDATED) { return result; }
    }
    return Validator::Result::VALIDATED;
}
} // namespace golem
