/*
 * Copyright (c) 2020 - 2022, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "Validator.h"

Validator::Result Validator::validate(ChcDirectedHyperGraph const & graph, VerificationResult const & result) {
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

Validator::Result Validator::validateValidityWitness(ChcDirectedHyperGraph const & graph, ValidityWitness const & witness) {
    auto definitions = witness.getDefinitions();
    if (definitions.find(logic.getTerm_false()) == definitions.end()) {
        definitions.insert({logic.getTerm_false(), logic.getTerm_false()});
        definitions.insert({logic.getTerm_true(), logic.getTerm_true()});
    }
    TermUtils utils(logic);
    ChcDirectedHyperGraph::VertexInstances vertexInstances(graph);
    // get correct interpretation for each node
    auto getInterpretation = [&](PTRef nodePredicate) -> PTRef {
        auto symbol = logic.getSymRef(nodePredicate);
        auto it = std::find_if(definitions.begin(), definitions.end(),
                               [this,symbol](auto const & entry) {
                                   return logic.getSymRef(entry.first) == symbol;
                               });
        if (it == definitions.end()) {
            std::cerr << ";Missing definition of a predicate " << logic.printSym(symbol) << std::endl;
            return PTRef_Undef;
        }
        // we need to substitute real arguments in the definition of the predicate
        PTRef definitionTemplate = it->second;
        // build the substitution map
        std::unordered_map<PTRef, PTRef, PTRefHash> subst;
        utils.mapFromPredicate(it->first, nodePredicate, subst);
        return utils.varSubstitute(definitionTemplate, subst);
    };

    auto edges = graph.getEdges();
    for (auto const & edge : edges) {
        vec<PTRef> bodyComponents;
        PTRef constraint = edge.fla.fla;
        bodyComponents.push(constraint);
        for (std::size_t i = 0; i < edge.from.size(); ++i) {
            auto source = edge.from[i];
            PTRef predicate = graph.getStateVersion(source, vertexInstances.getInstanceNumber(edge.id, i));
            PTRef interpreted = getInterpretation(predicate);
            if (interpreted == PTRef_Undef) { return Result::NOT_VALIDATED; }
            bodyComponents.push(interpreted);
        }
        PTRef interpretedBody = logic.mkAnd(std::move(bodyComponents));
        PTRef interpretedHead = getInterpretation(graph.getNextStateVersion(edge.to));
        PTRef query = logic.mkAnd(interpretedBody, logic.mkNot(interpretedHead));
        {
            SMTConfig config;
            MainSolver solver(logic, config, "validator");
            solver.insertFormula(query);
            auto res = solver.check();
            if (res != s_False) {
                std::cerr << ";Edge not validated!";
                // TODO: print edge
                return Validator::Result::NOT_VALIDATED;
            }
        }
    }
    return Validator::Result::VALIDATED;
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
    auto sourceNodes = graph.getSources(edge);
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
    SMTConfig config;
    MainSolver solver(logic, config, "validator");
    solver.insertFormula(constraintAfterSubstitution);
    auto res = solver.check();
    if (res == s_True) { return Validator::Result::VALIDATED; }
    return Validator::Result::NOT_VALIDATED;
}

Validator::Result
Validator::validateInvalidityWitness(ChcDirectedHyperGraph const & graph, InvalidityWitness const & witness) {
    auto const & derivation = witness.getDerivation();
    auto derivationSize = derivation.size();
    if (derivationSize == 0) { return Result::NOT_VALIDATED; }
    ChcDirectedHyperGraph::VertexInstances vertexInstances(graph);
    if (derivation[0].derivedFact != logic.getTerm_true()) {
        assert(false);
        return Result::NOT_VALIDATED;
    }
    for (std::size_t i = 1; i < derivationSize; ++i) {
        auto result = validateStep(i, derivation, graph, vertexInstances);
        if (result == Validator::Result::NOT_VALIDATED) { return result; }
    }
    return Validator::Result::VALIDATED;
}

