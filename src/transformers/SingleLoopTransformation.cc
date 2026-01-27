/*
 * Copyright (c) 2023-2025, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "SingleLoopTransformation.h"

#include "QuantifierElimination.h"
#include "TransformationUtils.h"
#include "utils/SmtSolver.h"

namespace golem {
SingleLoopTransformation::TransformationResult
SingleLoopTransformation::transform(const ChcDirectedGraph & graph) const {
    Logic & logic = graph.getLogic();
    TimeMachine timeMachine(logic);
    auto vertices = graph.getVertices();
    // MB: It is useful to have exit location, so we do not remove exit from the vertices
    std::erase(vertices, graph.getEntry());
    LocationVarMap locationVars;
    locationVars.reserve(vertices.size());
    for (auto vertex : vertices) {
        auto varName = std::string(".loc_") + std::to_string(vertex.x);
        locationVars.insert({vertex, timeMachine.getVarVersionZero(varName, logic.getSort_bool())});
    }

    PositionVarMap argVars;
    for (auto vertex : vertices) {
        auto args_count = logic.getSym(vertex).nargs();
        for (uint32_t i = 0; i < args_count; ++i) {
            VarPosition pos = {vertex, i};
            auto varName = std::string(".arg_") + std::to_string(vertex.x) + '_' + std::to_string(i);
            PTRef var = timeMachine.getVarVersionZero(varName, logic.getSym(vertex)[i]);
            argVars.insert({pos, var});
        }
    }

    EdgeTranslator edgeTranslator{graph, locationVars, argVars, {}};
    vec<PTRef> transitionRelationComponent;
    vec<PTRef> initialComponent;
    graph.forEachEdge([&](auto const & edge) {
        if (edge.from == graph.getEntry()) {
            initialComponent.push(edgeTranslator.translateEdge(edge));
        } else {
            transitionRelationComponent.push(edgeTranslator.translateEdge(edge));
        }
    });
    PTRef initialStates = logic.mkOr(std::move(initialComponent));

    PTRef transitionRelation = logic.mkOr(std::move(transitionRelationComponent));

    PTRef badStates = locationVars.at(graph.getExit());

    vec<PTRef> stateVars = [&locationVars, &argVars]() {
        vec<PTRef> ret;
        ret.capacity(locationVars.size() + argVars.size());
        for (auto && entry : locationVars) {
            ret.push(entry.second);
        }
        for (auto && entry : argVars) {
            ret.push(entry.second);
        }
        return ret;
    }();
    auto systemType = std::make_unique<SystemType>(stateVars, edgeTranslator.auxiliaryVariables, logic);
    auto ts =
        std::make_unique<TransitionSystem>(logic, std::move(systemType), initialStates, transitionRelation, badStates);
    auto backTranslator =
        std::make_unique<WitnessBackTranslator>(graph, *ts, std::move(locationVars), std::move(argVars));
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
    Logic & logic = graph.getLogic();
    TimeMachine tm(logic);
    SMTSolver solver(logic, SMTSolver::WitnessProduction::ONLY_MODEL);
    solver.assertProp(transitionSystem.getInit());
    PTRef transition = transitionSystem.getTransition();
    for (auto i = 0u; i < unrolling; ++i) {
        solver.assertProp(tm.sendFlaThroughTime(transition, i));
    }
    solver.assertProp(tm.sendFlaThroughTime(transitionSystem.getQuery(), unrolling));
    auto res = solver.check();
    assert(res == SMTSolver::Answer::SAT);
    if (res != SMTSolver::Answer::SAT) { throw std::logic_error("Unrolling should have been satisfiable"); }
    auto model = solver.getModel();
    std::vector<SymRef> pathVertices;
    pathVertices.push_back(graph.getEntry());
    auto allVertices = graph.getVertices();
    for (auto i = 0u; i <= unrolling; ++i) {
        auto it = std::find_if(allVertices.begin(), allVertices.end(), [&](auto vertex) {
            if (vertex == graph.getEntry()) { return false; }
            auto varName = ".loc_" + std::to_string(vertex.x);
            auto vertexVar = logic.mkBoolVar(varName.c_str());
            vertexVar = tm.getVarVersionZero(vertexVar);
            vertexVar = tm.sendVarThroughTime(vertexVar, i);
            return model->evaluate(vertexVar) == logic.getTerm_true();
        });
        assert(it != allVertices.end());
        pathVertices.push_back(*it);
    }

    // Build error path from the vertices
    std::vector<EId> errorEdges;
    auto adj = AdjacencyListsGraphRepresentation::from(graph);
    for (auto i = 1u; i < pathVertices.size(); ++i) {
        auto source = pathVertices[i - 1];
        auto target = pathVertices[i];
        auto const & outgoing = adj.getOutgoingEdgesFor(source);
        auto it =
            std::find_if(outgoing.begin(), outgoing.end(), [&](EId eid) { return target == graph.getTarget(eid); });
        assert(it != outgoing.end());
        errorEdges.push_back(*it);
        // TODO: deal with multiedges properly
        if (std::find_if(it + 1, outgoing.end(), [&](EId eid) { return target == graph.getTarget(eid); }) !=
            outgoing.end()) {
            // Bail out in this case
            return NoWitness{"Could not backtranslate invalidity witness in single-loop transformation"};
        }
    }
    ErrorPath errorPath;
    errorPath.setPath(std::move(errorEdges));
    return InvalidityWitness::fromErrorPath(errorPath, graph);
}

SingleLoopTransformation::WitnessBackTranslator::ErrorOr<ValidityWitness>
SingleLoopTransformation::WitnessBackTranslator::translateInvariant(PTRef inductiveInvariant) {
    Logic & logic = graph.getLogic();
    //    std::cout << "Invariant is " << logic.pp(inductiveInvariant) << std::endl;
    auto vertices = graph.getVertices();
    TermUtils utils(logic);
    TermUtils::substitutions_map substitutions;
    for (auto vertex : vertices) {
        if (vertex == graph.getEntry()) { continue; }
        PTRef locationVar = this->locationVarMap.at(vertex);
        substitutions.insert({locationVar, logic.getTerm_false()});
    }

    auto vertexInvariants = ValidityWitness::trivialDefinitions(graph);
    for (auto vertex : vertices) {
        if (vertex == graph.getEntry() or vertex == graph.getExit()) { continue; }
        PTRef locationVar = this->locationVarMap.at(vertex);
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
        PTRef basePredicate = TimeMachine(logic).versionedFormulaToUnversioned(graph.getStateVersion(vertex));
        auto argsNum = logic.getPterm(basePredicate).nargs();
        for (auto i = 0u; i < argsNum; ++i) {
            PTRef positionVar = positionVarMap.at(VarPosition{vertex, i});
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
    for (auto const & entry : positionVarMap) {
        if (entry.first.vertex == vertex) { vars.insert(entry.second); }
    }
    return vars;
}
} // namespace golem