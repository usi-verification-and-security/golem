/*
 * Copyright (c) 2024, Konstantin Britikov <britikovki@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "NestedLoopTransformation.h"

#include "QuantifierElimination.h"
#include "TransformationUtils.h"
#include "graph/ChcGraph.h"
#include "utils/SmtSolver.h"

namespace golem {
std::tuple<std::unique_ptr<ChcDirectedGraph>, std::unique_ptr<NestedLoopTransformation::WitnessBackTranslator>>
NestedLoopTransformation::transform(ChcDirectedGraph const & graph) {
    auto vertices = graph.getVertices();
    auto copyGraph = std::make_unique<ChcDirectedGraph>(graph);
    std::vector<EId> loop = detectLoop(*copyGraph);
    std::vector<WitnessInfo> loops;
    while (loop.size() > 1) {
        auto wtnsInfo = copyGraph->contractConnectedVertices(loop);
        loops.push_back(wtnsInfo);
        loop = detectLoop(*copyGraph);
    }
    return {std::move(copyGraph),
            std::make_unique<NestedLoopTransformation::WitnessBackTranslator>(graph, *copyGraph, loops)};
}

VerificationResult NestedLoopTransformation::WitnessBackTranslator::translate(VerificationResult & result) {
    if (result.getAnswer() == VerificationAnswer::UNSAFE) {
        auto witness = translateErrorPath(result.getInvalidityWitness());
        if (std::holds_alternative<NoWitness>(witness)) {
            return {result.getAnswer(), std::get<NoWitness>(std::move(witness))};
        }
        return {VerificationAnswer::UNSAFE, std::get<InvalidityWitness>(std::move(witness))};
    }
    if (result.getAnswer() == VerificationAnswer::SAFE) {
        auto witness = translateInvariant(result.getValidityWitness());
        if (std::holds_alternative<NoWitness>(witness)) {
            return {result.getAnswer(), std::get<NoWitness>(std::move(witness))};
        }
        return {VerificationAnswer::SAFE, std::get<ValidityWitness>(std::move(witness))};
    }
    return std::move(result);
}

NestedLoopTransformation::WitnessBackTranslator::ErrorOr<InvalidityWitness>
NestedLoopTransformation::WitnessBackTranslator::translateErrorPath(InvalidityWitness wtns) {
    // We need to get the CEX path, which will define the locations in the graph
    Logic & logic = initialGraph.getLogic();
    TimeMachine tm(logic);
    auto errorPath = wtns.getDerivation();
    std::vector<SymRef> pathVertices;
    pathVertices.push_back(initialGraph.getEntry());
    auto allVertices = initialGraph.getVertices();

    // Compute model for the error path
    auto model = [&]() {
        SMTSolver solverWrapper(logic, SMTSolver::WitnessProduction::ONLY_MODEL);
        for (std::size_t i = 1; i < errorPath.size(); ++i) {
            PTRef fla = graph.getEdgeLabel(errorPath[i].clauseId);
            fla = TimeMachine(logic).sendFlaThroughTime(fla, i);
            solverWrapper.assertProp(fla);
        }
        auto res = solverWrapper.check();
        if (res != SMTSolver::Answer::SAT) { throw std::logic_error("Error in computing model for the error path"); }
        return solverWrapper.getModel();
    }();

    for (std::size_t i = 1; i < errorPath.size(); ++i) {
        SymRef target = graph.getTarget(errorPath[i].clauseId);
        auto loopNode = std::find_if(loopContractionInfos.begin(), loopContractionInfos.end(),
                                     [&target](const WitnessInfo & x) { return x.loopVertex == target; });
        if (loopNode != loopContractionInfos.end()) {
            auto it = std::find_if(allVertices.begin(), allVertices.end(), [&](auto vertex) {
                if (loopNode->locations.find(vertex) == loopNode->locations.end()) { return false; }
                auto varName = ".loc_" + std::to_string(vertex.x);
                auto vertexVar = logic.mkBoolVar(varName.c_str());
                vertexVar = tm.getVarVersionZero(vertexVar);
                vertexVar = tm.sendVarThroughTime(vertexVar, i + 1);
                return model->evaluate(vertexVar) == logic.getTerm_true();
            });
            assert(it != allVertices.end());
            pathVertices.push_back(*it);
        } else {
            pathVertices.push_back(initialGraph.getTarget(errorPath[i].clauseId));
        };
    }

    // Build error path from the vertices
    std::vector<EId> errorEdges;
    auto adj = AdjacencyListsGraphRepresentation::from(initialGraph);
    for (std::size_t i = 1; i < pathVertices.size(); ++i) {
        auto source = pathVertices[i - 1];
        auto target = pathVertices[i];
        auto const & outgoing = adj.getOutgoingEdgesFor(source);
        auto it = std::find_if(outgoing.begin(), outgoing.end(),
                               [&](EId eid) { return target == initialGraph.getTarget(eid); });
        assert(it != outgoing.end());
        errorEdges.push_back(*it);
        // TODO: deal with multiedges properly
        if (std::find_if(it + 1, outgoing.end(), [&](EId eid) { return target == initialGraph.getTarget(eid); }) !=
            outgoing.end()) {
            // Bail out in this case
            return NoWitness{"Could not backtranslate invalidity witness in single-loop transformation"};
        }
    }
    ErrorPath ep;
    ep.setPath(std::move(errorEdges));
    return InvalidityWitness::fromErrorPath(ep, initialGraph);
}

NestedLoopTransformation::WitnessBackTranslator::ErrorOr<ValidityWitness>
NestedLoopTransformation::WitnessBackTranslator::translateInvariant(ValidityWitness wtns) {
    Logic & logic = initialGraph.getLogic();
    TimeMachine timeMachine(logic);
    auto oldVertices = initialGraph.getVertices();
    TermUtils utils(logic);
    TermUtils::substitutions_map substitutions;
    for (auto vertex : oldVertices) {
        if (vertex == graph.getEntry()) { continue; }
        for (auto loop : loopContractionInfos) {
            if (loop.locations.find(vertex) != loop.locations.end()) {
                substitutions.insert({timeMachine.getUnversioned(loop.locations.at(vertex)), logic.getTerm_false()});
                break;
            }
        }
    }

    ValidityWitness::definitions_t newDefinitions = wtns.getDefinitions();
    for (auto v : loopContractionInfos) {
        PTRef mergedInv = wtns.getDefinitions().at(v.loopVertex);
        newDefinitions.erase(v.loopVertex);
        for (auto vertex : oldVertices) {
            if (vertex == initialGraph.getEntry() or vertex == initialGraph.getExit()) { continue; }
            if (not v.locations.contains(vertex)) { continue; }
            PTRef locationVar = timeMachine.getUnversioned(v.locations.at(vertex));
            substitutions.at(locationVar) = logic.getTerm_true();
            auto vertexInvariant = utils.varSubstitute(mergedInv, substitutions);
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

            auto args_count = logic.getSym(vertex).nargs();
            std::unordered_set<PTRef, PTRefHash> changedVertexVars;
            for (uint32_t i = 0; i < args_count; i++) {
                changedVertexVars.insert(timeMachine.getUnversioned(v.positions.at(VarPosition{vertex, i})));
            }
            auto vertexVars = getVarsForVertex(v);
            bool hasAlienVariable = std::any_of(allVars.begin(), allVars.end(), [&](PTRef var) {
                return changedVertexVars.find(var) == changedVertexVars.end();
            });
            if (hasAlienVariable) {
                vec<PTRef> variablesToKeep;
                for (PTRef var : changedVertexVars) {
                    variablesToKeep.push(var);
                }
                // Universally quantify all alien variables. QE eliminates existential quantifiers, so use double
                // negation
                PTRef negatedInvariant = logic.mkNot(vertexInvariant);
                PTRef cleanNegatedInvariant = QuantifierElimination(logic).keepOnly(negatedInvariant, variablesToKeep);
                vertexInvariant = logic.mkNot(cleanNegatedInvariant);
            }
            // No alien variable, we can translate the invariant using predicate's variables
            TermUtils::substitutions_map varSubstitutions;
            PTRef basePredicate = TimeMachine(logic).versionedFormulaToUnversioned(graph.getStateVersion(vertex));
            auto argsNum = logic.getPterm(basePredicate).nargs();
            for (uint32_t i = 0u; i < argsNum; ++i) {
                PTRef positionVar = v.positions.at(VarPosition{vertex, i});
                varSubstitutions.insert({timeMachine.getUnversioned(positionVar), logic.getPterm(basePredicate)[i]});
            }
            vertexInvariant = utils.varSubstitute(vertexInvariant, varSubstitutions);
            assert(not newDefinitions.contains(vertex));
            newDefinitions.insert({vertex, vertexInvariant});
        }
    }
    return ValidityWitness(std::move(newDefinitions));
}

std::unordered_set<PTRef, PTRefHash>
NestedLoopTransformation::WitnessBackTranslator::getVarsForVertex(WitnessInfo wtns) const {
    std::unordered_set<PTRef, PTRefHash> vars;
    for (auto const & entry : wtns.positions) {
        vars.insert(entry.second);
    }
    return vars;
}
} // namespace golem