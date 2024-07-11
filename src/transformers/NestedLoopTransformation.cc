/*
 * Copyright (c) 2023, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "NestedLoopTransformation.h"

#include "QuantifierElimination.h"
#include "TransformationUtils.h"
#include "utils/SmtSolver.h"
#include "graph/ChcGraph.h"

namespace {
using LocationVarMap = NestedLoopTransformation::LocationVarMap;
using PositionVarMap = NestedLoopTransformation::PositionVarMap;
using VarPosition = NestedLoopTransformation::VarPosition;

struct EdgeTranslator {
    ChcDirectedGraph const & graph;
    LocationVarMap const & locationVarMap;
    PositionVarMap const & positionVarMap;

    mutable vec<PTRef> auxiliaryVariablesSeen;

    PTRef translateEdge(DirectedEdge const & edge) const;
};

PTRef EdgeTranslator::translateEdge(DirectedEdge const & edge) const {
    TermUtils::substitutions_map substitutionsMap;
    Logic & logic = graph.getLogic();
    auto source = edge.from;
    auto target = edge.to;
    TimeMachine timeMachine(logic);

    auto edgeVariables = getVariablesFromEdge(logic, graph, edge.id);
    for (PTRef auxVar : edgeVariables.auxiliaryVars) {
        this->auxiliaryVariablesSeen.push(auxVar);
    }

    // TODO: prepare the substitution map in advance!
    auto const & stateVars = edgeVariables.stateVars;
    for (unsigned int i = 0; i < stateVars.size(); ++i) {
        VarPosition varPosition{source, i};
        auto it = positionVarMap.find(varPosition);
        assert(it != positionVarMap.end());
        substitutionsMap.insert({stateVars[i], it->second});
    }

    auto const & nextStateVars = edgeVariables.nextStateVars;
    for (unsigned int i = 0; i < nextStateVars.size(); ++i) {
        VarPosition varPosition{target, i};
        auto it = positionVarMap.find(varPosition);
        assert(it != positionVarMap.end());
        substitutionsMap.insert({nextStateVars[i], timeMachine.sendVarThroughTime(it->second, 1)});
    }

    // Translate the constraint
    PTRef translatedConstraint = TermUtils(logic).varSubstitute(edge.fla.fla, substitutionsMap);
    PTRef sourceLocationVar = source == graph.getEntry() ? logic.getTerm_true() : locationVarMap.at(source);
    PTRef targetLocationVar = locationVarMap.at(target);
    PTRef updatedLocation = [&]() {
        vec<PTRef> args;
        args.capacity(locationVarMap.size() * 2);
        for (auto && entry : locationVarMap) {
            if (entry.second != targetLocationVar) {
                args.push(logic.mkNot(timeMachine.sendVarThroughTime(entry.second, 1)));
            }
            if (entry.second != sourceLocationVar) { args.push(logic.mkNot(entry.second)); }
        }
        return logic.mkAnd(std::move(args));
    }();
    // We used to add equalities that restricted the values of all variables other than target ones to their default
    // values. The paper uses frame equalities that keep the values from previous step. Now, we do not restrict
    // the values of these variables in any way.
    // This is sound because we still force the right variables to be considered using the location variables.
    vec<PTRef> components{sourceLocationVar, translatedConstraint, timeMachine.sendVarThroughTime(targetLocationVar, 1),
                          updatedLocation};
    return logic.mkAnd(std::move(components));
}

} // namespace

void NestedLoopTransformation::transform( ChcDirectedGraph & graph) {
    auto vertices = graph.getVertices();
    std::vector<EId> loop = detectLoop(graph);
    while(loop.size()>1){
        simplifyLoop(graph, loop);
        loop = detectLoop(graph);
    }
}


void strongConnection(std::unordered_set<int> & visitedVertices, std::unordered_set<int> & verticesOnStack,
                      AdjacencyListsGraphRepresentation const & graphRepresentation, ChcDirectedGraph const & graph,
                      SymRef node, std::vector<EId>& loop) {
    visitedVertices.insert(node.x);
    verticesOnStack.insert(node.x);
    auto const & outEdges = graphRepresentation.getOutgoingEdgesFor(node);
    if (size(outEdges) <= 1) {
        verticesOnStack.erase(node.x);
        return;
    }

    for (EId eid : outEdges) {
        if (graph.getTarget(eid) != node) {
            auto nextVertex = graph.getTarget(eid);
            if (visitedVertices.find(nextVertex.x) == visitedVertices.end()) {
                strongConnection(visitedVertices, verticesOnStack, graphRepresentation, graph, nextVertex, loop);
                if (loop.size() > 0 && graph.getTarget(eid) != graph.getTarget(loop[0]) && graph.getTarget(eid) == graph.getSource(loop[loop.size()-1])) {
                    loop.push_back(eid);
                    return;
                }
            } else if (verticesOnStack.find(nextVertex.x) != verticesOnStack.end()) {
                loop.push_back(eid);
                return;
            }
        }
    }

    verticesOnStack.erase(node.x);

    return;
}

std::vector<EId> NestedLoopTransformation::detectLoop(const ChcDirectedGraph & graph) {
    std::vector<EId> loop;
    if (graph.getVertices().size() < 3) { return loop; }
    auto graphRepresentation = AdjacencyListsGraphRepresentation::from(graph);
    auto vertices = reversePostOrder(graph, graphRepresentation);
    std::unordered_set<int> visitedVertices;
    std::unordered_set<int> verticesOnStack;
    for (uint i = 1; i < vertices.size() - 1; i++) {
        if (visitedVertices.find(vertices[i].x) == visitedVertices.end()) {
            strongConnection(visitedVertices, verticesOnStack, graphRepresentation, graph, vertices[i], loop);
        }
    }
    return loop;
}

void NestedLoopTransformation::simplifyLoop( ChcDirectedGraph & graph, std::vector<EId> loop) {
    Logic & logic = graph.getLogic();
    TimeMachine timeMachine(logic);
    TermUtils utils(logic);
    std::vector<SymRef> vertices;
    assert(graph.getSource(loop[0]) == graph.getTarget(loop[loop.size()-1]));
    assert(loop.size() >= 2);
    for(int i = loop.size() - 1; i >= 0; i--){
         vertices.push_back(graph.getSource(loop[i]));
    }

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

    // KB: Translation of edges between vertices of loop in DAG
    EdgeTranslator edgeTranslator{graph, locationVars, argVars, {}};
    vec<PTRef> transitionRelationComponent;
    for(auto edge: loop) {
        transitionRelationComponent.push(edgeTranslator.translateEdge(graph.getEdge(edge)));

    }


    // KB: Translation of vertices' self-loops of loop in DAG
    std::vector<EId> allEdges = graph.getEdges();
    for(auto edge: allEdges) {
        if(graph.getTarget(edge) == graph.getSource(edge)){
            for(auto check: loop){
                if(graph.getSource(check) == graph.getSource(edge)){
                    transitionRelationComponent.push(edgeTranslator.translateEdge(graph.getEdge(edge)));
                    graph.removeEdge(edge);
                    break;
                }

            }
        }
    };

    PTRef transitionRelation = logic.mkOr(std::move(transitionRelationComponent));



    for(auto edge: loop){
        graph.removeEdge(edge);
    }
//    PTRef badStates = locationVars.at(vertices[0]);
//TODO: we're not guaranteed that old and new predicate will have the same number of vars
    allEdges = graph.getEdges();
    for(auto edge: allEdges){
        if (std::find(vertices.begin(), vertices.end(), graph.getSource(edge)) != vertices.end()){
            PTRef badStates = locationVars.at(graph.getSource(edge));
            auto oldEdgeVars = getVariablesFromEdge(logic, graph, edge);
            PTRef conds = logic.getTerm_true();
            for(uint i = 0; i < oldEdgeVars.stateVars.size(); i++){
                conds = logic.mkAnd(conds, logic.mkEq(oldEdgeVars.stateVars[i], argVars[{graph.getSource(edge), i}]));
                //                argVars[{graph.getTarget(edge), i}];
            }
            graph.updateEdgeSource(edge, vertices[0]);
            auto newEdgeVars = getVariablesFromEdge(logic, graph, edge);

            std::unordered_map<PTRef, PTRef, PTRefHash> subMap;
            std::transform(oldEdgeVars.stateVars.begin(), oldEdgeVars.stateVars.end(), newEdgeVars.stateVars.begin(),
                           std::inserter(subMap, subMap.end()),
                           [](PTRef key, PTRef value) { return std::make_pair(key, value); });
            PTRef label = utils.varSubstitute(logic.mkAnd(graph.getEdgeLabel(edge), logic.mkAnd(badStates, conds)), subMap);

            graph.updateEdgeLabel(edge, InterpretedFla{label});
        }
        if (std::find(vertices.begin(), vertices.end(), graph.getTarget(edge)) != vertices.end()){

            PTRef initialStates = [&]() -> PTRef {
                vec<PTRef> negatedLocations;
                negatedLocations.capacity(locationVars.size());
                for (auto && entry : locationVars) {
                    if(std::get<0>(entry) != graph.getTarget(edge)) {
                        negatedLocations.push(logic.mkNot(timeMachine.sendVarThroughTime(entry.second, 1)));
                    }
                }
                return logic.mkAnd(std::move(negatedLocations));
            }();

            auto oldEdgeVars = getVariablesFromEdge(logic, graph, edge);
            PTRef arr = timeMachine.sendVarThroughTime(locationVars.at(graph.getTarget(edge)), 1);
            PTRef conds = logic.getTerm_true();
            for(uint i = 0; i < oldEdgeVars.nextStateVars.size(); i++){
                conds = logic.mkAnd(conds, logic.mkEq(oldEdgeVars.nextStateVars[i], timeMachine.sendVarThroughTime(argVars[{graph.getTarget(edge), i}],1)));
//                argVars[{graph.getTarget(edge), i}];
            }
            graph.updateEdgeTarget(edge, vertices[0]);
            auto newEdgeVars = getVariablesFromEdge(logic, graph, edge);
            std::unordered_map<PTRef, PTRef, PTRefHash> subMap;
            std::transform(oldEdgeVars.nextStateVars.begin(), oldEdgeVars.nextStateVars.end(), newEdgeVars.nextStateVars.begin(),
                           std::inserter(subMap, subMap.end()),
                           [](PTRef key, PTRef value) { return std::make_pair(key, value); });

            PTRef label = utils.varSubstitute(graph.getEdgeLabel(edge), subMap);
            graph.updateEdgeLabel(edge, InterpretedFla{rewriteMaxArityClassic(logic,logic.mkAnd(logic.mkAnd(initialStates, label), logic.mkAnd(arr, conds)))});
        }
    }

    std::vector<PTRef> stateVars = [&locationVars, &argVars]() {
        std::vector<PTRef> ret;
        for (auto && entry : locationVars) {
            ret.push_back(entry.second);
        }
        for (auto && entry : argVars) {
            ret.push_back(entry.second);
        }
        return ret;
    }();

    graph.newEdge(vertices[0], vertices[0],InterpretedFla{transitionRelation});
    graph.addAuxVars(vertices[0], stateVars);
}





VerificationResult
NestedLoopTransformation::WitnessBackTranslator::translate(TransitionSystemVerificationResult result) {
//    if (result.answer == VerificationAnswer::UNSAFE) {
//        auto witness = translateErrorPath(std::get<std::size_t>(result.witness));
//        if (std::holds_alternative<NoWitness>(witness)) {
//            return {result.answer, std::get<NoWitness>(std::move(witness))};
//        }
//        return {VerificationAnswer::UNSAFE, std::get<InvalidityWitness>(std::move(witness))};
//    }
//    if (result.answer == VerificationAnswer::SAFE) {
//        auto witness = translateInvariant(std::get<PTRef>(result.witness));
//        if (std::holds_alternative<NoWitness>(witness)) {
//            return {result.answer, std::get<NoWitness>(std::move(witness))};
//        }
//        return {VerificationAnswer::SAFE, std::get<ValidityWitness>(std::move(witness))};
//    }
    return VerificationResult(result.answer);
}


//SingleLoopTransformation::WitnessBackTranslator::ErrorOr<InvalidityWitness>
//SingleLoopTransformation::WitnessBackTranslator::translateErrorPath(std::size_t unrolling) {
//    // We need to get the CEX path, which will define the locations in the graph
//    Logic & logic = graph.getLogic();
//    TimeMachine tm(logic);
//    SMTSolver solverWrapper(logic, SMTSolver::WitnessProduction::ONLY_MODEL);
//    auto & solver = solverWrapper.getCoreSolver();
//    solver.insertFormula(transitionSystem.getInit());
//    PTRef transition = transitionSystem.getTransition();
//    for (auto i = 0u; i < unrolling; ++i) {
//        solver.insertFormula(tm.sendFlaThroughTime(transition, i));
//    }
//    solver.insertFormula(tm.sendFlaThroughTime(transitionSystem.getQuery(), unrolling));
//    auto res = solver.check();
//    assert(res == s_True);
//    if (res != s_True) { throw std::logic_error("Unrolling should have been satisfiable"); }
//    auto model = solver.getModel();
//    std::vector<SymRef> pathVertices;
//    pathVertices.push_back(graph.getEntry());
//    auto allVertices = graph.getVertices();
//    for (auto i = 0u; i < unrolling; ++i) {
//        auto it = std::find_if(allVertices.begin(), allVertices.end(), [&](auto vertex) {
//            if (vertex == graph.getEntry()) { return false; }
//            auto varName = ".loc_" + std::to_string(vertex.x);
//            auto vertexVar = logic.mkBoolVar(varName.c_str());
//            vertexVar = tm.getVarVersionZero(vertexVar);
//            vertexVar = tm.sendVarThroughTime(vertexVar, i + 1);
//            return model->evaluate(vertexVar) == logic.getTerm_true();
//        });
//        assert(it != allVertices.end());
//        pathVertices.push_back(*it);
//    }
//
//    // Build error path from the vertices
//    std::vector<EId> errorEdges;
//    auto adj = AdjacencyListsGraphRepresentation::from(graph);
//    for (auto i = 1u; i < pathVertices.size(); ++i) {
//        auto source = pathVertices[i - 1];
//        auto target = pathVertices[i];
//        auto const & outgoing = adj.getOutgoingEdgesFor(source);
//        auto it =
//            std::find_if(outgoing.begin(), outgoing.end(), [&](EId eid) { return target == graph.getTarget(eid); });
//        assert(it != outgoing.end());
//        errorEdges.push_back(*it);
//        // TODO: deal with multiedges properly
//        if (std::find_if(it + 1, outgoing.end(), [&](EId eid) { return target == graph.getTarget(eid); }) !=
//            outgoing.end()) {
//            // Bail out in this case
//            return NoWitness{"Could not backtranslate invalidity witness in single-loop transformation"};
//        }
//    }
//    ErrorPath errorPath;
//    errorPath.setPath(std::move(errorEdges));
//    return InvalidityWitness::fromErrorPath(errorPath, graph);
//}