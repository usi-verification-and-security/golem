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
                if (loop.size() > 0) {
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
    std::vector<SymRef> vertices;
    assert(graph.getSource(loop[0]) == graph.getTarget(loop[loop.size()-1]));
    assert(loop.size() >= 2);
    for(int i = 0; i < loop.size(); i++){
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
    PTRef initialStates = [&]() -> PTRef {
        vec<PTRef> negatedLocations;
        negatedLocations.capacity(locationVars.size());
        for (auto && entry : locationVars) {
            negatedLocations.push(logic.mkNot(entry.second));
        }
        return logic.mkAnd(std::move(negatedLocations));
    }();


    for(auto edge: loop){
        graph.removeEdge(edge);
    }
//    PTRef badStates = locationVars.at(vertices[0]);

    allEdges = graph.getEdges();
    for(auto edge: allEdges){
        if (std::find(vertices.begin(), vertices.end(), graph.getSource(edge)) != vertices.end()){
            PTRef badStates = locationVars.at(graph.getSource(edge));
            graph.updateEdgeSource(edge, vertices[0]);
            graph.updateEdgeLabel(edge, InterpretedFla{logic.mkAnd(graph.getEdgeLabel(edge),badStates)});
        }
        if (std::find(vertices.begin(), vertices.end(), graph.getTarget(edge)) != vertices.end()){
            graph.updateEdgeTarget(edge, vertices[0]);
            PTRef arr = timeMachine.sendVarThroughTime(locationVars.at(graph.getTarget(edge)), 1);
            graph.updateEdgeLabel(edge, InterpretedFla{rewriteMaxArityClassic(logic,logic.mkAnd(logic.mkAnd(initialStates, graph.getEdgeLabel(edge)), arr))});
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
