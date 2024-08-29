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

std::unique_ptr<NestedLoopTransformation::WitnessBackTranslator> NestedLoopTransformation::transform( ChcDirectedGraph & graph) {
    auto vertices = graph.getVertices();
    auto originalGraph = graph;
    std::vector<EId> loop = detectLoop(graph);
    std::vector<SymRef> simplifiedNodes;
    LocationVarMap locationVars;
    PositionVarMap argVars;
    while(loop.size()>1){
        simplifiedNodes.push_back(simplifyLoop(graph, loop, locationVars, argVars));
        loop = detectLoop(graph);
    }
//    auto backTranslator =
//        std::make_unique<WitnessBackTranslator>(originalGraph, graph, std::move(locationVars), std::move(argVars), simplifiedNodes);
    return std::make_unique<NestedLoopTransformation::WitnessBackTranslator>(std::move(originalGraph), graph, std::move(locationVars), std::move(argVars), simplifiedNodes);
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

SymRef NestedLoopTransformation::simplifyLoop( ChcDirectedGraph & graph, std::vector<EId> loop, LocationVarMap& locationVars, PositionVarMap& argVars) {
    Logic & logic = graph.getLogic();
    TimeMachine timeMachine(logic);
    TermUtils utils(logic);
    std::vector<SymRef> vertices;
    assert(graph.getSource(loop[0]) == graph.getTarget(loop[loop.size()-1]));
    assert(loop.size() >= 2);
    for(int i = loop.size() - 1; i >= 0; i--){
         vertices.push_back(graph.getSource(loop[i]));
    }
    // KB: Translation of vertices' self-loops of loop in DAG
    std::vector<EId> allEdges = graph.getEdges();

    locationVars.reserve(vertices.size());
    for (auto vertex : vertices) {
        auto varName = std::string(".loc_") + std::to_string(vertex.x);
        locationVars.insert({vertex, timeMachine.getVarVersionZero(varName, logic.getSort_bool())});
    }

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
    vec<SRef> args;
    for(auto arg: stateVars){
        args.push(logic.getSortRef(arg));
    }

    PTRef transitionRelation = logic.mkOr(std::move(transitionRelationComponent));

    SymRef newRef =  logic.declareFun("hello", logic.getSort_bool(), args);
    std::vector<PTRef> vars;
    for (PTRef var : stateVars) {
        vars.push_back(timeMachine.getUnversioned(var));
    }

    graph.getPredicateRepresentation().addRepresentation(newRef, std::move(vars));


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
            std::unordered_map<PTRef, PTRef, PTRefHash> subMap;
            for(uint i = 0; i < oldEdgeVars.stateVars.size(); i++){
                subMap.insert(std::make_pair(oldEdgeVars.stateVars[i], argVars[{graph.getSource(edge), i}]));
                conds = logic.mkAnd(conds, logic.mkEq(oldEdgeVars.stateVars[i], argVars[{graph.getSource(edge), i}]));
                //                argVars[{graph.getTarget(edge), i}];
            }
            graph.updateEdgeSource(edge, newRef);
            auto newEdgeVars = getVariablesFromEdge(logic, graph, edge);
            PTRef label = utils.varSubstitute(logic.mkAnd(graph.getEdgeLabel(edge), badStates), subMap);
            std::transform(oldEdgeVars.stateVars.begin(), oldEdgeVars.stateVars.end(), newEdgeVars.stateVars.begin(),
                           std::inserter(subMap, subMap.end()),
                           [](PTRef key, PTRef value) { return std::make_pair(key, value); });
            label = utils.varSubstitute(label, subMap);

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
            std::unordered_map<PTRef, PTRef, PTRefHash> subMap;
            for(uint i = 0; i < oldEdgeVars.nextStateVars.size(); i++){
                subMap.insert(std::make_pair(oldEdgeVars.nextStateVars[i], timeMachine.sendVarThroughTime(argVars[{graph.getTarget(edge), i}],1)));
                conds = logic.mkAnd(conds, logic.mkEq(oldEdgeVars.nextStateVars[i], timeMachine.sendVarThroughTime(argVars[{graph.getTarget(edge), i}],1)));
//                argVars[{graph.getTarget(edge), i}];
            }
            graph.updateEdgeTarget(edge, newRef);
            auto newEdgeVars = getVariablesFromEdge(logic, graph, edge);
            PTRef label = utils.varSubstitute(graph.getEdgeLabel(edge), subMap);
            std::transform(oldEdgeVars.nextStateVars.begin(), oldEdgeVars.nextStateVars.end(), newEdgeVars.nextStateVars.begin(),
                           std::inserter(subMap, subMap.end()),
                           [](PTRef key, PTRef value) { return std::make_pair(key, value); });

            label = utils.varSubstitute(graph.getEdgeLabel(edge), subMap);
            graph.updateEdgeLabel(edge, InterpretedFla{rewriteMaxArityClassic(logic,logic.mkAnd(logic.mkAnd(initialStates, label), arr))});
        }
    }

    graph.newEdge(newRef, newRef,InterpretedFla{transitionRelation});
    return newRef;
}





VerificationResult
NestedLoopTransformation::WitnessBackTranslator::translate(VerificationResult & result) {
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
    Logic & logic = graph.getLogic();
    TimeMachine tm(logic);
    auto errorPath = wtns.getDerivation();
    std::vector<SymRef> pathVertices;
    pathVertices.push_back(initialGraph.getEntry());
    auto newVertices = graph.getVertices();
    auto allVertices = initialGraph.getVertices();

    // Compute model for the error path
    auto model = [&]() {
        SMTSolver solverWrapper(logic, SMTSolver::WitnessProduction::ONLY_MODEL);
        auto & solver = solverWrapper.getCoreSolver();
        for (std::size_t i = 1; i < errorPath.size(); ++i) {
            PTRef fla = graph.getEdgeLabel(errorPath[i].clauseId);
            fla = TimeMachine(logic).sendFlaThroughTime(fla, i);
            solver.insertFormula(fla);
        }
        auto res = solver.check();
        if (res != s_True) { throw std::logic_error("Error in computing model for the error path"); }
        return solver.getModel();
    }();

    for (std::size_t i = 1; i < errorPath.size(); ++i) {
        if(graph.getTarget(errorPath[i].clauseId) == graph.getSource(errorPath[i].clauseId)){
            if (std::find(loopNodes.begin(), loopNodes.end(), graph.getTarget(errorPath[i].clauseId)) != loopNodes.end()) {
                auto it = std::find_if(allVertices.begin(), allVertices.end(), [&](auto vertex) {
                    if(locationVarMap.find(vertex) == locationVarMap.end()){
                        return false;
                    }
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
        } else {
            pathVertices.push_back(initialGraph.getTarget(errorPath[i].clauseId));
        }

    }

    // Build error path from the vertices
    std::vector<EId> errorEdges;
    auto adj = AdjacencyListsGraphRepresentation::from(initialGraph);
    for (auto i = 1; i < pathVertices.size(); ++i) {
        auto source = pathVertices[i - 1];
        auto target = pathVertices[i];
        auto const & outgoing = adj.getOutgoingEdgesFor(source);
        auto it =
            std::find_if(outgoing.begin(), outgoing.end(), [&](EId eid) { return target == initialGraph.getTarget(eid); });
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
    Logic & logic = graph.getLogic();
    TimeMachine timeMachine(logic);
    //    std::cout << "Invariant is " << logic.pp(inductiveInvariant) << std::endl;
    auto vertices = graph.getVertices();
    auto oldVertices = initialGraph.getVertices();
    TermUtils utils(logic);
    TermUtils::substitutions_map substitutions;
    for (auto vertex : oldVertices) {
        if (vertex == graph.getEntry()) { continue; }
        try {
            PTRef locationVar = this->locationVarMap.at(vertex);
            substitutions.insert({timeMachine.getUnversioned(locationVar), logic.getTerm_false()});
        } catch (const std::out_of_range& ex) {
            continue ;
        }
    }

    ValidityWitness::definitions_t vertexInvariants;
    for(auto inv:
         wtns.getDefinitions()) {
        vertexInvariants.insert(inv);
    }
    auto edges = graph.getEdges();
    for(auto v: loopNodes) {
//        vec<PTRef> unversionedVars;
//        for (std::size_t i = 0; i < edges.size(); ++i) {
//            if(graph.getTarget(edges[i]) == v && graph.getSource(edges[i]) == v){
//                auto vars = getVariablesFromEdge(logic,graph,edges[i]);
//                for(auto var: vars.stateVars){
//                    unversionedVars.push(timeMachine.getUnversioned(var));
//                }
//            }
//        }
//        PTRef unversionedPredicate = logic.mkUninterpFun(v, std::move(unversionedVars));

        PTRef unversionedPredicate = TimeMachine(logic).versionZeroToUnversioned(graph.getStateVersion(v));
        PTRef mergedInv = wtns.getDefinitions().at(unversionedPredicate);
        for (auto vertex : oldVertices) {
            if (vertex == initialGraph.getEntry() or vertex == initialGraph.getExit()) { continue; }
            PTRef locationVar ;
            try {
                locationVar = timeMachine.getUnversioned(this->locationVarMap.at(vertex));
            } catch (const std::out_of_range& ex) {
                continue;
            }
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
            for(uint32_t i = 0; i < args_count; i++){
                changedVertexVars.insert(timeMachine.getUnversioned(positionVarMap.at(VarPosition{vertex, i})));
            }
            auto vertexVars = getVarsForVertex(vertex);
            bool hasAlienVariable = std::any_of(allVars.begin(), allVars.end(),
                                                [&](PTRef var) { return changedVertexVars.find(var) == changedVertexVars.end(); });
            if (hasAlienVariable) {
                vec<PTRef> variablesToKeep;
                for (PTRef var : changedVertexVars) {
                    variablesToKeep.push(var);
                }
                // Universally quantify all alien variables. QE eliminates existential quantifiers, so use double negation
                PTRef negatedInvariant = logic.mkNot(vertexInvariant);
                PTRef cleanNegatedInvariant = QuantifierElimination(logic).keepOnly(negatedInvariant, variablesToKeep);
                vertexInvariant = logic.mkNot(cleanNegatedInvariant);
            }
            // No alien variable, we can translate the invariant using predicate's variables
            TermUtils::substitutions_map varSubstitutions;
            PTRef basePredicate = TimeMachine(logic).versionZeroToUnversioned(graph.getStateVersion(vertex));
            auto argsNum = logic.getPterm(basePredicate).nargs();
            for (auto i = 0u; i < argsNum; ++i) {
                PTRef positionVar = positionVarMap.at(VarPosition{vertex, i});
                varSubstitutions.insert({timeMachine.getUnversioned(positionVar), logic.getPterm(basePredicate)[i]});
            }
            vertexInvariant = utils.varSubstitute(vertexInvariant, varSubstitutions);
            if(vertexInvariants.find(basePredicate) != vertexInvariants.end()){
                vertexInvariants[basePredicate] = vertexInvariant;
            } else {
                vertexInvariants.insert({basePredicate, vertexInvariant});
            }
            // std::cout << logic.printSym(vertex) << " -> " << logic.pp(vertexInvariant) << std::endl;
        }
    }
    return ValidityWitness(std::move(vertexInvariants));
}

std::unordered_set<PTRef, PTRefHash>
NestedLoopTransformation::WitnessBackTranslator::getVarsForVertex(SymRef vertex) const {
    std::unordered_set<PTRef, PTRefHash> vars;
    for (auto const & entry : positionVarMap) {
        if (entry.first.vertex == vertex) { vars.insert(entry.second); }
    }
    return vars;
}
