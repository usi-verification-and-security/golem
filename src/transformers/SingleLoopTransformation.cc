/*
* Copyright (c) 2023, Martin Blicha <martin.blicha@gmail.com>
*
* SPDX-License-Identifier: MIT
*/

#include "SingleLoopTransformation.h"

#include "TransformationUtils.h"

namespace {
using LocationVarMap = SingleLoopTransformation::LocationVarMap;
using PositionVarMap = SingleLoopTransformation::PositionVarMap;
using VarPosition = SingleLoopTransformation::VarPosition;

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
        VarPosition varPosition {source, i};
        auto it = positionVarMap.find(varPosition);
        assert(it != positionVarMap.end());
        substitutionsMap.insert({stateVars[i], it->second});
    }

    auto const & nextStateVars = edgeVariables.nextStateVars;
    for (unsigned int i = 0; i < nextStateVars.size(); ++i) {
        VarPosition varPosition {target, i};
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
            if (entry.second != sourceLocationVar) {
                args.push(logic.mkNot(entry.second));
            }
        }
        return logic.mkAnd(std::move(args));
    }();
    PTRef frameEqualities = [&]() {
        vec<PTRef> equalities;
        for (auto && entry : positionVarMap) {
            if (entry.first.vertex == target) { continue; }
            PTRef var = timeMachine.sendVarThroughTime(entry.second, 1);
            equalities.push(logic.mkEq(var, logic.getDefaultValuePTRef(var)));
        }
        return logic.mkAnd(std::move(equalities));
    }();
    vec<PTRef> components {
        sourceLocationVar,
        translatedConstraint,
        timeMachine.sendVarThroughTime(targetLocationVar, 1),
        updatedLocation,
        frameEqualities
    };
    return logic.mkAnd(std::move(components));
}

}

SingleLoopTransformation::TransformationResult SingleLoopTransformation::transform(const ChcDirectedGraph & graph) {
    Logic & logic = graph.getLogic();
    TimeMachine timeMachine(logic);
    auto vertices = graph.getVertices();
    // MB: It is useful to have exit location, so we do not remove exit from the vertices
    vertices.erase(std::remove_if(vertices.begin(), vertices.end(), [&](auto vertex) {
                       return vertex == graph.getEntry();
                   }), vertices.end());
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
    graph.forEachEdge([&](auto const & edge) {
        transitionRelationComponent.push(edgeTranslator.translateEdge(edge));
    });

    PTRef transitionRelation = logic.mkOr(std::move(transitionRelationComponent));
    PTRef initialStates = [&]() -> PTRef {
        vec<PTRef> negatedLocations;
        negatedLocations.capacity(locationVars.size());
        for (auto && entry : locationVars) {
            negatedLocations.push(logic.mkNot(entry.second));
        }
        return logic.mkAnd(std::move(negatedLocations));
    }();

    PTRef badStates = locationVars.at(graph.getExit());

    vec<PTRef> stateVars = [&locationVars,&argVars]() {
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
    auto systemType = std::make_unique<SystemType>(stateVars, edgeTranslator.auxiliaryVariablesSeen, logic);
    auto ts = std::make_unique<TransitionSystem>(logic, std::move(systemType), initialStates, transitionRelation, badStates);
    auto backTraslator = std::make_unique<WitnessBackTranslator>(graph, *ts, std::move(locationVars), std::move(argVars));
    return {std::move(ts), std::move(backTraslator)};
}

// Witness backtranslation

VerificationResult SingleLoopTransformation::WitnessBackTranslator::translate(TransitionSystemVerificationResult result) {
    if (result.answer == VerificationAnswer::UNSAFE) {
        return {VerificationAnswer::UNSAFE, translateErrorPath(std::get<std::size_t>(result.witness))};
    }
    if (result.answer == VerificationAnswer::SAFE) {
        return {VerificationAnswer::SAFE, translateInvariant(std::get<PTRef>(result.witness))};
    }
    return VerificationResult(result.answer);
}

InvalidityWitness SingleLoopTransformation::WitnessBackTranslator::translateErrorPath(std::size_t unrolling) {
    // We need to get the CEX path, which will define the locations in the graph
    Logic & logic = graph.getLogic();
    TimeMachine tm(logic);
    SMTConfig config;
    MainSolver solver(logic, config, "CEX");
    solver.insertFormula(transitionSystem.getInit());
    PTRef transition = transitionSystem.getTransition();
    for (auto i = 0u; i < unrolling; ++i) {
        solver.insertFormula(tm.sendFlaThroughTime(transition, i));
    }
    solver.insertFormula(tm.sendFlaThroughTime(transitionSystem.getQuery(), unrolling));
    auto res = solver.check();
    assert(res == s_True);
    if (res != s_True) {
        throw std::logic_error("Unrolling should have been satisfiable");
    }
    auto model = solver.getModel();
    std::vector<SymRef> pathVertices;
    pathVertices.push_back(graph.getEntry());
    auto allVertices = graph.getVertices();
    for (auto i = 0u; i < unrolling; ++i) {
        auto it = std::find_if(allVertices.begin(), allVertices.end(), [&](auto vertex) {
            if (vertex == graph.getEntry()) { return false; }
            auto varName = ".loc_" + std::to_string(vertex.x);
            auto vertexVar = logic.mkBoolVar(varName.c_str());
            vertexVar = tm.getVarVersionZero(vertexVar);
            vertexVar = tm.sendVarThroughTime(vertexVar, i + 1);
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
        auto it = std::find_if(outgoing.begin(), outgoing.end(), [&](EId eid) {
            return target == graph.getTarget(eid);
        });
        assert(it != outgoing.end());
        errorEdges.push_back(*it);
        // TODO: deal with multiedges properly
        if (std::find_if(it + 1, outgoing.end(), [&](EId eid) {
                return target == graph.getTarget(eid);
            }) != outgoing.end()) {
            // Bail out in this case
            return {};
        }
    }
    ErrorPath errorPath;
    errorPath.setPath(std::move(errorEdges));
    return InvalidityWitness::fromErrorPath(errorPath, graph);
}

ValidityWitness SingleLoopTransformation::WitnessBackTranslator::translateInvariant(PTRef inductiveInvariant) {
    Logic & logic = graph.getLogic();
    //    std::cout << "Invariant is " << logic.pp(invariant) << std::endl;
    auto vertices = graph.getVertices();
    TermUtils utils(logic);
    TermUtils::substitutions_map substitutions;
    for (auto vertex : vertices) {
        if (vertex == graph.getEntry()) { continue; }
        PTRef locationVar = this->locationVarMap.at(vertex);
        substitutions.insert({locationVar, logic.getTerm_false()});
    }

    ValidityWitness::definitions_t vertexInvariants;
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
            // TODO: Improve the rewriting in OpenSMT. If child simplifies to atom, it can be used to simplify the remaining children
            while(logic.isBooleanOperator(vertexInvariant)) {
                PTRef before = vertexInvariant;
                vertexInvariant = ::simplifyUnderAssignment_Aggressive(vertexInvariant, logic);
                if (before == vertexInvariant) { break; }
            }
        }
        // Check if all variables are from the current vertex
        auto allVars = variables(logic, vertexInvariant);
        auto vertexVars = getVarsForVertex(vertex);
        bool hasAlienVariable = std::any_of(allVars.begin(), allVars.end(), [&](PTRef var) {
            return vertexVars.find(var) == vertexVars.end();
        });
        if (hasAlienVariable) { return ValidityWitness{}; } // TODO: Figure out a way to deal with this situation properly
        // No alien variable, we can translate the invariant using predicate's variables
        TermUtils::substitutions_map varSubstitutions;
        PTRef statePredicate = graph.getStateVersion(vertex);
        auto argsNum = logic.getPterm(statePredicate).nargs();
        for (auto i = 0u; i < argsNum; ++i) {
            PTRef positionVar = positionVarMap.at(VarPosition{vertex, i});
            varSubstitutions.insert({positionVar, logic.getPterm(statePredicate)[i]});
        }
        vertexInvariant = utils.varSubstitute(vertexInvariant, varSubstitutions);
        vertexInvariants.insert({statePredicate, vertexInvariant});
        //std::cout << logic.printSym(vertex) << " -> " << logic.pp(vertexInvariant) << std::endl;
    }
    return ValidityWitness(std::move(vertexInvariants));
}

std::set<PTRef> SingleLoopTransformation::WitnessBackTranslator::getVarsForVertex(SymRef vertex) const {
    std::set<PTRef> vars;
    for (auto const & entry : positionVarMap) {
        if (entry.first.vertex == vertex) {
            vars.insert(entry.second);
        }
    }
    return vars;
}
