/*
 * Copyright (c) 2024, Konstantin Britikov <britikovki@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */
#ifndef GOLEM_LOOPTRANSFORMATION_H
#define GOLEM_LOOPTRANSFORMATION_H


#include "TransitionSystem.h"
#include "TransformationUtils.h"
#include "Witnesses.h"
#include "graph/ChcGraph.h"

struct VarPosition {
    SymRef vertex;
    uint32_t pos;

    inline bool operator==(VarPosition other) const { return vertex == other.vertex and pos == other.pos; }
};
struct VarPositionHasher {
    std::size_t operator()(VarPosition pos) const {
        std::hash<std::uint32_t> hasher;
        return hasher(pos.vertex.x) ^ hasher(pos.pos);
    }
};

using LocationVarMap = std::unordered_map<SymRef, PTRef, SymRefHash>;
using PositionVarMap = std::unordered_map<VarPosition, PTRef, VarPositionHasher>;

namespace {
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
}
#endif // GOLEM_LOOPTRANSFORMATION_H
