/*
 * Copyright (c) 2020-2025, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef GOLEM_TRANSFORMATIONUTILS_H
#define GOLEM_TRANSFORMATIONUTILS_H

#include "TransitionSystem.h"
#include "Witnesses.h"
#include "graph/ChcGraph.h"

#include <memory>

namespace golem {
bool isTransitionSystem(ChcDirectedGraph const & graph);

bool isTransitionSystemWithoutQuery(ChcDirectedGraph const & graph);

bool isTransitionSystemDAG(ChcDirectedGraph const & graph);

bool isTrivial(ChcDirectedGraph const & graph);

std::unique_ptr<TransitionSystem> toTransitionSystem(ChcDirectedGraph const & graph, bool allowNoQuery = false);

std::unique_ptr<TransitionSystem> ensureNoAuxiliaryVariablesInInitAndQuery(std::unique_ptr<TransitionSystem> ts);

std::unique_ptr<TransitionSystem> ensureNoAuxiliaryVariablesInQuery(std::unique_ptr<TransitionSystem> ts);

struct EdgeVariables {
    std::vector<PTRef> stateVars;
    std::vector<PTRef> nextStateVars;
    std::vector<PTRef> auxiliaryVars;
};

EdgeVariables getVariablesFromEdge(Logic & logic, ChcDirectedGraph const & graph, EId eid);

std::unique_ptr<SystemType> systemTypeFrom(vec<PTRef> const & stateVars, vec<PTRef> const & auxVars, Logic & logic);

PTRef transitionFormulaInSystemType(SystemType const & systemType, EdgeVariables const & edgeVariables, PTRef edgeLabel,
                                    Logic & logic);

std::vector<EId> detectLoop(const ChcDirectedGraph & graph);
} // namespace golem

#endif // GOLEM_TRANSFORMATIONUTILS_H
