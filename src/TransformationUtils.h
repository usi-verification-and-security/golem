//
// Created by Martin Blicha on 10.08.20.
//

#ifndef OPENSMT_TRANSFORMATIONUTILS_H
#define OPENSMT_TRANSFORMATIONUTILS_H

#include "TransitionSystem.h"
#include "graph/ChcGraph.h"

#include <memory>

bool isTransitionSystem(ChcDirectedGraph const & graph);

bool isTransitionSystemDAG(ChcDirectedGraph const & graph);

std::unique_ptr<TransitionSystem> toTransitionSystem(ChcDirectedGraph const & graph, Logic & logic);

struct EdgeVariables {
    std::vector<PTRef> stateVars;
    std::vector<PTRef> nextStateVars;
    std::vector<PTRef> auxiliaryVars;
};

EdgeVariables getVariablesFromEdge(Logic & logic, ChcDirectedGraph const & graph, EId eid);

std::unique_ptr<SystemType> systemTypeFrom(vec<PTRef> const & stateVars, vec<PTRef> const & auxVars, Logic & logic);

PTRef transitionFormulaInSystemType(SystemType const & systemType, EdgeVariables const & edgeVariables, PTRef edgeLabel,
                                    Logic & logic);

#endif // OPENSMT_TRANSFORMATIONUTILS_H
