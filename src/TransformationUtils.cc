//
// Created by Martin Blicha on 01.06.21.
//

#include "TransformationUtils.h"
#include "QuantifierElimination.h"

bool isTransitionSystem(ChcDirectedGraph const & graph) {
    auto graphRepresentation = AdjacencyListsGraphRepresentation::from(graph);
    auto reversePostorder = graphRepresentation.reversePostOrder();
    // TS has 3 vertices: Init, Body, Bad
    if (reversePostorder.size() != 3) { return false; }
    // TS has 3 edges: From Init to Body, self-loop on Body, from Body to Bad
    Vertex const & beg = graph.getVertex(reversePostorder[0]);
    Vertex const & loop = graph.getVertex(reversePostorder[1]);
    Vertex const & end = graph.getVertex(reversePostorder[2]);
    auto const & begOutEdges = graphRepresentation.getOutgoingEdgesFor(beg.id);
    if (begOutEdges.size() != 1 || graph.getTarget(begOutEdges[0]) != loop.id) { return false; }
    auto const & loopOutEdges = graphRepresentation.getOutgoingEdgesFor(loop.id);
    if (loopOutEdges.size() != 2) { return false; }
    bool selfLoop = std::find_if(loopOutEdges.begin(), loopOutEdges.end(),
                                 [&graph, loop](EId eid) { return graph.getTarget(eid) == loop.id; }) !=
                    loopOutEdges.end();
    if (not selfLoop) { return false; }
    bool edgeToEnd = std::find_if(loopOutEdges.begin(), loopOutEdges.end(),
                                  [&graph, end](EId eid) { return graph.getTarget(eid) == end.id; }) !=
                     loopOutEdges.end();
    if (not edgeToEnd) { return false; }
    if (not graphRepresentation.getOutgoingEdgesFor(end.id).empty()) { return false; }
    return true;
}

std::unique_ptr<TransitionSystem> toTransitionSystem(ChcDirectedGraph const & graph, Logic& logic) {
    auto adjacencyRepresentation = AdjacencyListsGraphRepresentation::from(graph);
    auto reversePostOrder = adjacencyRepresentation.reversePostOrder();
    assert(reversePostOrder.size() == 3);
    VId loopNode = reversePostOrder[1];
    auto const & outEdges = adjacencyRepresentation.getOutgoingEdgesFor(loopNode);
    auto it = std::find_if(outEdges.begin(), outEdges.end(), [&](EId eid) {
        return graph.getTarget(eid) == loopNode;
    });
    assert(it != outEdges.end());
    EId loopEdge = *it;
    auto edgeVars = getVariablesFromEdge(logic, graph, loopEdge);
    // Now we can continue building the transition system
    std::vector<SRef> stateVarTypes;
    std::transform(edgeVars.stateVars.begin(), edgeVars.stateVars.end(), std::back_inserter(stateVarTypes), [&logic](PTRef var){ return logic.getSortRef(var); });
    std::vector<SRef> auxVarTypes;
    std::transform(edgeVars.auxiliaryVars.begin(), edgeVars.auxiliaryVars.end(), std::back_inserter(auxVarTypes), [&logic](PTRef var){ return logic.getSortRef(var); });
    auto systemType = std::unique_ptr<SystemType>(new SystemType(std::move(stateVarTypes), std::move(auxVarTypes), logic));
    auto stateVars = systemType->getStateVars();
    auto nextStateVars = systemType->getNextStateVars();
    auto auxiliaryVars = systemType->getAuxiliaryVars();
    assert(stateVars.size() == edgeVars.stateVars.size_());
    assert(nextStateVars.size() == edgeVars.nextStateVars.size_());
    PTRef init = PTRef_Undef;
    PTRef transitionRelation = PTRef_Undef;
    PTRef bad = PTRef_Undef;
    for (auto const & edge : graph.getEdges()) {
        VId source = graph.getSource(edge);
        VId target = graph.getTarget(edge);
        bool isInit = source == reversePostOrder[0] && target == reversePostOrder[1];
        bool isLoop = source == reversePostOrder[1] && target == reversePostOrder[1];
        bool isEnd = source == reversePostOrder[1] && target == reversePostOrder[2];
        assert(isInit || isLoop || isEnd);
        PTRef fla = graph.getEdgeLabel(edge);
        TermUtils utils(logic);
        if (isInit) {
            std::unordered_map<PTRef, PTRef, PTRefHash> subMap;
            std::transform(edgeVars.nextStateVars.begin(), edgeVars.nextStateVars.end(), stateVars.begin(), std::inserter(subMap, subMap.end()),
                           [](PTRef key, PTRef value) { return std::make_pair(key, value); });
            init = utils.varSubstitute(fla, subMap);
            init = QuantifierElimination(logic).keepOnly(init, stateVars);
//            std::cout << logic.printTerm(init) << std::endl;
        }
        if (isLoop) {
            std::unordered_map<PTRef, PTRef, PTRefHash> subMap;
            std::transform(edgeVars.stateVars.begin(), edgeVars.stateVars.end(), stateVars.begin(), std::inserter(subMap, subMap.end()),
                           [](PTRef key, PTRef value) { return std::make_pair(key, value); });

            std::transform(edgeVars.nextStateVars.begin(), edgeVars.nextStateVars.end(), nextStateVars.begin(), std::inserter(subMap, subMap.end()),
                           [](PTRef key, PTRef value) { return std::make_pair(key, value); });

            std::transform(edgeVars.auxiliaryVars.begin(), edgeVars.auxiliaryVars.end(), auxiliaryVars.begin(), std::inserter(subMap, subMap.end()),
                           [](PTRef key, PTRef value) { return std::make_pair(key, value); });
            transitionRelation = utils.varSubstitute(fla, subMap);
//            std::cout << logic.printTerm(transitionRelation) << std::endl;
        }
        if (isEnd) {
            std::unordered_map<PTRef, PTRef, PTRefHash> subMap;
            std::transform(edgeVars.stateVars.begin(), edgeVars.stateVars.end(), stateVars.begin(), std::inserter(subMap, subMap.end()),
                           [](PTRef key, PTRef value) { return std::make_pair(key, value); });
            bad = utils.varSubstitute(fla, subMap);
            bad = QuantifierElimination(logic).keepOnly(bad, stateVars);
//            std::cout << logic.printTerm(bad) << std::endl;
        }
    }
    assert(init != PTRef_Undef && transitionRelation != PTRef_Undef && bad != PTRef_Undef);
    auto ts = std::unique_ptr<TransitionSystem>(new TransitionSystem(logic, std::move(systemType), init, transitionRelation, bad));
    return ts;
}

bool isTransitionSystemChain(ChcDirectedGraph const & graph) {
    if (graph.getVertices().size() < 3) { return false; }
    auto graphRepresentation = AdjacencyListsGraphRepresentation::from(graph);
    auto reversePostorder = graphRepresentation.reversePostOrder();
    assert(graph.getEntryId() == reversePostorder[0]);
    assert(graph.getExitId() == reversePostorder.back());
    if (graphRepresentation.getOutgoingEdgesFor(reversePostorder[0]).size() != 1
        or graphRepresentation.getIncomingEdgesFor(reversePostorder.back()).size() != 1) {
        return false;
    }
    for (unsigned i = 1; i < reversePostorder.size() - 1; ++i) {
        VId current = reversePostorder[i];
        auto const & outEdges = graphRepresentation.getOutgoingEdgesFor(current);
        if (outEdges.size() != 2) { return false; }
        bool hasSelfLoop = false;
        bool hasEdgeToNext = false;
        for (EId eid : outEdges) {
            hasSelfLoop |= graph.getTarget(eid) == current;
            hasEdgeToNext |= graph.getTarget(eid) == reversePostorder[i+1];
        }
        if (not (hasSelfLoop and hasEdgeToNext)) { return false; }
    }
    return true;
}

EdgeVariables getVariablesFromEdge(Logic & logic, ChcDirectedGraph const & graph, EId eid) {
    EdgeVariables res;
    TermUtils utils(logic);
    PTRef sourcePred = graph.getStateVersion(graph.getSource(eid));
    PTRef targetPred = graph.getNextStateVersion(graph.getTarget(eid));
    res.stateVars = utils.getVarsFromPredicateInOrder(sourcePred);
    res.nextStateVars = utils.getVarsFromPredicateInOrder(targetPred);
    PTRef edgeLabel = graph.getEdgeLabel(eid);
    auto allVars = TermUtils(logic).getVars(edgeLabel);
    for (PTRef var : allVars) {
        if (std::find(res.stateVars.begin(), res.stateVars.end(), var) == res.stateVars.end() and
            std::find(res.nextStateVars.begin(), res.nextStateVars.end(), var) == res.nextStateVars.end()) {
            res.auxiliaryVars.push(var);
        }
    }
    return res;
}

