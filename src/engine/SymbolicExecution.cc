/*
 * Copyright (c) 2025, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "SymbolicExecution.h"

#include "graph/ChcGraph.h"
#include "utils/SmtSolver.h"

namespace golem {

class DirectForwardSymbolicExecution {
public:
    explicit DirectForwardSymbolicExecution(std::unique_ptr<ChcDirectedGraph> graph) : graph(std::move(graph)) {}
    VerificationResult run();
private:
    std::unique_ptr<ChcDirectedGraph> graph;
};

VerificationResult DirectForwardSymbolicExecution::run() {
    enum class InsertionResult { NEW, DUPLICATE };
    using Entry = std::pair<SymRef, PTRef>;
    struct DiscoveredArgNodes {
        InsertionResult tryInsert(Entry const & entry) {
            return tryInsert(entry.first, entry.second);
        }
        InsertionResult tryInsert(SymRef node, PTRef state) {
            const auto [_, inserted] = nodes[node].insert(state);
            return inserted ? InsertionResult::NEW : InsertionResult::DUPLICATE;
        }
    private:
        std::unordered_map<SymRef, std::unordered_set<PTRef, PTRefHash>, SymRefHash> nodes;
    };
    using Queue = std::deque<Entry>;
    Queue q;
    DiscoveredArgNodes nodes;
    Logic & logic = graph->getLogic();
    AdjacencyListsGraphRepresentation ar = AdjacencyListsGraphRepresentation::from(*graph);
    TermUtils utils(logic);

    q.emplace_back(graph->getEntry(), logic.getTerm_true());
    nodes.tryInsert(q.back());
    while (not q.empty()) {
        auto [node, state] = q.front();
        q.pop_front();
        for (EId eid : ar.getOutgoingEdgesFor(node)) {
            auto target = graph->getTarget(eid);
            PTRef label = graph->getEdgeLabel(eid);
            if (target == graph->getExit()) {
                SMTSolver solver{logic, SMTSolver::WitnessProduction::NONE};
                solver.assertProp(state);
                solver.assertProp(label);
                auto res = solver.check();
                if (res == SMTSolver::Answer::SAT) { return VerificationResult{VerificationAnswer::UNSAFE}; }
                if (res != SMTSolver::Answer::UNSAT) { return VerificationResult{VerificationAnswer::UNKNOWN}; }
                continue;
            }
            PTRef rawState = utils.simplifyMax(logic.mkAnd(state, label));

            PTRef rawSimplified = TrivialQuantifierElimination(logic).tryEliminateVarsExcept(
                TermUtils(logic).predicateArgsInOrder(graph->getNextStateVersion(target)), rawState);
            PTRef newState = TimeMachine(logic).sendFlaThroughTime(rawSimplified, -1);
            Entry entry {target, newState};
            auto insertionResult = nodes.tryInsert(entry);
            switch (insertionResult) {
                case InsertionResult::NEW: {
                    // TODO: Lightweight feasibility check?
                    q.push_back(entry);
                    break;
                }
                case InsertionResult::DUPLICATE: {
                    // Already known state, ignore
                    break;
                }
            }
        }
    }
    return VerificationResult{VerificationAnswer::SAFE};
}


VerificationResult SymbolicExecution::solve(ChcDirectedHyperGraph const & graph) {
    if (graph.isNormalGraph()) {
        return DirectForwardSymbolicExecution(graph.toNormalGraph()).run();
    }
    return VerificationResult{VerificationAnswer::UNKNOWN};
}
} // namespace golem