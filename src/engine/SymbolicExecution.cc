/*
 * Copyright (c) 2025, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "SymbolicExecution.h"

#include "graph/ChcGraph.h"
#include "utils/SmtSolver.h"

#include <algorithm>

namespace golem {

namespace {

struct State {
    using id_t = std::size_t;
    SymRef node;
    PTRef state;
    id_t id;
};

struct Predecessors {
    std::vector<State> states;
    std::unordered_map<State::id_t, std::pair<State::id_t, EId>> predecessors;

    void add(State const & successor, State::id_t predecessorId, EId edge) {
        assert(successor.id == states.size());
        states.push_back(successor);
        assert(not predecessors.contains(successor.id));
        predecessors.insert({successor.id, {predecessorId, edge}});
    }
};

class DirectForwardSymbolicExecution {
public:
    explicit DirectForwardSymbolicExecution(std::unique_ptr<ChcDirectedGraph> graph, Options const & options)
    : graph(std::move(graph)), options(options) {}
    VerificationResult run();
private:
    [[nodiscard]] bool computeWitness() const { return options.getOrDefault(Options::COMPUTE_WITNESS, "false") == "true"; }

    [[nodiscard]] InvalidityWitness getInvalidityWitness(EId errorEid, State::id_t errorPredecessorId, Predecessors const & predecessors) const;

    std::unique_ptr<ChcDirectedGraph> graph;
    Options const & options;
};

InvalidityWitness DirectForwardSymbolicExecution::getInvalidityWitness(EId errorEid, State::id_t errorPredecessorId, Predecessors const & predecessors) const {
    std::vector<EId> errorPath {errorEid};
    State::id_t currentId = errorPredecessorId;
    while (true) {
        State const & state = predecessors.states.at(currentId);
        assert(state.id == currentId);
        if (state.node == graph->getEntry()) { break; }
        auto const & [predecessorId, edge] = predecessors.predecessors.at(currentId);
        errorPath.push_back(edge);
        currentId = predecessorId;
    }
    std::ranges::reverse(errorPath);
    ErrorPath const path{std::move(errorPath)};
    return InvalidityWitness::fromErrorPath(path, *graph);
}

VerificationResult DirectForwardSymbolicExecution::run() {
    enum class InsertionResult { NEW, DUPLICATE };
    struct DiscoveredArgNodes {
        InsertionResult tryInsert(SymRef node, PTRef state) {
            const auto [_, inserted] = nodes[node].insert(state);
            return inserted ? InsertionResult::NEW : InsertionResult::DUPLICATE;
        }
    private:
        std::unordered_map<SymRef, std::unordered_set<PTRef, PTRefHash>, SymRefHash> nodes;
    };
    using Queue = std::deque<State>;
    Queue q;
    DiscoveredArgNodes nodes;
    Predecessors predecessors;
    Logic & logic = graph->getLogic();
    AdjacencyListsGraphRepresentation ar = AdjacencyListsGraphRepresentation::from(*graph);
    TermUtils utils(logic);
    State::id_t nextId = 0u;

    State entry {graph->getEntry(), logic.getTerm_true(), nextId++};
    q.emplace_back(entry);
    nodes.tryInsert(entry.node, entry.state);
    predecessors.states.push_back(entry);
    while (not q.empty()) {
        State currentState = q.front();
        q.pop_front();
        for (EId eid : ar.getOutgoingEdgesFor(currentState.node)) {
            auto target = graph->getTarget(eid);
            PTRef label = graph->getEdgeLabel(eid);
            if (target == graph->getExit()) {
                SMTSolver solver{logic, SMTSolver::WitnessProduction::NONE};
                solver.assertProp(currentState.state);
                solver.assertProp(label);
                auto res = solver.check();
                if (res == SMTSolver::Answer::SAT) {
                    if (computeWitness()) { return VerificationResult{VerificationAnswer::UNSAFE, getInvalidityWitness(eid, currentState.id, predecessors)}; }
                    return VerificationResult{VerificationAnswer::UNSAFE};
                }
                if (res != SMTSolver::Answer::UNSAT) { return VerificationResult{VerificationAnswer::UNKNOWN}; }
                continue;
            }
            PTRef rawState = utils.simplifyMax(logic.mkAnd(currentState.state, label));

            PTRef rawSimplified = TrivialQuantifierElimination(logic).tryEliminateVarsExcept(
                TermUtils(logic).predicateArgsInOrder(graph->getNextStateVersion(target)), rawState);
            PTRef newState = TimeMachine(logic).sendFlaThroughTime(rawSimplified, -1);
            auto insertionResult = nodes.tryInsert(target, newState);
            switch (insertionResult) {
                case InsertionResult::NEW: {
                    // TODO: Lightweight feasibility check?
                    State nextState {target, newState, nextId++};
                    if (computeWitness()) {
                        predecessors.add(nextState, currentState.id, eid);
                    }
                    q.push_back(nextState);
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

} // namespace



VerificationResult SymbolicExecution::solve(ChcDirectedHyperGraph const & graph) {
    if (graph.isNormalGraph()) {
        return DirectForwardSymbolicExecution(graph.toNormalGraph(), options).run();
    }
    return VerificationResult{VerificationAnswer::UNKNOWN};
}
} // namespace golem