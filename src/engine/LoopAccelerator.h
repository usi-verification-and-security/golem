//
// Created by Martin Blicha on 24.08.20.
//

#ifndef OPENSMT_LOOPACCELERATOR_H
#define OPENSMT_LOOPACCELERATOR_H

#include "Engine.h"

#include "osmt_terms.h"

#include <memory>

class LoopAccelerator : public Engine {
    LALogic & logic;
    std::unique_ptr<Engine> delegate;
    static const std::string PREFIX;
    static const std::string LOOP_COUNTER_PREFIX;
    mutable long long varCounter = 0;
    mutable long long loopCounter = 0;
public:
    LoopAccelerator(LALogic & logic, std::unique_ptr<Engine> delegate) : logic(logic), delegate(std::move(delegate)) {}

    GraphVerificationResult solve(const ChcDirectedGraph & graph) override;
private:
    struct AcceleratedResult {
        ChcDirectedGraph graph;
        std::map<EId, EId> toOriginal;
    };

    std::vector<EId> getSelfLoops(ChcDirectedGraph const & graph) const {
        auto edges = graph.getEdges();
        edges.erase(std::remove_if(edges.begin(), edges.end(), [&graph](EId edge) {
           return graph.getSource(edge) != graph.getTarget(edge);
        }), edges.end());
        return edges;
    }

    PTRef getLoopCounterVar() const {
        std::string varName = LOOP_COUNTER_PREFIX + std::to_string(loopCounter++);
        PTRef loopCounterVar = logic.mkNumVar(varName.c_str());
        return TimeMachine(logic).getVarVersionZero(loopCounterVar);
    }

    std::map<EId, PTRef> getAcceleratedLoops(std::vector<EId> selfLoops, ChcDirectedGraph const & graph) const;

    ChcDirectedGraph removeAcceleratedLoops(ChcDirectedGraph const & original, std::map<EId, PTRef> const & acceleratedLoops) const;

    bool isLoopCounterVar(PTRef var) const;
    bool isAcceleratedPredicatedSymbol(SymRef sym) const;
    bool isAcceleratedPredicatedSymbol(PTRef predicate) const { return isAcceleratedPredicatedSymbol(logic.getSymRef(predicate)); }

    PTRef extractLoopCountVar(PTRef fla) const;
};

#endif //OPENSMT_LOOPACCELERATOR_H
