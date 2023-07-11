/*
* Copyright (c) 2023, Martin Blicha <martin.blicha@gmail.com>
*
* SPDX-License-Identifier: MIT
*/
#ifndef GOLEM_SINGLELOOPTRANSFORMATION_H
#define GOLEM_SINGLELOOPTRANSFORMATION_H

#include "TransitionSystem.h"
#include "graph/ChcGraph.h"
#include "Witnesses.h"

class SingleLoopTransformation {
public:
    // Helper types
    struct VarPosition {
        SymRef vertex;
        uint32_t pos;

        inline bool operator==(VarPosition other) const { return vertex == other.vertex and pos == other.pos; }
    };
    struct VarPositionHasher {
        std::size_t operator()(VarPosition pos) const {
            std::hash<std::size_t> hasher;
            std::size_t res = 0;
            res ^= hasher(pos.vertex.x) + 0x9e3779b9 + (res<<6) + (res>>2);
            res ^= hasher(pos.pos) + 0x9e3779b9 + (res<<6) + (res>>2);
            return res;
        }
    };

    using LocationVarMap = std::unordered_map<SymRef, PTRef, SymRefHash>;
    using PositionVarMap = std::unordered_map<VarPosition, PTRef, VarPositionHasher>;


    class WitnessBackTranslator {
        ChcDirectedGraph const & graph;
        TransitionSystem const & transitionSystem;
        LocationVarMap locationVarMap;
        PositionVarMap positionVarMap;
    public:
        WitnessBackTranslator(
            ChcDirectedGraph const & graph,
            TransitionSystem const & transitionSystem,
            LocationVarMap && locationVarMap,
            PositionVarMap && positionVarMap
            )
            : graph(graph),
              transitionSystem(transitionSystem),
              locationVarMap(std::move(locationVarMap)),
              positionVarMap(std::move(positionVarMap))
        {}

        VerificationResult translate(TransitionSystemVerificationResult result);

        InvalidityWitness translateErrorPath(std::size_t unrolling);

        ValidityWitness translateInvariant(PTRef inductiveInvariant);

    private:
        std::set<PTRef> getVarsForVertex(SymRef vertex) const;
    };


    // Main methods
    using TransformationResult = std::pair<std::unique_ptr<TransitionSystem>, std::unique_ptr<WitnessBackTranslator>>;

    TransformationResult transform(ChcDirectedGraph const & graph);
};

#endif // GOLEM_SINGLELOOPTRANSFORMATION_H
