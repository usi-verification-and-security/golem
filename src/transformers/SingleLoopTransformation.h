/*
 * Copyright (c) 2023, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */
#ifndef GOLEM_SINGLELOOPTRANSFORMATION_H
#define GOLEM_SINGLELOOPTRANSFORMATION_H

#include "CommonUtils.h"
#include "TransitionSystem.h"
#include "Witnesses.h"
#include "graph/ChcGraph.h"

/**
 * This class implements a transformation from a general linear CHC system to a transition system (defined by initial
 * states, transition relation and bad states).
 * The implementation follows the algorithm described in the short paper
 * Horn2VMT: Translating Horn Reachability into Transition Systems
 * presented in HCVS 2020. See, e.g., https://www.osti.gov/biblio/1783647
 *
 * The idea behind the transformation is the following.
 * We introduce a separate boolean variable for each location (predicate, vertex in the CHC graph).
 * For each predicate and each argument of the predicate we add a new state variable of the transition system.
 * Then, for each edge (clause), we create a new disjunct of the transition relation.
 * This fragment captures the changes to the variables as defined by the edge constraint.
 * The fragment enforces that the current source location is variable is true and next target variable is true.
 * All other location variables are false (or alternatively keep their previous value).
 * The edge's constraint is translated to be over corresponding state variables (state vars from source, next state
 * vars from target), all other variables are unchanged.
 *
 * Backtranslating witness from transition system is currently based on the following reasoning:
 * To backtranslate proof, we have to identify which disjunct of the transition relation was used to make each step
 * in the error trace of the transition system. From that we can deduce which edge needs to be taken
 * (and with what values) in the CHC graph.
 *
 * For the model, we compute restriction of the TS invariant to each location by substituting appropriate constant
 * values for location variables. This may still leave some undesired variables in the invariant. We currently make
 * best effort to eliminate these variables by simplifying the formula.
 */
class SingleLoopTransformation {
public:
    class WitnessBackTranslator {
        ChcDirectedGraph const & graph;
        TransitionSystem const & transitionSystem;
        LocationVarMap locationVarMap;
        PositionVarMap positionVarMap;

    public:
        WitnessBackTranslator(ChcDirectedGraph const & graph, TransitionSystem const & transitionSystem,
                              LocationVarMap && locationVarMap, PositionVarMap && positionVarMap)
            : graph(graph), transitionSystem(transitionSystem), locationVarMap(std::move(locationVarMap)),
              positionVarMap(std::move(positionVarMap)) {}

        VerificationResult translate(TransitionSystemVerificationResult result);

    private:
        template<typename T> using ErrorOr = std::variant<NoWitness, T>;

        ErrorOr<InvalidityWitness> translateErrorPath(std::size_t unrolling);

        ErrorOr<ValidityWitness> translateInvariant(PTRef inductiveInvariant);

        std::unordered_set<PTRef, PTRefHash> getVarsForVertex(SymRef vertex) const;
    };

    // Main method
    using TransformationResult = std::pair<std::unique_ptr<TransitionSystem>, std::unique_ptr<WitnessBackTranslator>>;

    TransformationResult transform(ChcDirectedGraph const & graph);
};

#endif // GOLEM_SINGLELOOPTRANSFORMATION_H
