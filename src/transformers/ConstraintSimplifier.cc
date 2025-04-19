/*
 * Copyright (c) 2023-2025, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "ConstraintSimplifier.h"

namespace helper {
class Normalizer {
    Logic & logic;
public:
    Normalizer(Logic & logic) : logic(logic) {}

    PTRef eliminateItes(PTRef fla);
    PTRef eliminateDivMod(PTRef fla);
    PTRef eliminateDistincts(PTRef fla);
};

PTRef Normalizer::eliminateDivMod(PTRef fla) {
    ArithLogic * lalogic = dynamic_cast<ArithLogic *>(&logic);
    if (lalogic and lalogic->hasIntegers()) {
        return DivModRewriter(*lalogic).rewrite(fla);
    }
    return fla;
}

PTRef Normalizer::eliminateItes(PTRef fla) {
    return IteHandler(logic).rewrite(fla);
}

PTRef Normalizer::eliminateDistincts(PTRef fla) {
    return DistinctRewriter(logic).rewrite(fla);
}

} // namespace helper

namespace golem {
Transformer::TransformationResult ConstraintSimplifier::transform(std::unique_ptr<ChcDirectedHyperGraph> graph) {

    Logic & logic = graph->getLogic();
    TermUtils utils(logic);
    graph->forEachEdge([&](auto & edge) {
        PTRef constraint = edge.fla.fla;
        helper::Normalizer normalizer(logic);
        constraint = normalizer.eliminateItes(constraint);
        constraint = normalizer.eliminateDivMod(constraint);
        constraint = normalizer.eliminateDistincts(constraint);

        vec<PTRef> stateVars;
        // TODO: Implement a helper to iterate over source vertices together with instantiation counter
        std::unordered_map<SymRef, std::size_t, SymRefHash> instanceCounter;
        for (auto source : edge.from) {
            PTRef sourcePredicate = graph->getStateVersion(source, instanceCounter[source]++);
            for (PTRef var : utils.predicateArgsInOrder(sourcePredicate)) {
                assert(logic.isVar(var));
                stateVars.push(var);
            }
        }

        PTRef targetPredicate = graph->getNextStateVersion(edge.to);
        for (PTRef var : utils.predicateArgsInOrder(targetPredicate)) {
            assert(logic.isVar(var));
            stateVars.push(var);
        }
        constraint = TrivialQuantifierElimination(logic).tryEliminateVarsExcept(stateVars, constraint);
        // Elimination of DIV/MOD and ITE might have introduced new auxiliary variables, we need to version them
        TimeMachine timeMachine(logic);
        VersionManager versionManager(logic);
        auto isVarToNormalize = [&](PTRef var) {
            return logic.isVar(var) and not versionManager.isTagged(var) and not timeMachine.isVersioned(var);
        };
        auto localVars = matchingSubTerms(logic, constraint, isVarToNormalize);
        if (localVars.size() > 0) {
            TermUtils::substitutions_map subst;
            for (PTRef localVar : localVars) {
                // FIXME: This is not ideal, we can get a clash if the same DIV/MOD/ITE term occurs in different clauses
                //        But we should anyway find a better way to handle these variables. Ideally unify this again with normalizer.
                subst.insert({localVar, timeMachine.getVarVersionZero(localVar)});
            }
            constraint = utils.varSubstitute(constraint, subst);
        }
        edge.fla.fla = constraint;
    });
    return {std::move(graph), std::make_unique<BackTranslator>()};
}
} // namespace golem