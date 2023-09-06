/*
 * Copyright (c) 2023, Martin Blicha <martin.blicha@gmail.com>
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

}

Transformer::TransformationResult ConstraintSimplifier::transform(std::unique_ptr<ChcDirectedHyperGraph> graph) {

    Logic & logic = graph->getLogic();
    graph->forEachEdge([&](auto & edge) {
        PTRef constraint = edge.fla.fla;
        helper::Normalizer normalizer(logic);
        constraint = normalizer.eliminateItes(constraint);
        constraint = normalizer.eliminateDivMod(constraint);
        constraint = normalizer.eliminateDistincts(constraint);

        auto auxiliaryVars = matchingSubTerms(logic, constraint, [&](PTRef term) {
             return logic.isVar(term) and strncmp("aux#", logic.getSymName(term), 4) == 0;
         });
        constraint = TrivialQuantifierElimination(logic).tryEliminateVars(auxiliaryVars, constraint);
        edge.fla.fla = constraint;
    });
    return {std::move(graph), std::make_unique<BackTranslator>()};
}
