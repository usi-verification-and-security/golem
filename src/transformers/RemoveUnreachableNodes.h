/*
 * Copyright (c) 2022-2025, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef GOLEM_REMOVEUNREACHABLENODES_H
#define GOLEM_REMOVEUNREACHABLENODES_H

#include "Transformer.h"

namespace golem {

class RemoveUnreachableNodes : public Transformer {
public:
    TransformationResult transform(std::unique_ptr<ChcDirectedHyperGraph> graph) override;

    class BackTranslator : public WitnessBackTranslator {
        Logic & logic;
        std::vector<SymRef> unreachableFromTrue;
        std::vector<SymRef> backwardUnreachableFromFalse;

    public:
        BackTranslator(Logic & logic, std::vector<SymRef> && unreachableFromTrue,
                       std::vector<SymRef> && backwardUnreachableFromFalse)
            : logic(logic),
              unreachableFromTrue(std::move(unreachableFromTrue)),
              backwardUnreachableFromFalse(std::move(backwardUnreachableFromFalse)) {}

        InvalidityWitness translate(InvalidityWitness witness) override { return witness; }
        ValidityWitness translate(ValidityWitness witness) override;
    };
};

// For termination, we want to have an option that eliminates only forward unreachable nodes
class RemoveForwardUnreachableNodes : public Transformer {
public:
    TransformationResult transform(std::unique_ptr<ChcDirectedHyperGraph> graph) override;

    class BackTranslator : public WitnessBackTranslator {
        Logic & logic;
        std::vector<SymRef> unreachableFromTrue;

    public:
        BackTranslator(Logic & logic, std::vector<SymRef> && unreachableFromTrue)
            : logic(logic), unreachableFromTrue(std::move(unreachableFromTrue)) {}

        InvalidityWitness translate(InvalidityWitness witness) override { return witness; }
        ValidityWitness translate(ValidityWitness witness) override;
    };
};

} // namespace golem

#endif // GOLEM_REMOVEUNREACHABLENODES_H
