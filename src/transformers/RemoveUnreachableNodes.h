/*
 * Copyright (c) 2022, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef GOLEM_REMOVEUNREACHABLENODES_H
#define GOLEM_REMOVEUNREACHABLENODES_H

#include "Transformer.h"

class RemoveUnreachableNodes : public Transformer {
public:
    TransformationResult transform(std::unique_ptr<ChcDirectedHyperGraph> graph) override;

    class BackTranslator : public WitnessBackTranslator {
        Logic & logic;
        std::vector<SymRef> unreachableFromTrue;
        std::vector<SymRef> backwardUnreachableFromFalse;

    public:
        BackTranslator(Logic & logic, std::vector<SymRef> && unreachableFromTrue, std::vector<SymRef> && backwardUnreachableFromFalse) :
            logic(logic),
            unreachableFromTrue(std::move(unreachableFromTrue)),
            backwardUnreachableFromFalse(std::move(backwardUnreachableFromFalse))
            {}

        InvalidityWitness translate(InvalidityWitness witness) override { return witness; }
        ValidityWitness translate(ValidityWitness witness) override;
    };
};


#endif //GOLEM_REMOVEUNREACHABLENODES_H
