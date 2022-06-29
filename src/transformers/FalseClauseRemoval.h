/*
 * Copyright (c) 2022, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef GOLEM_FALSECLAUSEREMOVAL_H
#define GOLEM_FALSECLAUSEREMOVAL_H

#include "Transformer.h"

class FalseClauseRemoval : public Transformer {
public:
    TransformationResult transform(std::unique_ptr<ChcDirectedHyperGraph> graph) override;

    class BackTranslator : public WitnessBackTranslator {
    public:
        InvalidityWitness translate(InvalidityWitness witness) override { return witness; }
        ValidityWitness translate(ValidityWitness witness) override { return witness; }
    };
};


#endif //GOLEM_FALSECLAUSEREMOVAL_H
