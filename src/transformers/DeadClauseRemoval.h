/*
 * Copyright (c) 2022, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef GOLEM_DEADCLAUSEREMOVAL_H
#define GOLEM_DEADCLAUSEREMOVAL_H

#include "Transformer.h"

class DeadClauseRemoval : public Transformer {
public:
    TransformationResult transform(std::unique_ptr<ChcDirectedHyperGraph> graph) override;

    class BackTranslator : public WitnessBackTranslator {
        InvalidityWitness translate(InvalidityWitness witness) { return witness; }
        ValidityWitness translate(ValidityWitness witness) { return witness; }
    };
};


#endif //GOLEM_DEADCLAUSEREMOVAL_H
