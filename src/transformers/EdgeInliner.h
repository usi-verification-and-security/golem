/*
 * Copyright (c) 2024, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef EDGEINLINER_H
#define EDGEINLINER_H

#include "Transformer.h"

class EdgeInliner : public Transformer {

public:
    TransformationResult transform(std::unique_ptr<ChcDirectedHyperGraph> graph) override;

    class BackTranslator : public WitnessBackTranslator {
    public:
        InvalidityWitness translate(InvalidityWitness witness) override { return witness; }
        ValidityWitness translate(ValidityWitness witness) override { return witness; }
    };
};



#endif //EDGEINLINER_H
