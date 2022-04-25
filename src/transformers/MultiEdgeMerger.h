/*
 * Copyright (c) 2022, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef GOLEM_MULTIEDGEMERGER_H
#define GOLEM_MULTIEDGEMERGER_H

#include "Transformer.h"

class MultiEdgeMerger : public Transformer {
public:
    TransformationResult transform(std::unique_ptr<ChcDirectedHyperGraph> graph) override;

    class BackTranslator : public WitnessBackTranslator {
    public:
        InvalidityWitness translate(InvalidityWitness witness) override;

        ValidityWitness translate(ValidityWitness witness) override;

        bool somethingChanged {false};
    };
};


#endif //GOLEM_MULTIEDGEMERGER_H
