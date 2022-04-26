/*
 * Copyright (c) 2022, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef GOLEM_TRANSFORMATIONPIPELINE_H
#define GOLEM_TRANSFORMATIONPIPELINE_H

#include "Transformer.h"

class TransformationPipeline : Transformer {
public:
    class BackTranslator : public WitnessBackTranslator {
    public:
        using pipeline_t = std::vector<std::unique_ptr<WitnessBackTranslator>>;

        BackTranslator(pipeline_t && pipeline) : inner(std::move(pipeline)) {}

        InvalidityWitness translate(InvalidityWitness witness) override;

        ValidityWitness translate(ValidityWitness witness) override;
    private:
        pipeline_t inner;
    };

    using pipeline_t = std::vector<std::unique_ptr<Transformer>>;

    TransformationPipeline(pipeline_t && pipeline) : inner(std::move(pipeline)) {}

    TransformationResult transform(std::unique_ptr<ChcDirectedHyperGraph> graph) override;

private:
    pipeline_t inner;
};


#endif //GOLEM_TRANSFORMATIONPIPELINE_H
