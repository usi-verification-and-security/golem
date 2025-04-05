/*
 * Copyright (c) 2022-2025, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef GOLEM_TRANSFORMATIONPIPELINE_H
#define GOLEM_TRANSFORMATIONPIPELINE_H

#include "Transformer.h"

namespace golem {
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

    explicit TransformationPipeline(pipeline_t && pipeline) : inner(std::move(pipeline)) {}

    TransformationResult transform(std::unique_ptr<ChcDirectedHyperGraph> graph) override;

private:
    pipeline_t inner;
};
} // namespace golem

#endif //GOLEM_TRANSFORMATIONPIPELINE_H
