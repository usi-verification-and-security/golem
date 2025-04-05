/*
 * Copyright (c) 2022-2025, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef GOLEM_BASICTRANSFORMATIONPIPELINES_H
#define GOLEM_BASICTRANSFORMATIONPIPELINES_H

#include "TransformationPipeline.h"

namespace golem::Transformations {

TransformationPipeline towardsTransitionSystems();

TransformationPipeline defaultTransformationPipeline();

} // namespace golem::Transformations


#endif //GOLEM_BASICTRANSFORMATIONPIPELINES_H
