/*
 * Copyright (c) 2025, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef LASSODETECTOR_H
#define LASSODETECTOR_H

#include "osmt_terms.h"

#include "Options.h"
#include "TransitionSystem.h"

namespace golem::termination {

class LassoDetector {
public:
    explicit LassoDetector(Options const & options) : options(options) {}

    enum struct Answer { LASSO, NO_LASSO, UNKNOWN, ERROR };

    Answer find_lasso(TransitionSystem const & system);

private:
    Options const & options;
};
} // namespace golem::termination

#endif //LASSODETECTOR_H
