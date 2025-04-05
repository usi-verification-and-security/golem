/*
 * Copyright (c) 2021-2025, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef OPENSMT_SPACER_H
#define OPENSMT_SPACER_H

#include "Engine.h"
#include "Options.h"

namespace golem {
class Spacer : public Engine {
    Logic & logic;
    Options const & options;

public:
    Spacer(Logic & logic, Options const & options) : logic(logic), options(options) {}

    [[nodiscard]] VerificationResult solve(ChcDirectedHyperGraph const & system) override;
};
} // namespace golem


#endif //OPENSMT_SPACER_H
