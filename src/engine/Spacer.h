/*
 * Copyright (c) 2021-2022, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef OPENSMT_SPACER_H
#define OPENSMT_SPACER_H

#include "Engine.h"

class Spacer : public Engine {
    Logic & logic;
    Options const & options;

public:
    Spacer(Logic & logic, Options const & options) : logic(logic), options(options) {}

    [[nodiscard]] VerificationResult solve(ChcDirectedHyperGraph const & system) override;
};


#endif //OPENSMT_SPACER_H
