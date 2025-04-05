/*
 * Copyright (c) 2024-2025, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef GOLEM_ENGINEFACTORY_H
#define GOLEM_ENGINEFACTORY_H

#include "Engine.h"
#include "Options.h"

namespace golem {
class EngineFactory {
public:
    EngineFactory(Logic & logic, Options const & options) : logic(logic), options(options) {}
    std::unique_ptr<Engine> getEngine(std::string_view engine) &&;

private:
    Logic & logic;
    Options const & options;
};
} // namespace golem

#endif // GOLEM_ENGINEFACTORY_H
