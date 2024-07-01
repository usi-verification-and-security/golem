/*
 * Copyright (c) 2024, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "EngineFactory.h"

#include "Bmc.h"
#include "IMC.h"
#include "Kind.h"
#include "Lawi.h"
#include "Spacer.h"
#include "TPA.h"

std::unique_ptr<Engine> EngineFactory::getEngine(std::string_view engine) && {
    if (engine == "spacer") {
        return std::make_unique<Spacer>(logic, options);
    } else if (engine == TPAEngine::TPA) {
        return std::make_unique<TPAEngine>(logic, options, TPACore::BASIC);
    } else if (engine == TPAEngine::SPLIT_TPA) {
        return std::make_unique<TPAEngine>(logic, options, TPACore::SPLIT);
    } else if (engine == "bmc") {
        return std::make_unique<BMC>(logic, options);
    } else if (engine == "lawi") {
        return std::make_unique<Lawi>(logic, options);
    } else if (engine == "kind") {
        return std::make_unique<Kind>(logic, options);
    } else if (engine == "imc") {
        return std::make_unique<IMC>(logic, options);
    } else {
        throw std::invalid_argument("Unknown engine specified");
    }
}
