/*
 * Copyright (c) 2024, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "EngineFactory.h"

#include "ArgBasedEngine.h"
#include "Bmc.h"
#include "DAR.h"
#include "IMC.h"
#include "Kind.h"
#include "Lawi.h"
#include "PDKind.h"
#include "Spacer.h"
#include "SymbolicExecution.h"
#include "TPA.h"

namespace golem {
std::unique_ptr<Engine> EngineFactory::getEngine(std::string_view engine) && {
    if (engine == "spacer") {
        return std::make_unique<Spacer>(logic, options);
    } else if (engine == TPAEngine::TPA) {
        return std::make_unique<TPAEngine>(logic, options, TPACore::BASIC);
    } else if (engine == TPAEngine::SPLIT_TPA) {
        return std::make_unique<TPAEngine>(logic, options, TPACore::SPLIT);
    } else if (engine == "bmc") {
        return std::make_unique<BMC>(logic, options);
    } else if (engine == "dar") {
        return std::make_unique<DAR>(logic, options);
    } else if (engine == "lawi") {
        return std::make_unique<Lawi>(logic, options);
    } else if (engine == "kind") {
        return std::make_unique<Kind>(logic, options);
    } else if (engine == "imc") {
        return std::make_unique<IMC>(logic, options);
    } else if (engine == "pdkind") {
        return std::make_unique<PDKind>(logic, options);
    } else if (engine == "pa") {
        return std::make_unique<ARGBasedEngine>(logic, options);
    } else if (engine == "se") {
        return std::make_unique<SymbolicExecution>(logic, options);
    } else {
        throw std::invalid_argument("Unknown engine specified");
    }
}
} // namespace golem