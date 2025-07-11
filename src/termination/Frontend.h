/*
 * Copyright (c) 2025, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef FRONTEND_H
#define FRONTEND_H

#include "Options.h"

#include <string>

namespace golem::termination {
void run(std::string const & filename, Options const & options);
}

#endif //FRONTEND_H
