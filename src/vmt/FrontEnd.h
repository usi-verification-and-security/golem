/*
 * Copyright (c) 2025, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef VMT_FRONTEND_H
#define VMT_FRONTEND_H

#include "Options.h"

#include <string>

namespace golem::vmt {
void run(std::string const & filename, Options const & options);
}

#endif //VMT_FRONTEND_H