/*
 * Copyright (c) 2021-2025, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef GOLEM_OSMT_LOGICS_H
#define GOLEM_OSMT_LOGICS_H

#ifdef OPENSMT_LOCAL_BUILD
#include "api/MainSolver.h"
#include "models/Model.h"
#else
#include "opensmt/MainSolver.h"
#include "opensmt/Model.h"
#endif // OPENSMT_LOCAL_BUILD

using namespace opensmt;

#endif //GOLEM_OSMT_LOGICS_H
