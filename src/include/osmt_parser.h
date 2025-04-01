/*
 * Copyright (c) 2021-2025, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef GOLEM_OSMT_PARSER_H
#define GOLEM_OSMT_PARSER_H

#ifdef OPENSMT_LOCAL_BUILD
#include "parsers/smt2new/smt2newcontext.h"
#else
#include "opensmt/smt2newcontext.h"
#endif // OPENSMT_LOCAL_BUILD

#endif //GOLEM_OSMT_PARSER_H
