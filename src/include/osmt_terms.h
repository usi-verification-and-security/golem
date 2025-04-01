/*
 * Copyright (c) 2021-2025, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef GOLEM_OSMT_TERMS_H
#define GOLEM_OSMT_TERMS_H

#ifdef OPENSMT_LOCAL_BUILD
#include "logics/ArithLogic.h"
#include "pterms/PTRef.h"
#include "symbols/SymRef.h"
#include "common/TreeOps.h"
#include "simplifiers//BoolRewriting.h"
#include "rewriters/Substitutor.h"
#include "rewriters/DivModRewriter.h"
#include "rewriters/DistinctRewriter.h"
#include "itehandler/IteHandler.h"
#else
#include "opensmt/ArithLogic.h"
#include "opensmt/PTRef.h"
#include "opensmt/SymRef.h"
#include "opensmt/TreeOps.h"
#include "opensmt/BoolRewriting.h"
#include "opensmt/Substitutor.h"
#include "opensmt/DivModRewriter.h"
#include "opensmt/DistinctRewriter.h"
#include "opensmt/IteHandler.h"
#endif // OPENSMT_LOCAL_BUILD

using namespace opensmt;

#endif //GOLEM_OSMT_TERMS_H
