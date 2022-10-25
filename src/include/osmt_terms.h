/*
 * Copyright (c) 2021-2022, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef GOLEM_OSMT_TERMS_H
#define GOLEM_OSMT_TERMS_H

#ifdef OPENSMT_LOCAL_BUILD
#include "ArithLogic.h"
#include "PTRef.h"
#include "SymRef.h"
#include "TreeOps.h"
#include "BoolRewriting.h"
#include "Substitutor.h"
#include "DivModRewriter.h"
#include "DistinctRewriter.h"
#include "IteHandler.h"
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

#endif //GOLEM_OSMT_TERMS_H
