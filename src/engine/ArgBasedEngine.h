/*
 * Copyright (c) 2024, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef GOLEM_ARGBASEDENGINE_H
#define GOLEM_ARGBASEDENGINE_H

#include "osmt_terms.h"
#include "graph/ChcGraph.h"
#include "Witnesses.h"

class ARGBasedEngine {
   Logic & logic;
public:

   ARGBasedEngine(Logic & logic) : logic(logic) {}

   VerificationResult solve(ChcDirectedHyperGraph const & graph);
};


#endif //GOLEM_ARGBASEDENGINE_H
