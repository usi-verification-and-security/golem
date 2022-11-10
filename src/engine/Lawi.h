/*
 * Copyright (c) 2020-2022, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef GOLEM_LAWI_H
#define GOLEM_LAWI_H

#include "Engine.h"

/*
 * Implementation of Lazy Abstraction with Interpolants (also known as IMPACT algorithm)
 *
 * Implementation based on McMillan's original paper Lazy Abstraction with Interpolants, CAV 2006.
 * https://link.springer.com/chapter/10.1007/11817963_14
 * Another good paper: Algorithms for Software Model Checking: Predicate Abstraction vs. IMPACT, D. Beyer and P. Wendler, FMCAD 2012
 * https://ieeexplore.ieee.org/document/6462562
 */
class Lawi : public Engine {
    Logic & logic;
    Options const & options;
public:
    Lawi(Logic & logic, Options const & options) : logic(logic), options(options) {}

    GraphVerificationResult solve(ChcDirectedHyperGraph & system) override;

    GraphVerificationResult solve(const ChcDirectedGraph & system);

private:

};


#endif //GOLEM_LAWI_H
