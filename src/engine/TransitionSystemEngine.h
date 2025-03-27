/*
* Copyright (c) 2025, Martin Blicha <martin.blicha@gmail.com>
*
* SPDX-License-Identifier: MIT
*/

#ifndef TRANSITIONSYSTEMENGINE_H
#define TRANSITIONSYSTEMENGINE_H

#include "Engine.h"

class TransitionSystemEngine : public Engine {
public:
    VerificationResult solve(ChcDirectedHyperGraph const &) override;
    virtual VerificationResult solve(ChcDirectedGraph const &);
    virtual TransitionSystemVerificationResult solve(TransitionSystem const &);

protected:
    bool computeWitness{false};
};

#endif //TRANSITIONSYSTEMENGINE_H
