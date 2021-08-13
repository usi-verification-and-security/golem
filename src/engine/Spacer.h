//
// Created by Martin Blicha on 21.02.21.
//

#ifndef OPENSMT_SPACER_H
#define OPENSMT_SPACER_H

#include "Engine.h"

class Spacer : public Engine {
    Logic & logic;

public:
    Spacer(Logic & logic, Options const & options): logic(logic) {}

    GraphVerificationResult solve(ChcDirectedHyperGraph & system) override;

    GraphVerificationResult solve(const ChcDirectedGraph & system) override;

};


#endif //OPENSMT_SPACER_H
