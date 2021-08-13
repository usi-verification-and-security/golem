//
// Created by Martin Blicha on 17.07.20.
//

#ifndef OPENSMT_BMC_H
#define OPENSMT_BMC_H

#include "Engine.h"

#include "TransitionSystem.h"

class BMC : public Engine {
    Logic & logic;
    Options const & options;
public:

    BMC(Logic& logic, Options const & options) : logic(logic), options(options) {}

    virtual GraphVerificationResult
    solve(ChcDirectedHyperGraph& system) override { throw std::logic_error("Not supported yet!"); }

    virtual GraphVerificationResult solve(ChcDirectedGraph const & system) override;

private:
    GraphVerificationResult solveTransitionSystem(TransitionSystem & system);
};


#endif //OPENSMT_BMC_H
