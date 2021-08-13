//
// Created by Martin Blicha on 21.08.20.
//

#ifndef OPENSMT_VALIDATOR_H
#define OPENSMT_VALIDATOR_H


#include "engine/Engine.h"
#include "ChcGraph.h"

class Validator {
    Logic & logic;
public:
    Validator(Logic & logic) : logic(logic) {}

    enum class Result {VALIDATED, NOT_VALIDATED};
    Result validate(ChcSystem const & system, SystemVerificationResult const & result);

private:
    Result validateValidityWitness(ChcDirectedGraph const & graph, ValidityWitness const & witness);
    Result validateValidityWitness(ChcSystem const & system, ValidityWitness const & witness);
    Result validateInvalidityWitness(ChcSystem const & system, SystemInvalidityWitness const & witness);

    bool isPresentInSystem(ChClause const & clause, ChcSystem const & system) const;
};


#endif //OPENSMT_VALIDATOR_H
