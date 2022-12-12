/*
 * Copyright (c) 2020 - 2022, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef OPENSMT_VALIDATOR_H
#define OPENSMT_VALIDATOR_H


#include "engine/Engine.h"
#include "graph/ChcGraph.h"

struct ValidationException : public std::runtime_error {
public:
    ValidationException(const std::string & msg) : std::runtime_error(msg) {}
    ValidationException(const char * msg) : std::runtime_error(msg) {}
};

class Validator {
    Logic & logic;
public:
    Validator(Logic & logic) : logic(logic) {}

    enum class Result {VALIDATED, NOT_VALIDATED};
    Result validate(ChcDirectedHyperGraph const & system, VerificationResult const & result);

private:
    Result validateValidityWitness(ChcDirectedHyperGraph const & graph, ValidityWitness const & witness);
    Result validateInvalidityWitness(ChcDirectedHyperGraph const & graph, InvalidityWitness const & witness);
};


#endif //OPENSMT_VALIDATOR_H
