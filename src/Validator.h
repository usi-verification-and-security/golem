/*
 * Copyright (c) 2020-2025, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef GOLEM_VALIDATOR_H
#define GOLEM_VALIDATOR_H

#include "Witnesses.h"

#include "graph/ChcGraph.h"

namespace golem {
struct ValidationException : public std::runtime_error {
    explicit ValidationException(const std::string & msg) : std::runtime_error(msg) {}
    explicit ValidationException(const char * msg) : std::runtime_error(msg) {}
};

class Validator {
    Logic & logic;
public:
    explicit Validator(Logic & logic) : logic(logic) {}

    enum class Result {VALIDATED, NOT_VALIDATED};
    Result validate(ChcDirectedHyperGraph const & system, VerificationResult const & result);

private:
    [[nodiscard]]
    Result validateValidityWitness(ChcDirectedHyperGraph const & graph, ValidityWitness const & witness) const;

    [[nodiscard]]
    Result validateInvalidityWitness(ChcDirectedHyperGraph const & graph, InvalidityWitness const & witness) const;
};
} // namespace golem


#endif //GOLEM_VALIDATOR_H
