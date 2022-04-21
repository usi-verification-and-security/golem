//
// Created by Martin Blicha on 17.07.20.
//

#ifndef OPENSMT_ENGINE_H
#define OPENSMT_ENGINE_H

#include "Witnesses.h"
#include "ChcGraph.h"
#include "Options.h"

#include "osmt_solver.h"
#include "osmt_terms.h"

#include <memory>


enum class VerificationResult {SAFE, UNSAFE, UNKNOWN};

class GraphVerificationResult {
    VerificationResult answer;
    // TODO: use variant from c++17
    ValidityWitness validityWitness;
    InvalidityWitness invalidityWitness;

public:
    GraphVerificationResult(VerificationResult answer, ValidityWitness validityWitness)
        : answer(answer), validityWitness(std::move(validityWitness)) {}

    GraphVerificationResult(VerificationResult answer, InvalidityWitness invalidityWitness)
        : answer(answer), invalidityWitness(std::move(invalidityWitness)) {}

    explicit GraphVerificationResult(VerificationResult answer) : answer(answer) {}

    VerificationResult getAnswer() const { return answer; }

    ValidityWitness const & getValidityWitness() const { assert(answer == VerificationResult::SAFE); return validityWitness; }
    InvalidityWitness const & getInvalidityWitness() const { assert(answer == VerificationResult::UNSAFE); return invalidityWitness; }
};

class SystemVerificationResult {
    VerificationResult answer;
    // TODO: use variant from c++17
    ValidityWitness validityWitness;
    SystemInvalidityWitness invalidityWitness;

public:
    SystemVerificationResult(GraphVerificationResult && graphResult, ChcDirectedGraph & graph) {
        answer = graphResult.getAnswer();
        if (answer == VerificationResult::SAFE) {
            validityWitness = graphResult.getValidityWitness();
        }
        if (answer == VerificationResult::UNSAFE) {
            invalidityWitness = graphToSystemInvalidityWitness(graphResult.getInvalidityWitness(), graph);
        }
    }

    SystemVerificationResult(GraphVerificationResult && graphResult) {
        answer = graphResult.getAnswer();
        if (answer == VerificationResult::SAFE) {
            validityWitness = graphResult.getValidityWitness();
        }
    }

    VerificationResult getAnswer() const { return answer; }

    ValidityWitness const & getValidityWitness() const { return validityWitness; }
    SystemInvalidityWitness const & getInvalidityWitness() const { return invalidityWitness; }

    void printWitness(std::ostream & out, Logic & logic) const {
        switch (answer) {
            case VerificationResult::SAFE: {
                TermUtils utils(logic);
                validityWitness.print(out, logic);
                return;
            }
            case VerificationResult::UNSAFE: {
                invalidityWitness.print(out, logic);
                return;
            }
            default:
                return;
        }
    }
};

class Engine {
public:
    virtual GraphVerificationResult solve(ChcDirectedHyperGraph &) {
        throw std::logic_error("Not implemented yet!");
    }

    virtual GraphVerificationResult solve(ChcDirectedGraph const &) {
        throw std::logic_error("Not implemented yet!");
    }

    virtual ~Engine() = default;
};

#endif //OPENSMT_ENGINE_H
