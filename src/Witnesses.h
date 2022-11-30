/*
 * Copyright (c) 2020-2022, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef GOLEM_WITNESSES_H
#define GOLEM_WITNESSES_H

#include "ChcGraph.h"
#include "TransitionSystem.h"

#include "osmt_solver.h"

class WitnessModel {
    std::unique_ptr<Model> model;
public:
    WitnessModel() = default;
    explicit WitnessModel(std::unique_ptr<Model> model) : model(std::move(model)) {}

    PTRef evaluate(PTRef fla) const { return model->evaluate(fla); }
};

class ErrorPath {
    std::vector<EId> path;
public:
    ErrorPath() = default;
    ErrorPath(std::vector<EId> path) : path(std::move(path)) {}

    std::vector<EId> getEdges() const { return path; }
    void setPath(std::vector<EId> npath) { this->path = std::move(npath); }
    bool isEmpty() const { return path.empty(); }

    static ErrorPath fromTransitionSystem(ChcDirectedGraph const & graph, std::size_t unrollings);
};



class InvalidityWitness {
public:
    class Derivation {
        // Each derivation step derived a fact: fully instantiated predicate
        // Additionally, derivation step remembers its premises (ids) and edge/clause
    public:
        using id_t = EId;
    	struct DerivationStep {
            std::size_t index {0};
            std::vector<std::size_t> premises;
            PTRef derivedFact;
            id_t clauseId;
        };

        void addDerivationStep(DerivationStep step) {
            derivationSteps.push_back(std::move(step));
        }
        DerivationStep &        operator[](std::size_t index)       { assert(index < derivationSteps.size()); return derivationSteps[index]; }
        DerivationStep const &  operator[](std::size_t index) const { assert(index < derivationSteps.size()); return derivationSteps[index]; }
        DerivationStep &        last()       { assert(size() > 0); return derivationSteps[size() - 1]; }
        DerivationStep const &  last() const { assert(size() > 0); return derivationSteps[size() - 1]; }
        std::size_t size() const { return derivationSteps.size(); }
private:
        std::vector<DerivationStep> derivationSteps;
    };

private:
    Derivation derivation;

public:
    void setDerivation(Derivation derivation_) { derivation = std::move(derivation_); }

    Derivation const & getDerivation() const { return derivation; }

    static InvalidityWitness fromErrorPath(ErrorPath const & errorPath, ChcDirectedGraph const & graph);
    static InvalidityWitness fromTransitionSystem(ChcDirectedGraph const & graph, std::size_t unrollings);

    void print(std::ostream & out, Logic & logic) const;
};

class ValidityWitness {
    std::unordered_map<PTRef, PTRef, PTRefHash> interpretations;
public:
    using definitions_t = decltype(interpretations);
    using entry_type = decltype(interpretations)::value_type;

    ValidityWitness() {}

    explicit ValidityWitness(definitions_t interpretations)
        : interpretations(std::move(interpretations)) {}

    template<typename TFun>
    void run(TFun fun) const {
        for (auto const & entry : interpretations) {
            fun(entry);
        }
    }

    definitions_t getDefinitions() const { return interpretations; }

    void print(std::ostream & out, Logic & logic) const;

    static ValidityWitness fromTransitionSystem(Logic & logic, ChcDirectedGraph const & graph,
                                                TransitionSystem const & transitionSystem, PTRef invariant);
};

enum class VerificationAnswer : char {SAFE, UNSAFE, UNKNOWN};

class VerificationResult {
    VerificationAnswer answer;
    // TODO: use variant from c++17
    ValidityWitness validityWitness;
    InvalidityWitness invalidityWitness;

public:
    VerificationResult(VerificationAnswer answer, ValidityWitness validityWitness)
        : answer(answer), validityWitness(std::move(validityWitness)) {}

    VerificationResult(VerificationAnswer answer, InvalidityWitness invalidityWitness)
        : answer(answer), invalidityWitness(std::move(invalidityWitness)) {}

    explicit VerificationResult(VerificationAnswer answer) : answer(answer) {}

    VerificationAnswer getAnswer() const { return answer; }

    ValidityWitness const & getValidityWitness() const { assert(answer == VerificationAnswer::SAFE); return validityWitness; }
    InvalidityWitness const & getInvalidityWitness() const { assert(answer == VerificationAnswer::UNSAFE); return invalidityWitness; }

    void printWitness(std::ostream & out, Logic & logic) const;
};

#endif // GOLEM_WITNESSES_H
