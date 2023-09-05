/*
 * Copyright (c) 2020-2023, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef GOLEM_WITNESSES_H
#define GOLEM_WITNESSES_H

#include "TransitionSystem.h"
#include "graph/ChcGraph.h"
#include "osmt_solver.h"
#include "proofs/Term.h"
#include "Normalizer.h"
#include <memory>
#include <variant>

class ErrorPath {
    std::vector<EId> path;
public:
    ErrorPath() = default;
    explicit ErrorPath(std::vector<EId> path) : path(std::move(path)) {}

    [[nodiscard]] std::vector<EId> getEdges() const { return path; }
    [[nodiscard]] bool isEmpty() const { return path.empty(); }
    void setPath(std::vector<EId> npath) { this->path = std::move(npath); }

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
        [[nodiscard]] DerivationStep const &  last() const { assert(size() > 0); return derivationSteps[size() - 1]; }
        [[nodiscard]] std::size_t size() const { return derivationSteps.size(); }
    private:
        std::vector<DerivationStep> derivationSteps;

    public:
        Derivation() = default;
        explicit Derivation(std::vector<DerivationStep> derivationSteps) : derivationSteps(std::move(derivationSteps)) {}

        using const_iterator = decltype(derivationSteps)::const_iterator;
        using iterator = decltype(derivationSteps)::iterator;

        [[nodiscard]] const_iterator begin() const { return derivationSteps.begin(); }
        [[nodiscard]] const_iterator end() const { return derivationSteps.end(); }
        [[nodiscard]] iterator begin() { return derivationSteps.begin(); }
        [[nodiscard]] iterator end() { return derivationSteps.end(); }

    };

private:
    Derivation derivation;

public:
    void setDerivation(Derivation derivation_) { derivation = std::move(derivation_); }

    [[nodiscard]] Derivation const & getDerivation() const { return derivation; }
    [[nodiscard]] Derivation & getDerivation() { return derivation; }

    static InvalidityWitness fromErrorPath(ErrorPath const & errorPath, ChcDirectedGraph const & graph);
    static InvalidityWitness fromTransitionSystem(ChcDirectedGraph const & graph, std::size_t unrollings);

    void print(std::ostream & out, Logic & logic) const;
    void alethePrint(std::ostream & out, Logic & logic, const ChcDirectedHyperGraph& originalGraph,
                     std::vector<std::shared_ptr<Term>> originalAssertions, std::vector<std::vector<PTRef>> normalizingEqualities) const;
    std::vector<std::pair<std::string, std::string>> getInstPairs(int it, Logic & logic, const ChcDirectedHyperGraph& originalGraph, std::vector<PTRef> stepNormEq) const;
};

class ValidityWitness {
    std::unordered_map<PTRef, PTRef, PTRefHash> interpretations;
public:
    using definitions_t = decltype(interpretations);

    ValidityWitness() = default;

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

class NoWitness {
    std::string reason;
public:
    explicit NoWitness(std::string_view reason) : reason(reason) {}

    NoWitness() = default;
    NoWitness(NoWitness &&) = default;
    NoWitness & operator=(NoWitness &&) = default;

    [[nodiscard]] std::string_view getReason() const { return reason; }
};

enum class VerificationAnswer : char {SAFE, UNSAFE, UNKNOWN};

class VerificationResult {
    VerificationAnswer answer;
    std::variant<NoWitness, ValidityWitness, InvalidityWitness> witness;

public:
    VerificationResult(VerificationAnswer answer, ValidityWitness validityWitness)
        : answer(answer), witness(std::move(validityWitness)) {}

    VerificationResult(VerificationAnswer answer, InvalidityWitness invalidityWitness)
        : answer(answer), witness(std::move(invalidityWitness)) {}

    VerificationResult(VerificationAnswer answer, NoWitness noWitness)
        : answer(answer), witness(std::move(noWitness)) {}

    explicit VerificationResult(VerificationAnswer answer) : answer(answer), witness(NoWitness()) {}

    [[nodiscard]] VerificationAnswer getAnswer() const { return answer; }

    [[nodiscard]] bool hasWitness() const { return not std::holds_alternative<NoWitness>(witness); }

    [[nodiscard]] ValidityWitness const & getValidityWitness() const & { assert(answer == VerificationAnswer::SAFE); return std::get<ValidityWitness>(witness); }
    [[nodiscard]] const InvalidityWitness getInvalidityWitness() const & { assert(answer == VerificationAnswer::UNSAFE); return std::get<InvalidityWitness>(witness); }
    [[nodiscard]] std::string_view getNoWitnessReason() const & { assert(not hasWitness()); return std::get<NoWitness>(witness).getReason(); }

    ValidityWitness && getValidityWitness() && { assert(answer == VerificationAnswer::SAFE); return std::move(std::get<ValidityWitness>(witness)); }
    InvalidityWitness && getInvalidityWitness() && { assert(answer == VerificationAnswer::UNSAFE); return std::move(std::get<InvalidityWitness>(witness)); }

    void printWitness(std::ostream & out, Logic & logic) const;
    void printWitness_(std::ostream & out, Logic & logic, ChcDirectedHyperGraph const & originalGraph, std::vector<std::shared_ptr<Term>> originalAssertions,
                       Normalizer::Equalities const & normalizingEqualities) const;
};

struct TransitionSystemVerificationResult {
    VerificationAnswer answer;
    std::variant<std::size_t, PTRef> witness; // Unrolling number or state inductive invariant
};

VerificationResult translateTransitionSystemResult(TransitionSystemVerificationResult result, ChcDirectedGraph const & graph, TransitionSystem const & ts);

#endif // GOLEM_WITNESSES_H
