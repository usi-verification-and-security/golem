/*
 * Copyright (c) 2020-2022, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef GOLEM_WITNESSES_H
#define GOLEM_WITNESSES_H

#include "ChcGraph.h"

#include "osmt_solver.h"

class WitnessModel {
    std::unique_ptr<Model> model;
public:
    WitnessModel() = default;
    explicit WitnessModel(std::unique_ptr<Model> model) : model(std::move(model)) {}

    PTRef evaluate(PTRef fla) const { return model->evaluate(fla); }
};

class InvalidityWitness {
public:
    class ErrorPath {
        std::vector<EId> path;
    public:
        std::vector<EId> getEdges() const { return path; }
        void setPath(std::vector<EId> npath) { this->path = std::move(npath); }
        bool isEmpty() const { return path.empty(); }
    };
    void setErrorPath(ErrorPath path) { errorPath = std::move(path); }

    ErrorPath const & getErrorPath() const { return errorPath; }

    static InvalidityWitness fromTransitionSystem(ChcDirectedGraph const & graph, std::size_t unrollings);

private:
    ErrorPath errorPath;
};

class SystemInvalidityWitness {
public:
    class Derivation { // Terminology based on Interpolation Strength Revisited
        // Derivation rule is 'positive hyper-resolution'
        // Antecedents are: one nucleus (with n negative literals) and n satellites, each with single positive literal
    public:
    	struct DerivationStep {
            enum class StepType {INPUT, DERIVED};
            std::size_t index;
            StepType type;
            std::vector<std::size_t> satellites;
            std::size_t nucleus;
            ChClause clause;
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
    WitnessModel model;

public:
    void setModel(WitnessModel model_) { model = std::move(model_); }
    void setDerivation(Derivation derivation_) { derivation = std::move(derivation_); }

    Derivation const & getDerivation() const { return derivation; }
    WitnessModel const & getModel() const { return model; }

    void print(std::ostream & out, Logic & logic) const;
};

SystemInvalidityWitness graphToSystemInvalidityWitness(InvalidityWitness const & witness, ChcDirectedGraph & graph);

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
};

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
    SystemVerificationResult(GraphVerificationResult && graphResult, ChcDirectedHyperGraph & graph) {
        answer = graphResult.getAnswer();
        if (answer == VerificationResult::SAFE) {
            validityWitness = graphResult.getValidityWitness();
        }
        if (answer == VerificationResult::UNSAFE) {
            if (graph.isNormalGraph()) {
                auto simpleGraph = graph.toNormalGraph();
                invalidityWitness = graphToSystemInvalidityWitness(graphResult.getInvalidityWitness(), *simpleGraph);
            }
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

#endif // GOLEM_WITNESSES_H
