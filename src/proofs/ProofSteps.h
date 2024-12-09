/*
 * Copyright (c) 2023, Matias Barandiaran <matias.barandiaran03@gmail.com>
 * Copyright (c) 2024, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef GOLEM_PROOFSTEPS_H
#define GOLEM_PROOFSTEPS_H

#include "Term.h"
#include "Witnesses.h"
#include "graph/ChcGraph.h"
#include "utils/SmtSolver.h"
#include <memory>
#include <utility>

class Step {
public:
    enum class StepType : char { ASSUME, STEP, ANCHOR };
    struct Premises {
        Premises() = default;
        explicit Premises(std::size_t premise) : premises{premise} {}
        explicit Premises(std::vector<std::size_t> premises) : premises{std::move(premises)} {}
        Premises(std::initializer_list<std::size_t> premises) : premises{premises} {}
        std::vector<std::size_t> premises;
    };

private:
    std::size_t stepId;
    StepType type;
    std::vector<std::shared_ptr<Term>> clause;
    std::string rule;
    Premises premises;
    std::vector<std::pair<std::string, std::string>> args;

public:
    Step(std::size_t stepId, StepType type, std::vector<std::shared_ptr<Term>> clause, std::string rule,
         Premises premises)
        : stepId(stepId), type(type), clause(std::move(clause)), rule(std::move(rule)), premises(std::move(premises)) {}
    Step(std::size_t stepId, StepType type, std::vector<std::shared_ptr<Term>> clause, std::string rule,
         std::vector<std::pair<std::string, std::string>> args)
        : stepId(stepId), type(type), clause(std::move(clause)), rule(std::move(rule)), args(std::move(args)) {}
    Step(std::size_t stepId, StepType type, std::vector<std::shared_ptr<Term>> clause, std::string rule)
        : stepId(stepId), type(type), clause(std::move(clause)), rule(std::move(rule)) {}
    Step(std::size_t stepId, StepType type, std::vector<std::shared_ptr<Term>> clause)
        : stepId(stepId), type(type), clause(std::move(clause)), rule(" ") {}

    [[nodiscard]] std::string printStepAlethe() const;
    [[nodiscard]] std::string printStepIntermediate() const;
};

class Observer {
public:
    virtual void update(Step const & step) = 0;
    virtual ~Observer() = default;
};

class AlethePrintObserver : public Observer {
    std::ostream & out;

public:
    explicit AlethePrintObserver(std::ostream & out) : out(out) {}
    void update(Step const & step) override { out << step.printStepAlethe(); }
};

class [[maybe_unused]] CountingObserver : public Observer {
    std::size_t count = 0;

public:
    CountingObserver() = default;
    ~CountingObserver() override { std::cout << count << std::endl; }
    void update(Step const &) override { ++count; }
};

class IntermediatePrintObserver : public Observer {
    std::ostream & out;

public:
    explicit IntermediatePrintObserver(std::ostream & out) : out(out) {}
    void update(Step const & step) override { out << step.printStepIntermediate(); }
};

class StepHandler {

    InvalidityWitness::Derivation derivation;
    std::vector<std::shared_ptr<Term>> originalAssertions;
    Normalizer::Equalities const & normalizingEqualities;
    Logic & logic;
    ChcDirectedHyperGraph originalGraph;

    std::vector<Observer *> observers;

    std::size_t currentStep = 0;
    std::size_t trueRuleStep = 0;

public:
    StepHandler(InvalidityWitness::Derivation derivation, std::vector<std::shared_ptr<Term>> originalAssertions,
                Normalizer::Equalities const & normalizingEqualities, Logic & logic,
                ChcDirectedHyperGraph originalGraph)
        : derivation(std::move(derivation)), originalAssertions(std::move(originalAssertions)),
          normalizingEqualities(normalizingEqualities), logic(logic), originalGraph(std::move(originalGraph)) {}

    void buildAletheProof();
    void buildIntermediateProof();

    void registerObserver(Observer * observer) { observers.push_back(observer); }

    void deRegisterObserver(Observer const * observer) {
        if (const auto it = std::find(observers.begin(), observers.end(), observer); it != observers.end()) {
            observers.erase(it);
        }
    }

private:
    using InstantiationPairs = std::vector<std::pair<std::string, std::string>>;
    using TermPtr = std::shared_ptr<Term>;
    InstantiationPairs getInstPairs(std::size_t it, vec<Normalizer::Equality> const & stepNormEq);

    /** Records steps to derive instantiated term and returns this term */
    TermPtr instantiationSteps(std::size_t i, TermPtr quantifiedTerm);
    void buildAssumptionSteps();
    std::size_t deriveLHSWithoutConstraint(std::shared_ptr<Term> const & simplifiedLHS,
                                           std::vector<std::size_t> predicatePremises);

    std::size_t getOrCreateTrueStep();

    void notifyObservers(Step const & step) const {
        for (Observer * observer : observers) { // notify all observers
            observer->update(step);
        }
    }

    std::size_t lastStep() const { return currentStep - 1; }
    void recordStep(std::vector<std::shared_ptr<Term>> && clause, std::string rule, Step::Premises && premises);
    void recordForallInstStep(std::vector<std::shared_ptr<Term>> && clause, InstantiationPairs && instantiationPairs);
    void recordAssumption(std::vector<std::shared_ptr<Term>> && clause);

    /** Simplifies term by evaluating operations on constants, records the simplification steps */
    using SimplifyResult = std::optional<std::pair<TermPtr, std::size_t>>; // Simplified term + congruence step id
    SimplifyResult simplify(TermPtr const & term, std::optional<TermPtr> name = std::nullopt);
    SimplifyResult shortCircuitSimplifyITE(std::shared_ptr<Op> const & ite);
    // Assumes that arguments are already simplified
    TermPtr simplifyOpDirect(std::shared_ptr<Op> const & op);
};

#endif // GOLEM_PROOFSTEPS_H
