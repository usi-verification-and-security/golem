//
// Created by mambo on 8/29/23.
//

#ifndef GOLEM_ALETHETERMS_H
#define GOLEM_ALETHETERMS_H
#include "Term.h"
#include "Witnesses.h"
#include "graph/ChcGraph.h"
#include "utils/SmtSolver.h"
#include <memory>
#include <utility>

class Step {
public:
    enum stepType {
        ASSUME,
        STEP,
        ANCHOR
    };
private:
    int stepId;
    stepType type;
    std::vector<std::shared_ptr<Term>> clause;
    std::string rule;
    std::vector<int> premises;
    std::vector<std::pair<std::string, std::string>> args;
public :
    Step(int stepId, stepType type, std::vector<std::shared_ptr<Term>> clause, std::string rule, std::vector<int> premises) : type(type), stepId(stepId), clause(std::move(clause)), rule(std::move(rule)), premises(std::move(premises)) {}
    Step(int stepId, stepType type, std::vector<std::shared_ptr<Term>> clause, std::string rule, std::vector<std::pair<std::string, std::string>> args) : type(type), stepId(stepId), clause(std::move(clause)), rule(std::move(rule)), args(std::move(args)) {}
    Step(int stepId, stepType type, std::vector<std::shared_ptr<Term>> clause, std::string rule) : type(type), stepId(stepId), clause(std::move(clause)), rule(std::move(rule)) {}
    Step(int stepId, stepType type, std::vector<std::shared_ptr<Term>> clause) : type(type), stepId(stepId), clause(std::move(clause)), rule(" ") {}
    Step(int stepId, stepType type, std::string rule, std::vector<int> premises) : type(type), stepId(stepId), rule(std::move(rule)), premises(std::move(premises)) {}
    std::string printStepAlethe();
    std::string printStepIntermediate();
};

class Observer {
public:
    virtual void update(Step step) = 0;
};

class AlethePrintObserver : public Observer{
    std::ostream & out;
public:
    explicit AlethePrintObserver(std::ostream & out) : out(out){}
    void update(Step step) override{
        out << step.printStepAlethe();
    }
};

class IntermediatePrintObserver : public Observer{
    std::ostream & out;
public:
    explicit IntermediatePrintObserver(std::ostream & out) : out(out){}
    void update(Step step) override{
        out << step.printStepIntermediate();
    }
};

class StepHandler {

    InvalidityWitness::Derivation derivation;
    std::vector<std::shared_ptr<Term>> originalAssertions;
    Normalizer::Equalities const & normalizingEqualities;
    std::ostream & out;
    Logic & logic;
    ChcDirectedHyperGraph originalGraph;

    std::vector<Observer*> observers;

    int currStep = 0;
    int implicationStep;
    int transitivityStep;

    std::shared_ptr<Term> implicationRHS;
    std::shared_ptr<Term> implicationLHS;
    std::shared_ptr<Term> currTerm;
    std::vector<int> modusPonensSteps; //Modus Ponens Steps to derive the next node
    std::vector<int> simplificationSteps; //Simplification steps for final resolution of LHS

    std::shared_ptr<Term> originalLhsPrimaryBranch;

    // Visitors
    PrintVisitor printVisitor;
    SimplifyLocatorVisitor simplifyLocatorVisitor;
    OperateVisitor operateVisitor;
    SimplifyHelperVisitor helperVisitor;
    NonLinearVisitor nonLinearVisitor;
    NegatedAndVisitor negatedAndVisitor;
    OperateLetTermVisitor operateLetTermVisitor;
    LetLocatorVisitor letLocatorVisitor;
    RemoveUnusedVisitor removeUnusedVisitor;

public :

    StepHandler(InvalidityWitness::Derivation derivation, std::vector<std::shared_ptr<Term>> originalAssertions,
                Normalizer::Equalities const & normalizingEqualities, std::ostream & out,
                Logic & logic, ChcDirectedHyperGraph originalGraph) : derivation(std::move(derivation)), originalAssertions(std::move(originalAssertions)), normalizingEqualities(std::move(normalizingEqualities)), originalGraph(std::move(originalGraph)), out(out), logic(logic) {}


    std::vector<std::pair<std::string, std::string>> getInstPairs(int it, vec<Normalizer::Equality> const & stepNormEq);
    static std::vector<std::shared_ptr<Term>> packClause(const std::shared_ptr<Term>& term);
    static std::vector<std::shared_ptr<Term>> packClause(const std::shared_ptr<Term>& term1, const std::shared_ptr<Term>& term2);
    void buildAletheProof();
    void buildIntermediateProof();

    bool requiresCong();

    void instantiationSteps(int i);
    void assumptionSteps();
    void noCongRequiredSteps(std::vector<int> requiredMP);
    void notLhsPrimaryBranchSteps(std::shared_ptr<Term> simplification);
    void conjuctionSimplification(std::vector<int> requiredMP, std::shared_ptr<Term> simplification, std::shared_ptr<Term> termToSimplify, std::string simplificationRule);

    void notifyObservers(const Step& step){

        for (Observer *observer : observers) { // notify all observers
            observer->update(step);
        }
    }

};







#endif // GOLEM_ALETHETERMS_H
