/*
 * Copyright (c) 2023, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "CommonUtils.h"

#include "utils/SmtSolver.h"

using DerivationStep = InvalidityWitness::Derivation::DerivationStep;

InvalidityWitness::Derivation replaceSummarizingStep(
    InvalidityWitness::Derivation const & derivation,
    std::size_t stepIndex,
    std::vector<DirectedHyperEdge> const & replacedChain,
    DirectedHyperEdge const & replacingEdge,
    NonlinearCanonicalPredicateRepresentation const & predicateRepresentation,
    Logic & logic
    ) {
    assert(stepIndex < derivation.size());
    // Replace this step with the sequence of steps corresponding to the summarized chain
    std::vector<DerivationStep> newSteps;
    newSteps.reserve(stepIndex);
    // 1. Copy all the steps before the one to be replaced
    std::copy(derivation.begin(), derivation.begin() + stepIndex, std::back_inserter(newSteps));
    std::size_t firstShiftedIndex = newSteps.size();
    // 2. Replace the summarized step
    DerivationStep const & summarizedStep = derivation[stepIndex];
    // 2a. Compute instances for the summarized nodes
    // 2aa. Compute path constraint
    vec<PTRef> edgeConstraints;
    std::vector<DirectedEdge> simpleChain;
    EdgeConverter converter(logic, predicateRepresentation);
    std::transform(replacedChain.begin(), replacedChain.end(), std::back_inserter(simpleChain), converter);
    for (std::size_t i = 0; i < simpleChain.size(); ++i) {
        PTRef baseConstraint = simpleChain[i].fla.fla;
        edgeConstraints.push(TimeMachine(logic).sendFlaThroughTime(baseConstraint,i));
    }
    // 2ab Compute constraints for the end points
    TermUtils::substitutions_map subst;
    TermUtils utils(logic);
    assert(replacingEdge.from.size() == 1);
    assert(summarizedStep.premises.size() == 1);
    assert(logic.getSymRef(summarizedStep.derivedFact) == replacingEdge.to);
    assert(logic.getSymRef(derivation[summarizedStep.premises.front()].derivedFact) == replacingEdge.from[0]);
    VersionedPredicate versionPredicate(logic, predicateRepresentation);
    const PTRef sourcePredicate = versionPredicate(replacingEdge.from[0]);
    const PTRef targetPredicate = LinearPredicateVersioning(logic).sendPredicateThroughTime(versionPredicate(replacingEdge.to),simpleChain.size());
    utils.mapFromPredicate(targetPredicate, summarizedStep.derivedFact, subst);
    utils.mapFromPredicate(sourcePredicate, derivation[summarizedStep.premises.front()].derivedFact, subst);

    SMTSolver solverWrapper(logic, SMTSolver::WitnessProduction::ONLY_MODEL);
    auto & solver = solverWrapper.getCoreSolver();
    solver.insertFormula(logic.mkAnd(std::move(edgeConstraints)));
    for (auto const & [var,value] : subst) {
        assert(logic.isVar(var) and logic.isConstant(value));
        solver.insertFormula(logic.mkEq(var, value));
    }
    // 2ac Compute values for summarized predicates from model
    auto res = solver.check();
    if (res != s_True) { throw std::logic_error("Summarized chain should have been satisfiable!"); }
    auto model = solver.getModel();
    std::vector<PTRef> intermediatePredicateInstances;
    for (std::size_t i = 1; i < simpleChain.size(); ++i) {
        SymRef sourceSymbol = simpleChain[i].from;
        const PTRef predicate = LinearPredicateVersioning(logic).sendPredicateThroughTime(versionPredicate(sourceSymbol),i);
        auto vars = utils.predicateArgsInOrder(predicate);
        subst.clear();
        for (PTRef var : vars) {
            subst.insert({var, model->evaluate(var)});
        }
        intermediatePredicateInstances.push_back(utils.varSubstitute(predicate, subst));
    }
    // 2b. Create new steps based on intermediate predicate instances
    assert(not newSteps.empty());
    assert(summarizedStep.premises.size() == 1);
    for (std::size_t i = 0; i < intermediatePredicateInstances.size(); ++i) {
        DerivationStep step;
        step.derivedFact = intermediatePredicateInstances[i];
        step.index = newSteps.size();
        // MB: First of the new steps has the same premise as the summarized step
        step.premises = {i == 0 ? summarizedStep.premises.front() : newSteps.size() - 1};
        step.clauseId = simpleChain[i].id;
        newSteps.push_back(std::move(step));
    }
    std::size_t diff = intermediatePredicateInstances.size();
    // 2c. fix the step deriving the target of the summarized chain
    DerivationStep step = summarizedStep;
    assert(step.premises.size() == 1);
    assert(not newSteps.empty());
    step.premises[0] = newSteps.size() - 1;
    step.index += diff;
    step.clauseId = simpleChain.back().id;
    newSteps.push_back(std::move(step));
    // 3. copy all steps after the one replaced and update their premise indices
    std::transform(derivation.begin() + stepIndex + 1, derivation.end(), std::back_inserter(newSteps), [diff, firstShiftedIndex](auto const & step){
        auto newStep = step;
        for (auto & premiseIndex : newStep.premises) {
            if (premiseIndex >= firstShiftedIndex) {
                premiseIndex += diff;
            }
        }
        newStep.index += diff;
        return newStep;
    });
    // 4. Return the derivation
    InvalidityWitness::Derivation newDerivation(std::move(newSteps));
    return newDerivation;
}
