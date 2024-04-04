/*
 * Copyright (c) 2023, Matias Barandiaran <matias.barandiaran03@gmail.com>
 * Copyright (c) 2024, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "ProofSteps.h"
#include <memory>
#include <string>
#include <utility>

std::string Step::printStepAlethe() const {

    std::stringstream ss;
    ss << "(";

    if (type == ASSUME) {
        ss << "assume t";
    } else if (type == STEP) {
        ss << "step t";
    }

    ss << stepId;

    if (type != ASSUME) { ss << " (cl"; }

    if (not clause.empty()) {
        ss << " ";
        for (std::size_t i = 0; i < clause.size(); i++) {
            ss << clause[i]->printTerm();
            if (i != clause.size() - 1) { ss << " "; }
        }
    }

    if (type != ASSUME) { ss << ")"; }

    if (rule != " ") { ss << " :rule " << rule; }

    if (not premises.empty()) {
        ss << " :premises (";
        for (std::size_t i = 0; i < premises.size(); i++) {
            ss << "t" << premises[i];
            if (i != premises.size() - 1) { ss << " "; }
        }
        ss << ")";
    }

    if (not args.empty()) {
        ss << " :args (";
        for (std::size_t i = 0; i < args.size(); i++) {
            ss << "(:= " << args[i].first << " " << args[i].second << ")";
            if (i != args.size() - 1) { ss << " "; }
        }
        ss << ")";
    }

    ss << ")\n";

    return ss.str();
}

std::string Step::printStepIntermediate() const {

    PrintVisitor printVisitor;
    std::stringstream ss;

    ss << stepId << '\t';

    if (not clause.empty()) {
        ss << " ";
        for (auto const & arg : clause) {
            ss << arg->printTerm();
            ss << " ";
        }
    }

    if (not args.empty()) {
        ss << " :args (";
        for (std::size_t i = 0; i < args.size(); i++) {
            ss << "(:= " << args[i].first << " " << args[i].second << ")";
            if (i != args.size() - 1) { ss << " "; }
        }
        ss << ")";
    }

    if (not premises.empty()) {
        ss << " :premises ";
        for (auto premise : premises) {
            ss << premise << " ";
        }
    }

    ss << "\n";

    return ss.str();
}

std::vector<std::shared_ptr<Term>> packClause(std::shared_ptr<Term> const & term) {
    return std::vector<std::shared_ptr<Term>>{term};
}

std::vector<std::shared_ptr<Term>> packClause(std::shared_ptr<Term> const & term1,
                                              std::shared_ptr<Term> const & term2) {
    return std::vector<std::shared_ptr<Term>>{term1, term2};
}

std::vector<std::shared_ptr<Term>> packClause(std::shared_ptr<Term> const & term1, std::shared_ptr<Term> const & term2,
                                              std::shared_ptr<Term> const & term3) {
    return std::vector<std::shared_ptr<Term>>{term1, term2, term3};
}

void StepHandler::buildIntermediateProof() {

    auto derivationSize = derivation.size();

    for (std::size_t i = 0; i < derivationSize; ++i) {

        auto const & step = derivation[i];

        if (step.premises.empty()) { continue; }

        auto instPairs = getInstPairs(i, normalizingEqualities[step.clauseId.id]);
        currTerm = originalAssertions[step.clauseId.id];

        if (not instPairs.empty()) {
            InstantiateVisitor instantiateVisitor(instPairs);
            notifyObservers(Step(currentStep, Step::STEP, packClause(currTerm), "forall_inst", instPairs));
            currentStep++;

            currTerm = currTerm->accept(&instantiateVisitor);
        }

        notifyObservers(Step(currentStep, Step::STEP, packClause(currTerm)));
        currentStep++;

        std::stringstream premises;

        for (std::size_t j = 0; j < step.premises.size(); j++) {
            premises << logic.printTerm(derivation[step.premises[j]].derivedFact);
            if (j < step.premises.size() - 1) { premises << ' '; }
        }

        notifyObservers(
            Step(currentStep, Step::STEP,
                 packClause(std::make_shared<Op>(
                     "=>", packClause(std::make_shared<Terminal>(premises.str(), Term::VAR),
                                      std::make_shared<Terminal>(logic.printTerm(step.derivedFact), Term::VAR))))));
        currentStep++;

        std::vector<std::size_t> requiredMP;

        if (!modusPonensSteps.empty()) {
            // Get the necessary steps for modus ponens
            for (std::size_t premise : step.premises) {
                requiredMP.push_back(modusPonensSteps[premise - 1]);
            }
        }

        notifyObservers(Step(currentStep, Step::STEP,
                             packClause(std::make_shared<Terminal>(logic.printTerm(step.derivedFact), Term::VAR)),
                             "resolution", requiredMP));

        modusPonensSteps.push_back(currentStep);

        currentStep++;
    }
}

std::shared_ptr<Term> negate(std::shared_ptr<Term> const & arg) {
    return std::make_shared<Op>("not", std::vector<std::shared_ptr<Term>>{arg});
}

void StepHandler::buildAletheProof() {

    // Building assumptions
    assumptionSteps();

    auto derivationSize = derivation.size();

    // Iteration through derivations
    for (std::size_t i = 0; i < derivationSize; ++i) {
        auto const & step = derivation[i];

        if (step.premises.empty()) { continue; }

        std::vector<std::size_t> requiredMP;

        if (!modusPonensSteps.empty()) {
            // Get the necessary steps for modus ponens
            for (auto premise : step.premises) {
                requiredMP.push_back(modusPonensSteps[premise - 1]);
            }
        }

        currTerm = originalAssertions[step.clauseId.id];

        // Variable instantiation
        instantiationSteps(i); // pass the currTerm as an argument

        std::shared_ptr<Op> implication = std::dynamic_pointer_cast<Op>(currTerm);

        auto implicationLHS = implication->getArgs()[0];
        auto implicationRHS = implication->getArgs()[1];

        // Implication rule
        auto implicationStep = currentStep;
        notifyObservers(
            Step(currentStep, Step::STEP,
                 packClause(std::make_shared<Op>(
                                "not", packClause(std::make_shared<Op>(
                                           "!", packClause(implicationLHS, std::make_shared<Terminal>(
                                                                               ":named @impLHS" + std::to_string(i - 1),
                                                                               Terminal::UNDECLARED))))),
                            implicationRHS),
                 "implies", std::vector<std::size_t>{currentStep - 1}));

        currentStep++;

        std::shared_ptr<Term> renamedImpLHS =
            std::make_shared<Terminal>("@impLHS" + std::to_string(i - 1), Terminal::UNDECLARED);
        CongChainVisitor congChainVisitor(currentStep);

        // Casting implication to an operation, getting the LHS and calling the simplification visitor
        implicationLHS->accept(&congChainVisitor);
        // If it is empty, it means that the LHS was either a terminal or an application
        auto const & congruenceChainSteps = congChainVisitor.getSteps();
        std::size_t LHSderivationStep = 0;
        if (not congruenceChainSteps.empty()) {
            for (std::size_t j = 0; j < congruenceChainSteps.size() - 1; j++) {
                auto const & simpleStep = congruenceChainSteps[j];
                notifyObservers(Step(simpleStep.stepId, Step::STEP, packClause(simpleStep.clause), simpleStep.rule,
                                     simpleStep.premises));
            }

            // We deal with the last step separately, se we can use our name for LHS
            auto const & lastChainStep = congruenceChainSteps.back();
            auto const & simplifiedLHS = std::dynamic_pointer_cast<Op>(lastChainStep.clause)->getArgs()[1];
            auto originalSimplifiedEquality = std::make_shared<Op>("=", packClause(renamedImpLHS, simplifiedLHS));
            auto equalityStep = lastChainStep.stepId;
            notifyObservers(Step(lastChainStep.stepId, Step::STEP, packClause(originalSimplifiedEquality),
                                 lastChainStep.rule, lastChainStep.premises));
            currentStep = lastChainStep.stepId + 1;

            // now derive the original LHS
            auto simplifiedLHSderivationStep = deriveLHSWithoutConstraint(simplifiedLHS, std::move(requiredMP));
            // Now we have that LHS = simplifiedLHS and we have derived simplified LHS, from these we can derive the
            // original LHS
            notifyObservers(Step(currentStep, Step::STEP, packClause(renamedImpLHS, negate(simplifiedLHS)), "equiv2",
                                 std::vector<std::size_t>{equalityStep}));
            ++currentStep;
            notifyObservers(Step(currentStep, Step::STEP, packClause(renamedImpLHS), "resolution",
                                 std::vector<std::size_t>{simplifiedLHSderivationStep, currentStep - 1}));
            ++currentStep;
            LHSderivationStep = currentStep - 1;

        } else {
            LHSderivationStep = deriveLHSWithoutConstraint(implicationLHS, std::move(requiredMP));
        }

        // derive RHS
        auto RHSderivationStep = currentStep;
        notifyObservers(Step(currentStep, Step::STEP, packClause(implicationRHS), "resolution",
                             std::vector<std::size_t>{implicationStep, LHSderivationStep}));
        ++currentStep;
        CongChainVisitor rhsVisitor(currentStep);
        implicationRHS->accept(&rhsVisitor);
        auto const & simplificationStepsRHS = rhsVisitor.getSteps();
        if (not simplificationStepsRHS.empty()) {
            for (auto const & simpleStep : simplificationStepsRHS) {
                notifyObservers(Step(simpleStep.stepId, Step::STEP, packClause(simpleStep.clause), simpleStep.rule,
                                     simpleStep.premises));
                currentStep++;
            }
            auto equivalence = std::dynamic_pointer_cast<Op>(simplificationStepsRHS.back().clause);
            assert(equivalence->getArgs().size() == 2);
            auto simplifiedRHS = equivalence->getArgs()[1];
            assert(simplifiedRHS->printTerm() == logic.printTerm(step.derivedFact));
            // The last step is that RHS is equivalent to the simplified RHS. From that we can derive the simplified RHS
            notifyObservers(Step(currentStep, Step::STEP, packClause(negate(implicationRHS), simplifiedRHS), "equiv1",
                                 std::vector<std::size_t>{currentStep - 1}));
            ++currentStep;
            notifyObservers(Step(currentStep, Step::STEP, packClause(simplifiedRHS), "resolution",
                                 std::vector<std::size_t>{currentStep - 1, RHSderivationStep}));
            ++currentStep;
        }

        modusPonensSteps.push_back(currentStep - 1);
    }

    notifyObservers(Step(currentStep, Step::STEP,
                         packClause(std::make_shared<Terminal>("(not false)", Term::UNDECLARED)), "false"));

    currentStep++;
    // Get empty clause
    notifyObservers(
        Step(currentStep, Step::STEP, "resolution", std::vector<std::size_t>{currentStep - 2, currentStep - 1}));
}

void StepHandler::instantiationSteps(std::size_t i) {

    auto const & step = derivation[i];

    std::shared_ptr<Term> assumptionReNamedTerm =
        std::make_shared<Terminal>("@a" + std::to_string(step.clauseId.id), Terminal::UNDECLARED);
    std::shared_ptr<Term> instantiationReNamedTerm =
        std::make_shared<Terminal>("@i" + std::to_string(i - 1), Terminal::UNDECLARED);

    std::shared_ptr<Term> unusedRem = currTerm->accept(&removeUnusedVisitor);

    std::size_t quantStep = step.clauseId.id;

    if (unusedRem->printTerm() != currTerm->printTerm()) {

        notifyObservers(Step(currentStep, Step::STEP,
                             packClause(std::make_shared<Op>("=", packClause(assumptionReNamedTerm, unusedRem))),
                             "qnt_rm_unused"));

        currentStep++;

        notifyObservers(Step(currentStep, Step::STEP,
                             packClause(std::make_shared<Op>("not", packClause(assumptionReNamedTerm)), unusedRem),
                             "equiv1", std::vector<std::size_t>{currentStep - 1}));

        currentStep++;

        notifyObservers(Step(currentStep, Step::STEP, packClause(unusedRem), "resolution",
                             std::vector<std::size_t>{quantStep, currentStep - 1}));

        currentStep++;

        currTerm = unusedRem;
        assumptionReNamedTerm = unusedRem;
        quantStep = currentStep - 1;
    }

    // Getting the instantiated variable-value pairs
    std::vector<std::pair<std::string, std::string>> instPairs =
        getInstPairs(i, normalizingEqualities[step.clauseId.id]);

    if (not instPairs.empty()) {
        InstantiateVisitor instantiateVisitor(instPairs);

        notifyObservers(Step(
            currentStep, Step::STEP,
            packClause(std::make_shared<Op>(
                "or",
                packClause(std::make_shared<Op>("not", packClause(assumptionReNamedTerm)),
                           std::make_shared<Op>("!", packClause(currTerm->accept(&instantiateVisitor),
                                                                std::make_shared<Terminal>(
                                                                    ":named " + instantiationReNamedTerm->printTerm(),
                                                                    Terminal::UNDECLARED)))))),
            "forall_inst", instPairs));

        currentStep++;

        notifyObservers(
            Step(currentStep, Step::STEP,
                 packClause(std::make_shared<Op>("not", packClause(assumptionReNamedTerm)), instantiationReNamedTerm),
                 "or", std::vector<std::size_t>{currentStep - 1}));

        currentStep++;

        currTerm = currTerm->accept(&instantiateVisitor);

        notifyObservers(Step(currentStep, Step::STEP, packClause(instantiationReNamedTerm), "resolution",
                             std::vector<std::size_t>{currentStep - 1, quantStep}));

        currentStep++;
    }
}

void StepHandler::assumptionSteps() {

    for (auto & assertion : originalAssertions) {
        Term * potentialLet = assertion->accept(&letLocatorVisitor);
        while (potentialLet != nullptr) {
            auto simplifiedLet = potentialLet->accept(&operateLetTermVisitor);
            SimplifyVisitor simplifyLetTermVisitor(simplifiedLet, potentialLet);
            assertion = assertion->accept(&simplifyLetTermVisitor);
            potentialLet = assertion->accept(&letLocatorVisitor);
        }
        notifyObservers(
            Step(currentStep, Step::ASSUME,
                 packClause(std::make_shared<Op>(
                     "!", packClause(assertion, std::make_shared<Terminal>(":named @a" + std::to_string(currentStep),
                                                                           Terminal::UNDECLARED))))));

        currentStep++;
    }
}

// Returns the step id that derived the unit clause containing simplifiedLHS
std::size_t StepHandler::deriveLHSWithoutConstraint(std::shared_ptr<Term> const & simplifiedLHS,
                                                    std::vector<std::size_t> predicatePremises) {
    if (simplifiedLHS->getTermType() == Term::OP) { // conjunction of predicates
        auto predicateConjunction = std::dynamic_pointer_cast<Op>(simplifiedLHS);
        assert(predicateConjunction->getOp() == "and");

        std::vector<std::shared_ptr<Term>> andNegArgs;
        andNegArgs.reserve(predicateConjunction->getArgs().size() + 1);
        andNegArgs.push_back(predicateConjunction);
        for (auto const & arg : predicateConjunction->getArgs()) {
            andNegArgs.push_back(negate(arg));
        }
        notifyObservers(Step(currentStep, Step::STEP, std::move(andNegArgs), "and_neg", std::vector<std::size_t>{}));
        currentStep++;

        predicatePremises.push_back(currentStep - 1);
        notifyObservers(
            Step(currentStep, Step::STEP, packClause(simplifiedLHS), "resolution", std::move(predicatePremises)));
        return currentStep++;
    } else if (simplifiedLHS->getTermType() == Term::APP) { // single predicate
        assert(predicatePremises.size() == 1);
        return predicatePremises[0];
    } else if (simplifiedLHS->getTermType() == Term::TERMINAL) { // no predicate => constant true
        assert(simplifiedLHS->printTerm() == "true");
        return getOrCreateTrueStep();
    } else {
        assert(false);
        throw std::logic_error("Unexpected situation during proof building");
    }
}

std::vector<std::pair<std::string, std::string>>
StepHandler::getInstPairs(std::size_t stepIndex, vec<Normalizer::Equality> const & stepNormEq) {
    struct VarValPair {
        PTRef var;
        PTRef val;
    };
    std::unordered_set<PTRef, PTRefHash> processedOriginalArguments;
    std::vector<VarValPair> instPairsBeforeNormalization;
    std::vector<VarValPair> instPairsAfterNormalization;

    auto const & step = derivation[stepIndex];

    TermUtils utils(logic);

    auto premises = step.premises;
    premises.erase(std::remove(premises.begin(), premises.end(), 0), premises.end());

    std::unordered_map<SymRef, std::size_t, SymRefHash> vertexInstance;

    auto processFormalArgumentsWithValues = [&](std::vector<PTRef> const & formalArgs,
                                                std::vector<PTRef> const & concreteArgs) {
        assert(concreteArgs.size() == formalArgs.size());
        for (std::size_t m = 0; m < formalArgs.size(); m++) {
            for (auto const & equality : stepNormEq) {
                if (equality.normalizedVar == formalArgs[m]) {
                    assert(logic.isConstant(concreteArgs[m]));
                    instPairsAfterNormalization.push_back({equality.normalizedVar, concreteArgs[m]});
                    auto it = processedOriginalArguments.find(equality.originalArg);
                    if (it == processedOriginalArguments.end()) {
                        processedOriginalArguments.insert(equality.originalArg);
                        instPairsBeforeNormalization.push_back({equality.originalArg, concreteArgs[m]});
                    }
                }
            }
        }
    };

    for (std::size_t premise : premises) {
        auto concreteArgs = utils.predicateArgsInOrder(derivation[premise].derivedFact);
        auto targetVertex = originalGraph.getEdge(derivation[premise].clauseId).to;

        auto instance = vertexInstance[targetVertex]++;
        PTRef predicateInstance = originalGraph.getStateVersion(targetVertex, instance);

        auto formalArgs = utils.predicateArgsInOrder(predicateInstance);
        processFormalArgumentsWithValues(formalArgs, concreteArgs);
    }
    // Target variables instantiation
    auto concreteArgs = utils.predicateArgsInOrder(step.derivedFact);
    auto targetVertex = originalGraph.getEdge(step.clauseId).to;
    PTRef clauseHead = originalGraph.getNextStateVersion(targetVertex);
    auto formalArgs = utils.predicateArgsInOrder(clauseHead);
    processFormalArgumentsWithValues(formalArgs, concreteArgs);

    // Compute values for possible auxiliary variables
    PTRef originalConstraint = originalGraph.getEdgeLabel(step.clauseId);
    TermUtils::substitutions_map substitutionsMap;
    for (auto const & varVal : instPairsAfterNormalization) {
        substitutionsMap.insert({varVal.var, varVal.val});
    }
    auto auxVars = matchingSubTerms(logic, originalConstraint, [&](PTRef term) {
        return logic.isVar(term) and substitutionsMap.find(term) == substitutionsMap.end();
    });

    if (auxVars.size() > 0) {
        PTRef instantiatedConstraint = utils.varSubstitute(originalConstraint, substitutionsMap);
        assert(instantiatedConstraint != logic.getTerm_false());
        // Find values for auxiliary variables
        SMTSolver solver(logic, SMTSolver::WitnessProduction::ONLY_MODEL);
        solver.getCoreSolver().insertFormula(instantiatedConstraint);
        auto res = solver.getCoreSolver().check();
        if (res != s_True) {
            assert(false);
            throw std::logic_error("Formula should have been satisfiable");
        }
        auto model = solver.getCoreSolver().getModel();
        for (PTRef auxVar : auxVars) {
            PTRef val = model->evaluate(auxVar);
            auto it = std::find_if(stepNormEq.begin(), stepNormEq.end(),
                                   [&](auto const & eq) { return eq.normalizedVar == auxVar; });
            if (it == stepNormEq.end()) {
                throw std::logic_error("Auxiliary variable should have been found in normalizing equalities");
            }
            PTRef originalVar = it->originalArg;
            if (processedOriginalArguments.find(originalVar) == processedOriginalArguments.end()) {
                processedOriginalArguments.insert(originalVar);
                instPairsBeforeNormalization.push_back({originalVar, val});
            }
        }
    }

    // Arguments before normalization can be arbitrary terms
    // For now we assume we have all the variables as arguments of some predicate in the original system.
    // Thus, we can ignore non-variable terms.
    // NOTE: This approach does not work in all cases, but should work in all reasonable cases
    std::vector<std::pair<std::string, std::string>> res;
    res.reserve(instPairsBeforeNormalization.size());
    for (auto && [var, val] : instPairsBeforeNormalization) {
        if (logic.isVar(var)) { res.emplace_back(logic.getSymName(var), logic.printTerm(val)); }
    }
    return res;
}

std::size_t StepHandler::getOrCreateTrueStep() {
    if (trueRuleStep == 0) {
        notifyObservers(Step(currentStep, Step::STEP,
                             packClause(std::make_shared<Terminal>("true", Terminal::terminalType::BOOL)), "true"));
        trueRuleStep = currentStep;
        ++currentStep;
    }
    return trueRuleStep;
}
