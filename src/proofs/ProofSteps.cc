/*
 * Copyright (c) 2023, Matias Barandiaran <matias.barandiaran03@gmail.com>
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

std::vector<std::shared_ptr<Term>> StepHandler::packClause(std::shared_ptr<Term> const & term) {
    std::vector<std::shared_ptr<Term>> clause;
    clause.push_back(term);
    return clause;
}

std::vector<std::shared_ptr<Term>> StepHandler::packClause(std::shared_ptr<Term> const & term1,
                                                           std::shared_ptr<Term> const & term2) {
    std::vector<std::shared_ptr<Term>> clause;
    clause.push_back(term1);
    clause.push_back(term2);
    return clause;
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

        implicationLHS = implication->getArgs()[0];
        implicationRHS = std::make_shared<Terminal>(logic.printTerm(step.derivedFact), Term::VAR);

        std::shared_ptr<Term> renamedImpLHS =
            std::make_shared<Terminal>("@impLHS" + std::to_string(i - 1), Terminal::UNDECLARED);

        // Implication rule

        notifyObservers(
            Step(currentStep, Step::STEP,
                 packClause(std::make_shared<Op>(
                                "not", packClause(std::make_shared<Op>(
                                           "!", packClause(implicationLHS, std::make_shared<Terminal>(
                                                                               ":named @impLHS" + std::to_string(i - 1),
                                                                               Terminal::UNDECLARED))))),
                            implicationRHS),
                 "implies", std::vector<std::size_t>{currentStep - 1}));

        std::size_t implicationStep = currentStep;

        currentStep++;

        CongChainVisitor congChainVisitor(currentStep);

        // Casting implication to an operation, getting the LHS and calling the simplification visitor
        std::dynamic_pointer_cast<Op>(currTerm)->getArgs()[0]->accept(&congChainVisitor);
        // If it is empty, it means that the LHS was either a terminal or an application
        auto const & congruenceChainSteps = congChainVisitor.getSteps();
        if (not congruenceChainSteps.empty()) {
            for (std::size_t j = 0; j < congruenceChainSteps.size() - 1; j++) {
                auto const & simpleStep = congruenceChainSteps[j];
                notifyObservers(Step(simpleStep.stepId, Step::STEP, packClause(simpleStep.clause), simpleStep.rule,
                                     simpleStep.premises));
            }
        }

        std::shared_ptr<Term> lastClause;
        // Checking if we are dealing with a conjunction
        if (implicationLHS->getTermType() == Term::OP) {
            // renaming LHS for last chain step
            assert(not congruenceChainSteps.empty());
            auto const & lastChainStep = congruenceChainSteps.back();
            lastClause = lastChainStep.clause;
            notifyObservers(
                Step(lastChainStep.stepId, Step::STEP,
                     packClause(std::make_shared<Op>(
                         "=", packClause(renamedImpLHS, std::dynamic_pointer_cast<Op>(lastClause)->getArgs()[1]))),
                     lastChainStep.rule, lastChainStep.premises));
            currentStep = lastChainStep.stepId + 1;
            if (std::dynamic_pointer_cast<Op>(implicationLHS)->getOp() == "and") {
                // Final parent conjunction simplification
                conjunctionSimplification(requiredMP, lastClause, implicationStep, renamedImpLHS);
                continue;
            }
        } else {
            lastClause = implicationLHS;
        }
        // If it is not, we simplify with a different procedure
        directSimplification(requiredMP, implicationStep, lastClause, renamedImpLHS);
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

void StepHandler::directSimplification(std::vector<std::size_t> requiredMP, std::size_t implicationStep,
                                       std::shared_ptr<Term> const & lastClause,
                                       std::shared_ptr<Term> const & renamedImpLHS) {

    if (implicationLHS->getTermType() == Term::OP) {

        auto simplification = std::dynamic_pointer_cast<Op>(lastClause)->getArgs()[1];

        notifyObservers(Step(currentStep, Step::STEP,
                             packClause(renamedImpLHS, std::make_shared<Op>("not", packClause(simplification))),
                             "equiv2", std::vector<std::size_t>{currentStep - 1}));

        currentStep++;

        if (simplification->getTerminalType() == Terminal::BOOL) {
            assert(simplification->printTerm() == "true");
            stepReusage(simplification);
            notifyObservers(Step(currentStep, Step::STEP, packClause(renamedImpLHS), "resolution",
                                 std::vector<std::size_t>{currentStep - 2, currentStep - 1}));

            currentStep++;
            notifyObservers(Step(currentStep, Step::STEP, packClause(implicationRHS), "resolution",
                                 std::vector<std::size_t>{implicationStep, currentStep - 1}));
            modusPonensSteps.push_back(currentStep);
            currentStep++;
        }
    } else {

        if (implicationLHS->getTermType() == Term::APP) {

            requiredMP.push_back(currentStep - 1);

            notifyObservers(Step(currentStep, Step::STEP, packClause(implicationRHS), "resolution", requiredMP));

            modusPonensSteps.push_back(currentStep);

            currentStep++;

        } else if (implicationLHS->getTermType() == Term::TERMINAL) {

            notifyObservers(Step(currentStep, Step::STEP, packClause(renamedImpLHS), "true"));

            currentStep++;

            notifyObservers(Step(currentStep, Step::STEP, packClause(implicationRHS), "resolution",
                                 std::vector<std::size_t>{implicationStep, currentStep - 1}));

            modusPonensSteps.push_back(currentStep);

            currentStep++;
        }
    }
}

void StepHandler::conjunctionSimplification(std::vector<std::size_t> requiredMP,
                                            std::shared_ptr<Term> const & lastClause, std::size_t implicationStep,
                                            std::shared_ptr<Term> const & renamedImpLHS) {

    auto termToSimplify = std::dynamic_pointer_cast<Op>(lastClause)->getArgs()[0];
    auto simplification = std::dynamic_pointer_cast<Op>(lastClause)->getArgs()[1];

    notifyObservers(Step(currentStep, Step::STEP,
                         packClause(renamedImpLHS, std::make_shared<Op>("not", packClause(simplification))), "equiv2",
                         std::vector<std::size_t>{currentStep - 1}));

    currentStep++;

    // Check if we are dealing with a non linear case
    if (std::dynamic_pointer_cast<Op>(termToSimplify)->nonLinearity()) {
        notifyObservers(Step(
            currentStep, Step::STEP,
            packClause(simplification,
                       std::make_shared<Terminal>(
                           std::dynamic_pointer_cast<Op>(simplification)->nonLinearSimplification(), Term::UNDECLARED)),
            "and_neg"));

        currentStep++;

        notifyObservers(
            Step(currentStep, Step::STEP,
                 packClause(renamedImpLHS, std::make_shared<Terminal>(
                                               std::dynamic_pointer_cast<Op>(simplification)->nonLinearSimplification(),
                                               Term::UNDECLARED)),
                 "resolution", std::vector<std::size_t>{currentStep - 2, currentStep - 1}));

        requiredMP.push_back(currentStep);

        currentStep++;
    } else {
        requiredMP.push_back(currentStep - 1);
    }

    if (simplification->printTerm() == "true") {

        stepReusage(simplification);

        notifyObservers(Step(currentStep, Step::STEP, packClause(renamedImpLHS), "resolution",
                             std::vector<std::size_t>{currentStep - 2, currentStep - 1}));

        currentStep++;

    } else {

        notifyObservers(Step(currentStep, Step::STEP, packClause(renamedImpLHS), "resolution", requiredMP));

        currentStep++;
    }

    notifyObservers(Step(currentStep, Step::STEP, packClause(implicationRHS), "resolution",
                         std::vector<std::size_t>{implicationStep, currentStep - 1}));

    modusPonensSteps.push_back(currentStep);

    currentStep++;
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

    auto processFormalArgumentsWithValues = [&](std::vector<PTRef> const & formalArgs, std::vector<PTRef> const & concreteArgs) {
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

    std::vector<std::pair<std::string, std::string>> res;
    std::transform(instPairsBeforeNormalization.begin(), instPairsBeforeNormalization.end(), std::back_inserter(res),
                   [&](auto const & varVal) {
                       assert(logic.isVar(varVal.var));
                       std::string varName = logic.getSymName(varVal.var);
                       return std::make_pair(varName, logic.printTerm(varVal.val));
                   });
    return res;
}

void StepHandler::stepReusage(std::shared_ptr<Term> const & term) {
    std::string strTerm = term->printTerm();
    assert(strTerm == "true");
    if (trueRuleStep == 0) {
        notifyObservers(Step(currentStep, Step::STEP, packClause(term), "true"));
        trueRuleStep = currentStep;
    } else {
        notifyObservers(Step(currentStep, Step::STEP, packClause(implicationLHS), "resolution",
                             std::vector<std::size_t>{currentStep - 1, trueRuleStep}));
    }
    currentStep++;
}
