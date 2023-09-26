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
        for (const auto & arg : clause) {
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

std::vector<std::shared_ptr<Term>> StepHandler::packClause(const std::shared_ptr<Term> & term) {
    std::vector<std::shared_ptr<Term>> clause;
    clause.push_back(term);
    return clause;
}

std::vector<std::shared_ptr<Term>> StepHandler::packClause(const std::shared_ptr<Term> & term1,
                                                           const std::shared_ptr<Term> & term2) {
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
        InstantiateVisitor instantiateVisitor(instPairs);
        currTerm = originalAssertions[step.clauseId.id];

        if (not instPairs.empty()) {

            notifyObservers(Step(currStep, Step::STEP, packClause(currTerm), "forall_inst", instPairs));
            currStep++;

            currTerm = currTerm->accept(&instantiateVisitor);
        }

        notifyObservers(Step(currStep, Step::STEP, packClause(currTerm)));
        currStep++;

        std::stringstream premises;

        for (std::size_t i = 0; i < step.premises.size(); i++) {
            premises << logic.printTerm(derivation[step.premises[i]].derivedFact);
            if (i < step.premises.size() - 1) { premises << ' '; }
        }

        notifyObservers(
            Step(currStep, Step::STEP,
                 packClause(std::make_shared<Op>(
                     "=>", packClause(std::make_shared<Terminal>(premises.str(), Term::VAR),
                                      std::make_shared<Terminal>(logic.printTerm(step.derivedFact), Term::VAR))))));
        currStep++;

        std::vector<int> requiredMP;

        if (!modusPonensSteps.empty()) {
            // Get the necessary steps for modus ponens
            for (unsigned long premise : step.premises) {
                requiredMP.push_back(modusPonensSteps[(int)premise - 1]);
            }
        }

        notifyObservers(Step(currStep, Step::STEP,
                             packClause(std::make_shared<Terminal>(logic.printTerm(step.derivedFact), Term::VAR)),
                             "resolution", requiredMP));

        modusPonensSteps.push_back(currStep);

        currStep++;
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

        std::vector<int> requiredMP;

        if (!modusPonensSteps.empty()) {
            // Get the necessary steps for modus ponens
            for (std::size_t i = 0; i < step.premises.size(); i++) {
                requiredMP.push_back(modusPonensSteps[(int)step.premises[i] - 1]);
            }
        }

        currTerm = originalAssertions[step.clauseId.id];

        // Variable instantiation
        instantiationSteps(i); // pass the currTerm as an argument

        std::shared_ptr<Op> implication = std::dynamic_pointer_cast<Op>(currTerm);

        implicationLHS = implication->getArgs()[0]->accept(&copyVisitor);
        implicationRHS = std::make_shared<Terminal>(logic.printTerm(step.derivedFact), Term::VAR);

        std::shared_ptr<Term> renamedImpLHS =
            std::make_shared<Terminal>("@impLHS" + std::to_string(i - 1), Terminal::UNDECLARED);

        // Implication rule

        notifyObservers(
            Step(currStep, Step::STEP,
                 packClause(std::make_shared<Op>(
                                "not", packClause(std::make_shared<Op>(
                                           "!", packClause(implicationLHS, std::make_shared<Terminal>(
                                                                               ":named @impLHS" + std::to_string(i - 1),
                                                                               Terminal::UNDECLARED))))),
                            implicationRHS),
                 "implies", std::vector<int>{currStep - 1}));

        int implicationStep = currStep;

        currStep++;

        // Checking if height of LHS is greater than 1
        if (not requiresCong()) {
            // If it is not, the proof is shorter
            noCongRequiredSteps(requiredMP, implicationStep, renamedImpLHS);

        } else {
            // If it is, we require additional steps

            CongChainVisitor congChainVisitor(currStep);

            // Casting imlication to an operation
            std::dynamic_pointer_cast<Op>(currTerm)->getArgs()[0]->accept(&congChainVisitor);

            for (const auto & simpleStep : congChainVisitor.getSteps()) {
                notifyObservers(Step(simpleStep.stepId, Step::STEP, packClause(simpleStep.clause), simpleStep.rule,
                                     simpleStep.premises));
            }

            auto lastChainStep = congChainVisitor.getSteps()[congChainVisitor.getSteps().size() - 1];
            currStep = lastChainStep.stepId + 1;
            auto lastClause = lastChainStep.clause;

            // Final parent conjunction simplification
            conjunctionSimplification(requiredMP, lastClause, implicationStep, renamedImpLHS);
        }
    }

    notifyObservers(
        Step(currStep, Step::STEP, packClause(std::make_shared<Terminal>("(not false)", Term::UNDECLARED)), "false"));

    currStep++;
    // Get empty clause
    notifyObservers(Step(currStep, Step::STEP, "resolution", std::vector<int>{currStep - 2, currStep - 1}));
}

bool StepHandler::requiresCong() {

    if (implicationLHS->getTermType() == Term::TERMINAL or implicationLHS->getTermType() == Term::APP) {
        return false;
    } else {
        for (auto arg : std::dynamic_pointer_cast<Op>(implicationLHS)->getArgs()) {
            if (not(arg->getTermType() == Term::TERMINAL or arg->getTermType() == Term::APP)) { return true; }
        }
    }
    return false;
}

void StepHandler::instantiationSteps(int i) {

    auto const & step = derivation[i];

    std::shared_ptr<Term> assumptionReNamedTerm =
        std::make_shared<Terminal>("@a" + std::to_string(step.clauseId.id), Terminal::UNDECLARED);
    std::shared_ptr<Term> instantiationReNamedTerm =
        std::make_shared<Terminal>("@i" + std::to_string(i - 1), Terminal::UNDECLARED);

    std::shared_ptr<Term> unusedRem = currTerm->accept(&removeUnusedVisitor);

    int quantStep = static_cast<int>(step.clauseId.id);

    // Getting the instantiated variable-value pairs
    std::vector<std::pair<std::string, std::string>> instPairs =
        getInstPairs(i, normalizingEqualities[step.clauseId.id]);
    InstantiateVisitor instantiateVisitor(instPairs);

    if (unusedRem->printTerm() != currTerm->printTerm()) {

        notifyObservers(Step(currStep, Step::STEP,
                             packClause(std::make_shared<Op>("=", packClause(assumptionReNamedTerm, unusedRem))),
                             "qnt_rm_unused"));

        currStep++;

        notifyObservers(Step(currStep, Step::STEP,
                             packClause(std::make_shared<Op>("not", packClause(assumptionReNamedTerm)), unusedRem),
                             "equiv1", std::vector<int>{currStep - 1}));

        currStep++;

        notifyObservers(
            Step(currStep, Step::STEP, packClause(unusedRem), "resolution", std::vector<int>{quantStep, currStep - 1}));

        currStep++;

        currTerm = unusedRem;
        assumptionReNamedTerm = unusedRem;
        quantStep = currStep - 1;
    }

    if (not instPairs.empty()) {

        notifyObservers(Step(
            currStep, Step::STEP,
            packClause(std::make_shared<Op>(
                "or",
                packClause(std::make_shared<Op>("not", packClause(assumptionReNamedTerm)),
                           std::make_shared<Op>("!", packClause(currTerm->accept(&instantiateVisitor),
                                                                std::make_shared<Terminal>(
                                                                    ":named " + instantiationReNamedTerm->printTerm(),
                                                                    Terminal::UNDECLARED)))))),
            "forall_inst", instPairs));

        currStep++;

        notifyObservers(
            Step(currStep, Step::STEP,
                 packClause(std::make_shared<Op>("not", packClause(assumptionReNamedTerm)), instantiationReNamedTerm),
                 "or", std::vector<int>{currStep - 1}));

        currStep++;

        currTerm = currTerm->accept(&instantiateVisitor);

        notifyObservers(Step(currStep, Step::STEP, packClause(instantiationReNamedTerm), "resolution",
                             std::vector<int>{currStep - 1, quantStep}));

        currStep++;
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
            Step(currStep, Step::ASSUME,
                 packClause(std::make_shared<Op>(
                     "!", packClause(assertion, std::make_shared<Terminal>(":named @a" + std::to_string(currStep),
                                                                           Terminal::UNDECLARED))))));

        currStep++;
    }
}

void StepHandler::noCongRequiredSteps(std::vector<int> requiredMP, int implicationStep,
                                      std::shared_ptr<Term> const & renamedImpLHS) {

    if (implicationLHS->getTermType() == Term::OP) {

        auto termToSimplify = implicationLHS;
        auto simplificationRule =
            std::dynamic_pointer_cast<Op>(termToSimplify)->simplifyRule(); // Getting rule for simplification
        auto simplification = termToSimplify->accept(&operateVisitor);

        notifyObservers(Step(currStep, Step::STEP,
                             packClause(std::make_shared<Op>("=", packClause(termToSimplify, simplification))),
                             simplificationRule));

        currStep++;

        if (std::dynamic_pointer_cast<Op>(termToSimplify)->getOp() == "and") {

            conjunctionSimplification(requiredMP, std::make_shared<Op>("=", packClause(termToSimplify, simplification)),
                                      implicationStep, renamedImpLHS);
            return;
        } else if (std::dynamic_pointer_cast<Op>(termToSimplify)->getOp() == ">") {

            // If the term to simplify is a ">" or ">=" operation, we require additional steps

            auto originalSimplificaiton = simplification->accept(&copyVisitor);
            auto lessOrEq = std::dynamic_pointer_cast<Op>(simplification)->getArgs()[0];
            auto innerWorking = lessOrEq->accept(&operateVisitor);

            notifyObservers(Step(currStep, Step::STEP,
                                 packClause(std::make_shared<Op>("=", packClause(lessOrEq, innerWorking))),
                                 "comp_simplify"));

            currStep++;

            std::dynamic_pointer_cast<Op>(simplification)->setArg(0, innerWorking);

            notifyObservers(Step(currStep, Step::STEP,
                                 packClause(std::make_shared<Op>(
                                     "=", std::vector<std::shared_ptr<Term>>{originalSimplificaiton, simplification})),
                                 "cong", std::vector<int>{currStep - 1}));
            currStep++;

            auto outerWorking = simplification->accept(&operateVisitor);

            notifyObservers(Step(currStep, Step::STEP,
                                 packClause(std::make_shared<Op>("=", packClause(simplification, outerWorking))),
                                 "not_simplify"));
            currStep++;

            notifyObservers(Step(currStep, Step::STEP,
                                 packClause(std::make_shared<Op>(
                                     "=", std::vector<std::shared_ptr<Term>>{originalSimplificaiton, outerWorking})),
                                 "trans", std::vector<int>{currStep - 2, currStep - 1}));
            currStep++;

            notifyObservers(Step(
                currStep, Step::STEP,
                packClause(std::make_shared<Op>("=", std::vector<std::shared_ptr<Term>>{termToSimplify, outerWorking})),
                "trans", std::vector<int>{currStep - 5, currStep - 1}));
            currStep++;

            simplification = outerWorking;

        } else if (std::dynamic_pointer_cast<Op>(termToSimplify)->getOp() == ">=") {

            auto originalSimplificaiton = simplification->accept(&copyVisitor);

            simplification = simplification->accept(&operateVisitor);

            notifyObservers(
                Step(currStep, Step::STEP,
                     packClause(std::make_shared<Op>("=", packClause(originalSimplificaiton, simplification))),
                     "comp_simplify"));
            currStep++;

            notifyObservers(Step(currStep, Step::STEP,
                                 packClause(std::make_shared<Op>(
                                     "=", std::vector<std::shared_ptr<Term>>{termToSimplify, simplification})),
                                 "trans", std::vector<int>{currStep - 2, currStep - 1}));
            currStep++;
        }

        notifyObservers(Step(currStep, Step::STEP,
                             packClause(renamedImpLHS, std::make_shared<Op>("not", packClause(simplification))),
                             "equiv2", std::vector<int>{currStep - 1}));

        currStep++;

        if (simplification->printTerm() == "true") {

            stepReusage(simplification);

            notifyObservers(Step(currStep, Step::STEP, packClause(renamedImpLHS), "resolution",
                                 std::vector<int>{currStep - 2, currStep - 1}));

            currStep++;

            notifyObservers(Step(currStep, Step::STEP, packClause(implicationRHS), "resolution",
                                 std::vector<int>{implicationStep, currStep - 1}));

            modusPonensSteps.push_back(currStep);

            currStep++;
        } else {

            notifyObservers(Step(currStep, Step::STEP,
                                 packClause(std::make_shared<Op>("not", packClause(simplification)), implicationRHS),
                                 "resolution", std::vector<int>{implicationStep, currStep - 1}));

            currStep++;

            requiredMP.push_back(currStep - 1);

            notifyObservers(Step(currStep, Step::STEP, packClause(implicationRHS), "resolution", requiredMP));

            modusPonensSteps.push_back(currStep);

            currStep++;
        }
    } else {

        if (implicationLHS->getTermType() == Term::APP) {

            requiredMP.push_back(currStep - 1);

            notifyObservers(Step(currStep, Step::STEP, packClause(implicationRHS), "resolution", requiredMP));

            modusPonensSteps.push_back(currStep);

            currStep++;

        } else if (implicationLHS->getTermType() == Term::TERMINAL) {

            notifyObservers(Step(currStep, Step::STEP, packClause(renamedImpLHS), "true"));

            currStep++;

            notifyObservers(Step(currStep, Step::STEP, packClause(implicationRHS), "resolution",
                                 std::vector<int>{implicationStep, currStep - 1}));

            modusPonensSteps.push_back(currStep);

            currStep++;
        }
    }
}

void StepHandler::conjunctionSimplification(std::vector<int> requiredMP, const std::shared_ptr<Term> & lastClause,
                                            int implicationStep, const std::shared_ptr<Term> & renamedImpLHS) {

    auto termToSimplify = std::dynamic_pointer_cast<Op>(lastClause)->getArgs()[0];
    auto simplification = std::dynamic_pointer_cast<Op>(lastClause)->getArgs()[1];

    notifyObservers(Step(currStep, Step::STEP,
                         packClause(renamedImpLHS, std::make_shared<Op>("not", packClause(simplification))), "equiv2",
                         std::vector<int>{currStep - 1}));

    currStep++;

    // Check if we are dealing with a non linear case
    if (std::dynamic_pointer_cast<Op>(termToSimplify)->nonLinearity()) {
        notifyObservers(Step(
            currStep, Step::STEP,
            packClause(simplification,
                       std::make_shared<Terminal>(
                           std::dynamic_pointer_cast<Op>(simplification)->nonLinearSimplification(), Term::UNDECLARED)),
            "and_neg"));

        currStep++;

        notifyObservers(
            Step(currStep, Step::STEP,
                 packClause(renamedImpLHS, std::make_shared<Terminal>(
                                               std::dynamic_pointer_cast<Op>(simplification)->nonLinearSimplification(),
                                               Term::UNDECLARED)),
                 "resolution", std::vector<int>{currStep - 2, currStep - 1}));

        requiredMP.push_back(currStep);

        currStep++;
    } else {
        requiredMP.push_back(currStep - 1);
    }

    if (simplification->printTerm() == "true") {

        stepReusage(simplification);

    } else {

        notifyObservers(Step(currStep, Step::STEP, packClause(renamedImpLHS), "resolution", requiredMP));

        currStep++;
    }

    notifyObservers(Step(currStep, Step::STEP, packClause(implicationRHS), "resolution",
                         std::vector<int>{implicationStep, currStep - 1}));

    modusPonensSteps.push_back(currStep);

    currStep++;
}

std::vector<std::pair<std::string, std::string>>
StepHandler::getInstPairs(int stepIndex, vec<Normalizer::Equality> const & stepNormEq) {
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

    for (std::size_t premise : premises) {
        auto concreteArgs = utils.predicateArgsInOrder(derivation[premise].derivedFact);
        auto targetVertex = originalGraph.getEdge(derivation[premise].clauseId).to;

        auto instance = vertexInstance[targetVertex]++;
        PTRef predicateInstance = originalGraph.getStateVersion(targetVertex, instance);

        auto formalArgs = utils.predicateArgsInOrder(predicateInstance);
        assert(concreteArgs.size() == formalArgs.size());
        // Building the pairs
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
    }
    // Target variables instantiation
    auto concreteArgs = utils.predicateArgsInOrder(step.derivedFact);
    auto targetVertex = originalGraph.getEdge(step.clauseId).to;
    PTRef clauseHead = originalGraph.getNextStateVersion(targetVertex);
    auto formalArgs = utils.predicateArgsInOrder(clauseHead);
    assert(concreteArgs.size() == formalArgs.size());

    // Building the pairs
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

int StepHandler::stepReusage(std::shared_ptr<Term> term) {

    std::string strTerm = term->printTerm();

    if (strTerm == "(not true)") {
        if (stepsToReuse[0] == -1) {
            stepsToReuse[0] = currStep;
            return 0;
        } else {
            return 1;
        }
    } else if (strTerm == "(not false)") {
        if (stepsToReuse[1] == -1) {
            stepsToReuse[1] = currStep;
            return 0;
        } else {
            return 2;
        }
    } else if (strTerm == "true") {
        if (stepsToReuse[2] == -1) {
            notifyObservers(Step(currStep, Step::STEP, packClause(term), "true"));

            stepsToReuse[2] = currStep;

            currStep++;

            notifyObservers(Step(currStep, Step::STEP, packClause(implicationLHS), "resolution",
                                 std::vector<int>{currStep - 2, currStep - 1}));

        } else {
            notifyObservers(Step(currStep, Step::STEP, packClause(implicationLHS), "resolution",
                                 std::vector<int>{currStep - 1, stepsToReuse[2]}));
        }

        currStep++;
        return 3;
    }
    return 0;
}
