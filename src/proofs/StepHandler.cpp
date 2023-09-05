//
// Created by mambo on 8/29/23.
//
#include "AletheSteps.h"
#include <memory>
#include <string>

std::string Step::printStepAlethe() {

    PrintVisitor printVisitor;
    std::stringstream ss;
    ss << "(";

    if (type == ASSUME) {
        ss << "assume t";
    } else if (type == STEP) {
        ss << "step t";
    }

    ss << stepId;

    if (type != ASSUME) {
        ss << " (cl";
    }

    if (!clause.empty()) {
        ss << " ";
        for (int i = 0; i < clause.size(); i++) {
            ss << clause[i]->accept(&printVisitor);
            if (i != clause.size()-1) {
                ss << " ";
            }
        }
    }

    if (type != ASSUME) {
        ss << ")";
    }

    if (rule != " ") {
        ss << " :rule " << rule;
    }

    if (!premises.empty()) {
        ss << " :premises (";
        for (int i = 0; i < premises.size(); i++) {
            ss << "t" << premises[i];
            if (i != premises.size()-1) {
                ss << " ";
            }
        }
        ss << ")";
    }

    if (!args.empty()) {
        ss << " :args (";
        for (int i = 0; i < args.size(); i++){
            ss << "(:= " << args[i].first << " " << args[i].second << ")";
            if (i != args.size()-1) {
                ss << " ";
            }
        }
        ss << ")";
    }

    ss << ")\n";

    return ss.str();
}

void StepHandler::displayProof() {

    for (auto step : proofSteps) {
        out << step.printStepAlethe();
    }

}

std::vector<std::shared_ptr<Term>> StepHandler::packClause(const std::shared_ptr<Term>& term) {
    std::vector<std::shared_ptr<Term>> clause;
    clause.push_back(term);
    return clause;
}

std::vector<std::shared_ptr<Term>> StepHandler::packClause(const std::shared_ptr<Term>& term1, const std::shared_ptr<Term>& term2) {
    std::vector<std::shared_ptr<Term>> clause;
    clause.push_back(term1);
    clause.push_back(term2);
    return clause;
}

void StepHandler::buildAletheProof() {

    //Building assumptions
    assumptionSteps();

    auto derivationSize = derivation.size();

    //Iteration through derivations
    for (std::size_t i = 0; i < derivationSize; ++i) {
        auto const & step = derivation[i];

        if (not step.premises.empty()) {

            std::vector<int> requiredMP;

            if (!modusPonensSteps.empty()) {
                //Get the necessary steps for modus ponens
                for (int i = 0; i < step.premises.size(); i++) {
                    requiredMP.push_back(modusPonensSteps[(int)step.premises[i]-1]);
                }
            }

            currTerm = originalAssertions[step.clauseId.id];

            // Variable instantiation
            instantiationSteps(i);

            implicationLHS = currTerm->accept(&implicationLhsVisitor);
            implicationRHS = std::make_shared<Terminal>(logic.printTerm(step.derivedFact), Term::VAR);

            //Implication rule
            proofSteps.emplace_back(currStep, Step::STEP,
                                    packClause(std::make_shared<Op>("not", packClause(implicationLHS)), implicationRHS),
                                    "implies", std::vector<int>{currStep-1});

            implicationStep = currStep;

            currStep++;

            //Checking if height of LHS is greater than 1
            if (not implicationLHS->accept(&requiresCongVisitor)) {
                //If it is not, the proof is shorter
                noCongRequiredSteps(requiredMP);

            } else {
                //If it is, we require additional steps

                termToSimplify = currTerm->accept(&simplifyLocatorVisitor);  //Locating possible simplification
                simplificationRule = termToSimplify->accept(&simplifyRuleVisitor);    //Getting rule for simplification
                //Operating simplification
                simplification = termToSimplify->accept(&operateVisitor);

                //Loop if there are more possible simplifications
                while (not (termToSimplify->getTermType() == Term::TERMINAL or termToSimplify->getTermType() == Term::APP)) {

                    //If the current term to simplify is at height 0, break the loop to end the proof
                    if (currTerm->accept(&implicationLhsVisitor)->accept(&printVisitor) == termToSimplify->accept(&printVisitor)) {
                        break;
                    }

                    IsPrimaryBranchVisitor isPrimaryBranchVisitor(currTerm->accept(&helperVisitor));  //Checking if the current term is a primary branch / branch of height 1
                    bool isPrimaryBranch = currTerm->accept(&isPrimaryBranchVisitor);

                    //Apply the simplification rule
                    proofSteps.emplace_back(currStep, Step::STEP,
                                                    packClause(std::make_shared<Op>("=", packClause(termToSimplify, simplification))), simplificationRule);

                    currStep++;

                    //If the current term to simplify is not a primary branch we require additional steps
                    if (not isPrimaryBranch) {

                        //Proof simplification from bottom up
                        notLhsPrimaryBranchSteps();
                    }else {
                        //If it is a primary branch

                        //Check if the original primary branch has been applied for transitivity before
                        if (originalLhsPrimaryBranch != nullptr) {

                            //Pass along the information recall the transitivity state one last time
                            proofSteps.emplace_back(currStep, Step::STEP,
                                                    packClause(std::make_shared<Op>("=", packClause(originalLhsPrimaryBranch, simplification))),
                                                    "trans", std::vector<int>{transitivityStep, currStep-1});

                            currStep++;

                        }

                        //Because this is the last time we simplify in this primary branch, we can forget it
                        originalLhsPrimaryBranch = nullptr;

                        //If for some reason, this is a primary branch but we are not done simplifying it yet, we have to remember this step for transitivity later
                        if (simplification->getTermType() != Term::TERMINAL) {
                            originalLhsPrimaryBranch = termToSimplify;
                            transitivityStep = currStep-1;
                        } else {
                            //Remember this main simplification step for the final resolution
                            simplificationSteps.push_back(currStep-1);
                        }
                    }


                    //Simplifying the main LHS tree
                    SimplifyVisitor simplifyVisitor(simplification, currTerm->accept(&helperVisitor));
                    currTerm = currTerm->accept(&simplifyVisitor);


                    //Get new term to simplify and continue looping

                    termToSimplify = currTerm->accept(&simplifyLocatorVisitor);  //Locating possible simplification
                    simplificationRule = termToSimplify->accept(&simplifyRuleVisitor);    //Getting rule for simplification
                    //Operating simplification
                    simplification = termToSimplify->accept(&operateVisitor);
                }

                //If the last term to simplify is a nonLinear operation, proceed differently
                if (termToSimplify->accept(&nonLinearVisitor)) {
                    nonLinearSimplification(requiredMP);
                } else {
                    linearSimplification(requiredMP);
                }
            }
        }
        //We don't need the simplification steps of the previous derivation procedure
        simplificationSteps.clear();
    }

    proofSteps.emplace_back(currStep, Step::STEP,
                            packClause(std::make_shared<Terminal>("(not false)", Term::UNDECLARED)), "false");
    currStep++;
    //Get empty clause
    proofSteps.emplace_back(currStep, Step::STEP, "resolution", std::vector<int>{currStep-2, currStep-1});

}

void StepHandler::instantiationSteps(int i) {

    auto const & step = derivation[i];

    std::shared_ptr<Term> unusedRem = currTerm->accept(&removeUnusedVisitor);

    int quantStep = static_cast<int>(step.clauseId.id);

    //Getting the instantiated variable-value pairs
    std::vector<std::pair<std::string, std::string>> instPairs = getInstPairs(i, normalizingEqualities[step.clauseId.id]);
    InstantiateVisitor instantiateVisitor(instPairs);

    if (unusedRem->accept(&printVisitor) != currTerm->accept(&printVisitor)) {
        proofSteps.emplace_back(currStep, Step::STEP,
                                packClause(std::make_shared<Op>("=", packClause(currTerm, unusedRem))),
                                "qnt_rm_unused");
        currStep++;

        proofSteps.emplace_back(currStep, Step::STEP,
                                packClause(std::make_shared<Op>("not", packClause(currTerm)), unusedRem),
                                "equiv1", std::vector<int>{currStep-1});

        currStep++;

        proofSteps.emplace_back(currStep, Step::STEP,
                                packClause(unusedRem),
                                "resolution", std::vector<int>{quantStep, currStep-1});

        currStep++;

        currTerm = unusedRem;
        quantStep = currStep-1;
    }

    if (not instPairs.empty()) {

        proofSteps.emplace_back(currStep, Step::STEP,
                                packClause(std::make_shared<Op>("or", packClause(std::make_shared<Op>("not", packClause(currTerm)), currTerm->accept(&instantiateVisitor)))),
                                "forall_inst", instPairs);
        currStep++;

        proofSteps.emplace_back(currStep, Step::STEP,
                                packClause(std::make_shared<Op>("not", packClause(currTerm)), currTerm->accept(&instantiateVisitor)),
                                "or", std::vector<int>{currStep-1});
        currStep++;

        currTerm = currTerm->accept(&instantiateVisitor);

        proofSteps.emplace_back(currStep, Step::STEP,
                                packClause(currTerm),
                                "resolution", std::vector<int>{currStep-1, quantStep});
        currStep++;
    }
}

void StepHandler::assumptionSteps() {

    auto assertionSize = originalAssertions.size();
    for (std::size_t i = 1; i <= assertionSize; ++i) {
        Term* potentialLet = originalAssertions[i-1]->accept(&letLocatorVisitor);
        if (potentialLet != nullptr) {
            auto simplifiedLet = potentialLet->accept(&operateLetTermVisitor);
            SimplifyVisitor simplifyLetTermVisitor(simplifiedLet, potentialLet);
            originalAssertions[i-1] = originalAssertions[i-1]->accept(&simplifyLetTermVisitor);
        }

        proofSteps.emplace_back(currStep, Step::ASSUME, packClause(originalAssertions[i-1]));

        currStep++;
    }
}

void StepHandler::noCongRequiredSteps(std::vector<int> requiredMP){

    if (not (implicationLHS->getTermType() == Term::TERMINAL or implicationLHS->getTermType() == Term::APP)) {

        termToSimplify = currTerm->accept(&simplifyLocatorVisitor);  //Locating possible simplification
        simplificationRule = termToSimplify->accept(&simplifyRuleVisitor);    //Getting rule for simplification
        simplification = termToSimplify->accept(&operateVisitor);

        proofSteps.emplace_back(currStep, Step::STEP,
                                packClause(std::make_shared<Op>("=", packClause(termToSimplify, simplification))), simplificationRule);
        transitivityStep = currStep;

        currStep++;

        //Simplifying the main LHS tree
        SimplifyVisitor simplifyVisitor(simplification, currTerm->accept(&helperVisitor));
        currTerm = currTerm->accept(&simplifyVisitor);

        if (simplification->getTermType() == Term::OP) {

            std::shared_ptr<Term> localParentBranchSimplified;
            std::shared_ptr<Term> localParentBranch;

            while (true) {

                termToSimplify = currTerm->accept(&simplifyLocatorVisitor);  //Locating possible simplification
                simplificationRule = termToSimplify->accept(&simplifyRuleVisitor);    //Getting rule for simplification
                simplification = termToSimplify->accept(&operateVisitor);

                proofSteps.emplace_back(currStep, Step::STEP,
                                        packClause(std::make_shared<Op>("=", packClause(termToSimplify, simplification))), simplificationRule);
                currStep++;

                localParentBranch = currTerm->accept(&implicationLhsVisitor);

                //Simplifying the main LHS tree
                SimplifyVisitor simplifyVisitor(simplification, currTerm->accept(&helperVisitor));
                currTerm = currTerm->accept(&simplifyVisitor);

                if (currTerm->accept(&implicationLhsVisitor)->accept(&printVisitor) == simplification->accept(&printVisitor)) {
                    break;
                }

                SimplifyVisitor simplifyLocalParentBranchVisitor(simplification, localParentBranch->accept(&helperVisitor));

                localParentBranchSimplified = localParentBranch->accept(&simplifyLocalParentBranchVisitor);

                proofSteps.emplace_back(currStep, Step::STEP,
                                        packClause(std::make_shared<Op>("=", packClause(localParentBranch, localParentBranchSimplified))),
                                        "cong", std::vector<int>{currStep-1});

                currStep++;

                proofSteps.emplace_back(currStep, Step::STEP,
                                        packClause(std::make_shared<Op>("=", packClause(implicationLHS, localParentBranchSimplified))),
                                        "trans", std::vector<int>{transitivityStep, currStep-1});

                transitivityStep = currStep;

                currStep++;
            }
            proofSteps.emplace_back(currStep, Step::STEP,
                                    packClause(std::make_shared<Op>("=", packClause(implicationLHS, simplification))),
                                    "trans", std::vector<int>{transitivityStep, currStep-1});
            currStep++;
        }

        proofSteps.emplace_back(currStep, Step::STEP,
                                packClause(implicationLHS, std::make_shared<Op>("not", packClause(simplification))),
                                "equiv2", std::vector<int>{currStep-1});
        currStep++;

        if (simplification->accept(&printVisitor) == "true") {

            proofSteps.emplace_back(currStep, Step::STEP,
                                    packClause(simplification), "true");
            currStep++;

            proofSteps.emplace_back(currStep, Step::STEP,
                                    packClause(implicationLHS),
                                    "resolution", std::vector<int>{currStep-2, currStep-1});
            currStep++;

            proofSteps.emplace_back(currStep, Step::STEP,
                                    packClause(implicationRHS),
                                    "resolution", std::vector<int>{implicationStep, currStep-1});

            modusPonensSteps.push_back(currStep);

            currStep++;
        }
    } else {

        if (implicationLHS->getTermType() == Term::APP) {

            requiredMP.push_back(currStep-1);

            proofSteps.emplace_back(currStep, Step::STEP,
                                    packClause(implicationRHS),"resolution", requiredMP);

            modusPonensSteps.push_back(currStep);

            currStep++;

        } else if (implicationLHS->getTermType() == Term::TERMINAL) {
            proofSteps.emplace_back(currStep, Step::STEP,
                                    packClause(implicationLHS), "true");
            currStep++;

            proofSteps.emplace_back(currStep, Step::STEP,
                                    packClause(implicationRHS),
                                    "resolution", std::vector<int>{implicationStep, currStep-1});

            modusPonensSteps.push_back(currStep);

            currStep++;
        }
    }


}

void StepHandler::notLhsPrimaryBranchSteps() {

    //Simplifying from bottom up applying congruence to carry information

    GetLocalParentBranchVisitor getLocalParentBranchVisitor(currTerm->accept(&helperVisitor));
    Term* localParentBranch = currTerm->accept(&getLocalParentBranchVisitor);   //Getting the parent branch of the current term for simplification

    SimplifyVisitor simplifyLocalParentBranchVisitor(simplification, localParentBranch->accept(&helperVisitor));
    std::shared_ptr<Term> localParentBranchSimplified = localParentBranch->accept(&simplifyLocalParentBranchVisitor);   //Simplifying said parent branch

    IsPrimaryBranchVisitor localIsPrimary(localParentBranch);  //Checking if the local parent is also a primary branch

    InstantiateVisitor fakeInstantiation;

    //Loop to start carrying the simplification from the bottom up
    while (true) {
        proofSteps.emplace_back(currStep, Step::STEP,
                                packClause(std::make_shared<Op>("=", packClause(localParentBranch->accept(&fakeInstantiation), localParentBranchSimplified))),
                                "cong", std::vector<int>{currStep-1});
        currStep++;

        GetLocalParentBranchVisitor newGetLocalParentBranchVisitor(localParentBranch);

        //If we reached the top, break the loop
        if (currTerm->accept(&localIsPrimary)) {
            break;
        } else if (currTerm->accept(&implicationLhsVisitor)->accept(&printVisitor) == currTerm->accept(&newGetLocalParentBranchVisitor)->accept(&printVisitor)) {
            break;
        }

        //If not, get new local parent and keep looping
        localParentBranch = currTerm->accept(&newGetLocalParentBranchVisitor);
        SimplifyVisitor newSimplifyLocalParentBranchVisitor(simplification, localParentBranch->accept(&helperVisitor));
        localParentBranchSimplified = localParentBranch->accept(&newSimplifyLocalParentBranchVisitor);
    }

    //If there was no primary branch before this, save it as the original
    if (originalLhsPrimaryBranch == nullptr) {
        std::vector<std::pair<std::string, std::string>> emptypair;
        transitivityStep = currStep-1;
        originalLhsPrimaryBranch = localParentBranch->accept(&fakeInstantiation);
    } else {
        //If there was, create a transitivity step to remember information
        proofSteps.emplace_back(currStep, Step::STEP,
                                packClause(std::make_shared<Op>("=", packClause(originalLhsPrimaryBranch, localParentBranchSimplified))),
                                "trans", std::vector<int>{transitivityStep, currStep-1});

        transitivityStep = currStep;
        currStep++;
    }
}

void StepHandler::nonLinearSimplification(std::vector<int> requiredMP) {

    //Assuming the non Linearity appears at the last simplification step
    //Define this later

    proofSteps.emplace_back(currStep, Step::STEP,
                            packClause(std::make_shared<Op>("=", packClause(implicationLHS, termToSimplify))),
                            "cong", simplificationSteps);
    currStep++;

    proofSteps.emplace_back(currStep, Step::STEP,
                            packClause(std::make_shared<Op>("=", packClause(termToSimplify, termToSimplify->accept(&operateVisitor)))),
                            "and_simplify");
    currStep++;

    termToSimplify = termToSimplify->accept(&operateVisitor);

    proofSteps.emplace_back(currStep, Step::STEP,
                            packClause(std::make_shared<Op>("=", packClause(implicationLHS, termToSimplify))),
                            "trans", std::vector<int>{currStep-2, currStep-1});
    currStep++;

    proofSteps.emplace_back(currStep, Step::STEP,
                            packClause(implicationLHS, std::make_shared<Op>("not", packClause(termToSimplify))),
                            "equiv2", std::vector<int>{currStep-1});
    currStep++;

    proofSteps.emplace_back(currStep, Step::STEP,
                            packClause(termToSimplify, std::make_shared<Terminal>(termToSimplify->accept(&negatedAndVisitor), Term::UNDECLARED)),
                            "and_neg");
    currStep++;

    proofSteps.emplace_back(currStep, Step::STEP,
                            packClause(implicationLHS, std::make_shared<Terminal>(termToSimplify->accept(&negatedAndVisitor), Term::UNDECLARED)),
                            "resolution", std::vector<int>{currStep-2, currStep-1});

    requiredMP.push_back(currStep);

    currStep++;

    proofSteps.emplace_back(currStep, Step::STEP,
                            packClause(implicationLHS),"resolution", requiredMP);
    currStep++;

    proofSteps.emplace_back(currStep, Step::STEP,
                            packClause(implicationRHS),"resolution", std::vector<int>{implicationStep, currStep-1});

    modusPonensSteps.push_back(currStep);

    currStep++;
}

void StepHandler::linearSimplification(std::vector<int> requiredMP) {

    proofSteps.emplace_back(currStep, Step::STEP,
                            packClause(std::make_shared<Op>("=", packClause(implicationLHS, termToSimplify))),
                            "cong", simplificationSteps);
    currStep++;

    proofSteps.emplace_back(currStep, Step::STEP,
                            packClause(std::make_shared<Op>("=", packClause(termToSimplify, simplification))), simplificationRule);
    currStep++;

    proofSteps.emplace_back(currStep, Step::STEP,
                            packClause(std::make_shared<Op>("=", packClause(implicationLHS, simplification))),
                            "trans", std::vector<int>{currStep-2, currStep-1});
    currStep++;

    proofSteps.emplace_back(currStep, Step::STEP,
                            packClause(implicationLHS, std::make_shared<Op>("not", packClause(simplification))),
                            "equiv2", std::vector<int>{currStep-1});
    currStep++;

    if (simplification->accept(&printVisitor) == "true"){

        proofSteps.emplace_back(currStep, Step::STEP,
                                packClause(simplification), "true");
        currStep++;

        proofSteps.emplace_back(currStep, Step::STEP,
                                packClause(implicationLHS),
                                "resolution", std::vector<int>{currStep-2, currStep-1});
        currStep++;

    } else {

        requiredMP.push_back(currStep-1);

        proofSteps.emplace_back(currStep, Step::STEP,
                                packClause(implicationLHS),"resolution", requiredMP);
        currStep++;
    }

    proofSteps.emplace_back(currStep, Step::STEP,
                            packClause(implicationRHS),"resolution", std::vector<int>{implicationStep, currStep-1});

    modusPonensSteps.push_back(currStep);

    currStep++;
}


std::vector<std::pair<std::string, std::string>> StepHandler::getInstPairs(int it, vec<Normalizer::Equality> const & stepNormEq) {
    struct VarValPair { PTRef var; PTRef val; };
    std::vector<PTRef> sourceVariables;
    std::vector<VarValPair> instPairsBeforeNormalization;
    std::vector<VarValPair> instPairsAfterNormalization;

    auto const & step = derivation[it];

    TermUtils utils(logic);

    auto premises = step.premises;
    premises.erase(std::remove(premises.begin(), premises.end(), 0), premises.end());

    std::vector<std::pair<int, PTRef>> instanceVertexPairs;
    bool present = false;

    for (std::size_t premise : premises) {
        auto concreteArgs = utils.predicateArgsInOrder(derivation[premise].derivedFact);
        auto targetVertex = originalGraph.getEdge(derivation[premise].clauseId).to;

        PTRef clauseBody =  originalGraph.getStateVersion(targetVertex);

        //Dealing with repeated predicates
        unsigned instance;
        for (auto pair : instanceVertexPairs) {
            if (clauseBody == pair.second) {
                present = true;
                pair.first++;
                instance = pair.first;
                break;
            }
        }
        if (not present) {
            instanceVertexPairs.emplace_back(0, clauseBody);
        } else {
            clauseBody =  originalGraph.getStateVersion(targetVertex, instance);
        }

        auto formalArgs = utils.predicateArgsInOrder(clauseBody);
        assert(concreteArgs.size() == formalArgs.size());
        //Building the pairs
        for (int m = 0; m < formalArgs.size(); m++) {
            for (auto const & equality : stepNormEq) {
                if (equality.normalizedVar == formalArgs[m]) {
                    sourceVariables.push_back(equality.originalArg);
                    assert(logic.isConstant(concreteArgs[m]));
                    instPairsBeforeNormalization.push_back({equality.originalArg, concreteArgs[m]});
                    instPairsAfterNormalization.push_back({equality.normalizedVar, concreteArgs[m]});
                }
            }
        }
    }
    //Target variables instantiation
    bool redundance = false;
    auto concreteArgs = utils.predicateArgsInOrder(step.derivedFact);
    auto targetVertex = originalGraph.getEdge(step.clauseId).to;
    PTRef clauseHead = originalGraph.getNextStateVersion(targetVertex);
    auto formalArgs = utils.predicateArgsInOrder(clauseHead);
    assert(concreteArgs.size() == formalArgs.size());

    //Building the pairs
    for (int m = 0; m < formalArgs.size(); m++){
        for (auto const & equality : stepNormEq) {
            if (equality.normalizedVar == formalArgs[m]) {
                for (PTRef variable : sourceVariables){
                    if (variable == equality.originalArg){
                        redundance = true;
                    }
                }
                if (!redundance) {
                    assert(logic.isConstant(concreteArgs[m]));
                    instPairsBeforeNormalization.push_back({equality.originalArg, concreteArgs[m]});
                    instPairsAfterNormalization.push_back({equality.normalizedVar, concreteArgs[m]});
                } else {
                    redundance = false;
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

    PTRef instantiatedConstraint = utils.varSubstitute(originalConstraint, substitutionsMap);
    if (instantiatedConstraint != logic.getTerm_true()) {
        assert(instantiatedConstraint != logic.getTerm_false());
        auto auxVars = utils.getVars(instantiatedConstraint);
        // Find values for auxiliary variables
        SMTSolver solver(logic, SMTSolver::WitnessProduction::ONLY_MODEL);
        solver.getCoreSolver().insertFormula(instantiatedConstraint);
        auto res = solver.getCoreSolver().check();
        assert(res == s_True);
        auto model = solver.getCoreSolver().getModel();
        for (PTRef auxVar : auxVars) {
            PTRef val = model->evaluate(auxVar);
            auto it = std::find_if(stepNormEq.begin(), stepNormEq.end(), [&](auto const & eq) {
                return eq.normalizedVar == auxVar;
            });
            if (it == stepNormEq.end()) { throw std::logic_error("Auxiliary variable should have been found in normalizing equalities"); }
            PTRef originalVar = it->originalArg;
            instPairsBeforeNormalization.push_back({originalVar, val});
        }
    }

    std::vector<std::pair<std::string, std::string>> res;
    std::transform(instPairsBeforeNormalization.begin(), instPairsBeforeNormalization.end(), std::back_inserter(res), [&](auto const & varVal) {
       return std::make_pair(logic.printTerm(varVal.var), logic.printTerm(varVal.val));
    });

    return res;
}
