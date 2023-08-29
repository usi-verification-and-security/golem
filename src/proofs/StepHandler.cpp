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

std::vector<std::shared_ptr<Term>> StepHandler::packClause(std::shared_ptr<Term> term) {
    std::vector<std::shared_ptr<Term>> clause;
    clause.push_back(term);
    return clause;
}

std::vector<std::shared_ptr<Term>> StepHandler::packClause(std::shared_ptr<Term> term1, std::shared_ptr<Term> term2) {
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

            currTerm = originalAssertions[step.clauseId.id];

            // Variable instantiation
            instantiationSteps(i);

            implicationLHS = currTerm->accept(&implicationLhsVisitor);
            implicationRHS = std::make_shared<Terminal>(logic.printTerm(step.derivedFact), Term::VAR);

            //Implication rule
            proofSteps.emplace_back(currStep++, Step::STEP,
                                    packClause(std::make_shared<Op>("not", packClause(implicationLHS)), implicationRHS),
                                    "implies", std::vector<int>{currStep-1});

            implicationStep = currStep-1;

            //Checking if height of LHS is greater than 1
            if (not implicationLHS->accept(&requiresCongVisitor)) {
                //If it is not, the proof is shorter
                noCongRequiredSteps();

            } else {
                //If it is, we require additional steps

                termToSimplify = currTerm->accept(&simplifyLocatorVisitor);  //Locating possible simplification
                simplificationRule = termToSimplify->accept(&simplifyRuleVisitor);    //Getting rule for simplification
                //Operating simplification
                if (termToSimplify->accept(&operateVisitor) == "true" or termToSimplify->accept(&operateVisitor) == "false"){
                    simplification = std::make_shared<Terminal>(termToSimplify->accept(&operateVisitor), Term::INT);
                } else {
                    simplification = std::make_shared<Terminal>(termToSimplify->accept(&operateVisitor), Term::BOOL);
                }

                //Loop if there are more possible simplifications
                while (not (termToSimplify->Iam() == "Terminal" or termToSimplify->Iam() == "App")) {

                    //If the current term to simplify is at height 0, break the loop to end the proof
                    if (currTerm->accept(&implicationLhsVisitor)->accept(&printVisitor) == termToSimplify->accept(&printVisitor)) {
                        break;
                    }

                    IsPrimaryBranchVisitor isPrimaryBranchVisitor(currTerm->accept(&helperVisitor));  //Checking if the current term is a primary branch / branch of height 1
                    bool isPrimaryBranch = currTerm->accept(&isPrimaryBranchVisitor);

                    //Apply the simplification rule
                    proofSteps.emplace_back(currStep++, Step::STEP,
                                                    packClause(std::make_shared<Op>("=", packClause(termToSimplify, simplification))), simplificationRule);

                    //If the current term to simplify is not a primary branch we require additional steps
                    if (not isPrimaryBranch) {
                        //Proof simplification from bottom up
                        notLhsPrimaryBranchSteps();
                    }else {
                        //If it is a primary branch

                        //Check if the original primary branch has been applied for transitivity before
                        if (originalLhsPrimaryBranch != nullptr) {

                            //Pass along the information recall the transitivity state one last time
                            proofSteps.emplace_back(currStep++, Step::STEP,
                                                    packClause(std::make_shared<Op>("=", packClause(originalLhsPrimaryBranch, simplification))),
                                                    "trans", std::vector<int>{transitivityStep, currStep-1});

                        }
                        //Because this is the last time we simplify in this primary branch, we can forget it
                        originalLhsPrimaryBranch = nullptr;

                        //Remember this main simplification step for the final resolution
                        simplificationSteps.push_back(currStep-1);

                    }

                    //Simplifying the main LHS tree
                    SimplifyVisitor simplifyVisitor(simplification->accept(&printVisitor), currTerm->accept(&helperVisitor));
                    currTerm = currTerm->accept(&simplifyVisitor);

                    //Get new term to simplify and continue looping

                    termToSimplify = currTerm->accept(&simplifyLocatorVisitor);  //Locating possible simplification
                    simplificationRule = termToSimplify->accept(&simplifyRuleVisitor);    //Getting rule for simplification
                    //Operating simplification
                    if (termToSimplify->accept(&operateVisitor) == "true" or termToSimplify->accept(&operateVisitor) == "false"){
                        simplification = std::make_shared<Terminal>(termToSimplify->accept(&operateVisitor), Term::INT);
                    } else {
                        simplification = std::make_shared<Terminal>(termToSimplify->accept(&operateVisitor), Term::BOOL);
                    }
                }

                //Get the necessary steps for modus ponens
                std::vector<int> requiredMP;
                for (int i = 0; i < step.premises.size(); i++) {
                    requiredMP.push_back(modusPonensSteps[(int)step.premises[i]-1]);
                }

                //If the last term to simplify is a nonLinear operation, proceed differently
                if (termToSimplify->accept(&nonLinearVisitor)) {
                    nonLinearSimplification(requiredMP);
                } else {
                    linearSimplification(requiredMP);
                }
            }
        }
        //We don't need the simplification steps of the previous primary branch procedure
        simplificationSteps.clear();
    }

    proofSteps.emplace_back(currStep++, Step::STEP,
                            packClause(std::make_shared<Terminal>("(not false)", Term::UNDECLARED)), "false");
    //Get empty clause
    proofSteps.emplace_back(currStep++, Step::STEP, "resolution", std::vector<int>{currStep-2, currStep-1});

}

void StepHandler::instantiationSteps(int i) {

    auto const & step = derivation[i];

    //Getting the instantiated variable-value pairs
    std::vector<std::pair<std::string, std::string>> instPairs = getInstPairs(i, normalizingEqualities[step.clauseId.id]);
    InstantiateVisitor instantiateVisitor(instPairs);

    proofSteps.emplace_back(currStep++, Step::STEP,
                            packClause(std::make_shared<Op>("or", packClause(std::make_shared<Op>("not", packClause(currTerm)), currTerm->accept(&instantiateVisitor)))),
                            "forall_inst", instPairs);

    proofSteps.emplace_back(currStep++, Step::STEP,
                            packClause(std::make_shared<Op>("not", packClause(currTerm)), currTerm->accept(&instantiateVisitor)),
                            "or", std::vector<int>{currStep-1});

    currTerm = currTerm->accept(&instantiateVisitor);

    proofSteps.emplace_back(currStep++, Step::STEP,
                            packClause(currTerm),
                            "resolution", std::vector<int>{currStep-1, static_cast<int>(step.clauseId.id)});
}

void StepHandler::assumptionSteps() {
    auto assertionSize = originalAssertions.size();
    for (std::size_t i = 1; i <= assertionSize; ++i) {
        Term* potentialLet = originalAssertions[i-1]->accept(&letLocatorVisitor);
        if (potentialLet != nullptr) {
            auto simplifiedLet = potentialLet->accept(&operateLetTermVisitor);
            SimplifyLetTermVisitor simplifyLetTermVisitor(simplifiedLet, potentialLet);
            originalAssertions[i-1] = originalAssertions[i-1]->accept(&simplifyLetTermVisitor);
        }

        proofSteps.emplace_back(currStep++, Step::ASSUME, packClause(originalAssertions[i-1]));
    }
}

void StepHandler::noCongRequiredSteps(){

    termToSimplify = currTerm->accept(&simplifyLocatorVisitor);  //Locating possible simplification
    simplificationRule = termToSimplify->accept(&simplifyRuleVisitor);    //Getting rule for simplification

    //Operating simplification
    if (termToSimplify->accept(&operateVisitor) == "true" or termToSimplify->accept(&operateVisitor) == "false"){
        simplification = std::make_shared<Terminal>(termToSimplify->accept(&operateVisitor), Term::INT);
    } else {
        simplification = std::make_shared<Terminal>(termToSimplify->accept(&operateVisitor), Term::BOOL);
    }

    proofSteps.emplace_back(currStep++, Step::STEP,
                            packClause(std::make_shared<Op>("=", packClause(termToSimplify, simplification))), simplificationRule);

    proofSteps.emplace_back(currStep++, Step::STEP,
                            packClause(termToSimplify, std::make_shared<Op>("not", packClause(simplification))),
                            "equiv2", std::vector<int>{currStep-1});

    if (simplification->accept(&printVisitor) == "true") {

        proofSteps.emplace_back(currStep++, Step::STEP,
                                packClause(simplification), "true");

        proofSteps.emplace_back(currStep++, Step::STEP,
                                packClause(termToSimplify),
                                "resolution", std::vector<int>{currStep-2, currStep-1});

        proofSteps.emplace_back(currStep++, Step::STEP,
                                packClause(implicationRHS),
                                "resolution", std::vector<int>{implicationStep, currStep-1});

        modusPonensSteps.push_back(currStep-1);
    }
}

void StepHandler::notLhsPrimaryBranchSteps() {

    //Simplifying from bottom up applying congruence to carry information

    GetLocalParentBranchVisitor getLocalParentBranchVisitor(currTerm->accept(&helperVisitor));
    Term* localParentBranch = currTerm->accept(&getLocalParentBranchVisitor);   //Getting the parent branch of the current term for simplification

    SimplifyVisitor simplifyLocalParentBranchVisitor(simplification->accept(&printVisitor), localParentBranch->accept(&helperVisitor));
    std::shared_ptr<Term> localParentBranchSimplified = localParentBranch->accept(&simplifyLocalParentBranchVisitor);   //Simplifying said parent branch

    IsPrimaryBranchVisitor localIsPrimary(localParentBranch);  //Checking if the local parent is also a primary branch

    InstantiateVisitor fakeInstantiation;

    //Loop to start carrying the simplification from the bottom up
    while (true) {
        proofSteps.emplace_back(currStep++, Step::STEP,
                                packClause(std::make_shared<Op>("=", packClause(localParentBranch->accept(&fakeInstantiation), localParentBranchSimplified))),
                                "cong", std::vector<int>{currStep-1});

        GetLocalParentBranchVisitor newGetLocalParentBranchVisitor(localParentBranch);

        //If we reached the top, break the loop
        if (currTerm->accept(&implicationLhsVisitor)->accept(&printVisitor) == currTerm->accept(&newGetLocalParentBranchVisitor)->accept(&printVisitor)) {
            break;
        }
        //If not, get new local parent and keep looping
        localParentBranch = currTerm->accept(&newGetLocalParentBranchVisitor);
        SimplifyVisitor newSimplifyLocalParentBranchVisitor(simplification->accept(&printVisitor), localParentBranch->accept(&helperVisitor));
        localParentBranchSimplified = localParentBranch->accept(&newSimplifyLocalParentBranchVisitor);
    }

    //If there was no primary branch before this, save it as the original
    if (originalLhsPrimaryBranch == nullptr) {
        std::vector<std::pair<std::string, std::string>> emptypair;
        transitivityStep = currStep-1;
        originalLhsPrimaryBranch = localParentBranch->accept(&fakeInstantiation);
    } else {
        //If there was, create a transitivity step to remember information
        proofSteps.emplace_back(currStep++, Step::STEP,
                                packClause(std::make_shared<Op>("=", packClause(originalLhsPrimaryBranch, localParentBranchSimplified))),
                                "trans", std::vector<int>{transitivityStep, currStep-1});
        transitivityStep = currStep-1;
    }
}

void StepHandler::nonLinearSimplification(std::vector<int> requiredMP) {

    //Assuming the non Linearity appears at the last simplification step
    //Define this later

    proofSteps.emplace_back(currStep++, Step::STEP,
                            packClause(std::make_shared<Op>("=", packClause(implicationLHS, termToSimplify))),
                            "cong", simplificationSteps);

    proofSteps.emplace_back(currStep++, Step::STEP,
                            packClause(std::make_shared<Op>("=", packClause(termToSimplify, termToSimplify->accept(&simplifyNonLinearVisitor)))),
                            "and_simplify");

    termToSimplify = termToSimplify->accept(&simplifyNonLinearVisitor);

    proofSteps.emplace_back(currStep++, Step::STEP,
                            packClause(std::make_shared<Op>("=", packClause(implicationLHS, termToSimplify))),
                            "trans", std::vector<int>{currStep-2, currStep-1});

    proofSteps.emplace_back(currStep++, Step::STEP,
                            packClause(implicationLHS, std::make_shared<Op>("not", packClause(termToSimplify))),
                            "equiv2", std::vector<int>{currStep-1});

    proofSteps.emplace_back(currStep++, Step::STEP,
                            packClause(termToSimplify, std::make_shared<Terminal>(termToSimplify->accept(&negatedAndVisitor), Term::UNDECLARED)),
                            "and_neg");

    proofSteps.emplace_back(currStep++, Step::STEP,
                            packClause(implicationLHS, std::make_shared<Terminal>(termToSimplify->accept(&negatedAndVisitor), Term::UNDECLARED)),
                            "resolution", std::vector<int>{currStep-2, currStep-1});

    proofSteps.emplace_back(currStep++, Step::STEP,
                            packClause(implicationLHS),"resolution", requiredMP);

    proofSteps.emplace_back(currStep++, Step::STEP,
                            packClause(implicationRHS),"resolution", std::vector<int>{implicationStep, currStep-1});

    modusPonensSteps.push_back(currStep-1);

}

void StepHandler::linearSimplification(std::vector<int> requiredMP) {

    proofSteps.emplace_back(currStep++, Step::STEP,
                            packClause(std::make_shared<Op>("=", packClause(implicationLHS, termToSimplify))),
                            "cong", simplificationSteps);

    proofSteps.emplace_back(currStep++, Step::STEP,
                            packClause(std::make_shared<Op>("=", packClause(termToSimplify, simplification))), simplificationRule);

    proofSteps.emplace_back(currStep++, Step::STEP,
                            packClause(std::make_shared<Op>("=", packClause(implicationLHS, simplification))),
                            "trans", std::vector<int>{currStep-2, currStep-1});

    proofSteps.emplace_back(currStep++, Step::STEP,
                            packClause(implicationLHS, std::make_shared<Op>("not", packClause(simplification))),
                            "equiv2", std::vector<int>{currStep-1});

    if (simplification->accept(&printVisitor) == "true"){

        proofSteps.emplace_back(currStep++, Step::STEP,
                                packClause(simplification), "true");

        proofSteps.emplace_back(currStep++, Step::STEP,
                                packClause(implicationLHS),
                                "resolution", std::vector<int>{currStep-2, currStep-1});

    } else {

        requiredMP.push_back(currStep-1);

        proofSteps.emplace_back(currStep++, Step::STEP,
                                packClause(implicationLHS),"resolution", requiredMP);
    }

    proofSteps.emplace_back(currStep++, Step::STEP,
                            packClause(implicationRHS),"resolution", std::vector<int>{implicationStep, currStep-1});

    modusPonensSteps.push_back(currStep-1);
}


std::vector<std::pair<std::string, std::string>> StepHandler::getInstPairs(int it, std::vector<PTRef> stepNormEq) {
    std::vector<PTRef> sourceVariables;
    std::vector<std::pair<std::string, std::string>> instPairs;

    auto const & step = derivation[it];

    TermUtils utils(logic);

    bool skip = true;

    for (std::size_t premise : step.premises) {
        if (premise == 0){
            skip = false;
        }
    }

    if(skip) {
        for (std::size_t premise : step.premises) {
            auto concreteArgs = utils.predicateArgsInOrder(derivation[premise].derivedFact);
            auto targetVertex = originalGraph.getEdge(derivation[premise].clauseId).to;
            PTRef clauseHead = originalGraph.getStateVersion(targetVertex);
            auto formalArgs = utils.predicateArgsInOrder(clauseHead);
            assert(step.premises.size() == originalGraph.getEdge(derivation[premise].clauseId).from.size());
            assert(concreteArgs.size() == formalArgs.size());
            //Building the pairs
            for (int m = 0; m < formalArgs.size(); m++) {
                for (int n = 0; n < stepNormEq.size(); n++) {
                    if (stepNormEq[n] == formalArgs[m]) {
                        sourceVariables.push_back(stepNormEq[n-1]);
                        std::pair<std::string, std::string> pair;
                        pair.first = logic.printTerm(stepNormEq[n-1]);
                        pair.second = logic.printTerm(concreteArgs[m]);
                        instPairs.push_back(pair);
                    }
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
        for (int n = 0; n < stepNormEq.size(); n++) {
            if (stepNormEq[n] == formalArgs[m]) {
                for (PTRef variable : sourceVariables){
                    if (variable == stepNormEq[n-1]){
                        redundance = true;
                    }
                }
                if (!redundance) {
                    std::pair<std::string, std::string> pair;
                    pair.first = logic.printTerm(stepNormEq[n-1]);
                    pair.second = logic.printTerm(concreteArgs[m]);
                    instPairs.push_back(pair);
                } else {
                    redundance = false;
                }
            }
        }
    }
    return instPairs;
}
