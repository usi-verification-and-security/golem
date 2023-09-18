//
// Created by mambo on 8/29/23.
//
#include "AletheSteps.h"
#include <memory>
#include <string>
#include <utility>

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

std::string Step::printStepIntermediate() {

    PrintVisitor printVisitor;
    std::stringstream ss;

    ss << stepId << '\t';

    if (!clause.empty()) {
        ss << " ";
        for (int i = 0; i < clause.size(); i++) {
            ss << clause[i]->accept(&printVisitor);
            ss << " ";
        }
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

    if (!premises.empty()) {
        ss << " :premises ";
        for (auto premise : premises) {
            ss << premise << " ";
        }
    }

    ss << "\n";

    return ss.str();
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

void StepHandler::buildIntermediateProof() {

    auto derivationSize = derivation.size();

    for (std::size_t i = 0; i < derivationSize; ++i) {

        auto const & step = derivation[i];

        if (step.premises.empty()) {
            continue;
        }

        auto instPairs = getInstPairs(i, normalizingEqualities[step.clauseId.id]);
        InstantiateVisitor instantiateVisitor(instPairs);
        currTerm = originalAssertions[step.clauseId.id];

        if (not instPairs.empty()) {

            notifyObservers(Step(currStep, Step::STEP,
                                 packClause(currTerm),
                                 "forall_inst", instPairs));
            currStep++;

            currTerm = currTerm->accept(&instantiateVisitor);

        }

        notifyObservers(Step(currStep, Step::STEP,
                             packClause(currTerm)));
        currStep++;

        std::stringstream premises;

        for (int i = 0; i < step.premises.size(); i++) {
            premises << logic.printTerm(derivation[step.premises[i]].derivedFact);
            if (i < step.premises.size()-1) {
                premises << ' ';
            }
        }

        notifyObservers(Step(currStep, Step::STEP,
                             packClause(std::make_shared<Op>("=>",
                                                             packClause(std::make_shared<Terminal>(premises.str(), Term::VAR), std::make_shared<Terminal>(logic.printTerm(step.derivedFact), Term::VAR))))));
        currStep++;

        std::vector<int> requiredMP;

        if (!modusPonensSteps.empty()) {
            //Get the necessary steps for modus ponens
            for (int i = 0; i < step.premises.size(); i++) {
                requiredMP.push_back(modusPonensSteps[(int)step.premises[i]-1]);
            }
        }

        notifyObservers(Step(currStep, Step::STEP,
                             packClause(std::make_shared<Terminal>(logic.printTerm(step.derivedFact), Term::VAR)), "resolution",requiredMP));

        modusPonensSteps.push_back(currStep);

        currStep++;
    }

}

void StepHandler::buildAletheProof() {

    //Building assumptions
    assumptionSteps();

    auto derivationSize = derivation.size();

    //Iteration through derivations
    for (std::size_t i = 0; i < derivationSize; ++i) {
        auto const & step = derivation[i];

        //We don't need the simplification steps of the previous derivation procedure
        simplificationSteps.clear();

        if (step.premises.empty()) {
            continue;
        }

        std::vector<int> requiredMP;

        if (!modusPonensSteps.empty()) {
            //Get the necessary steps for modus ponens
            for (int i = 0; i < step.premises.size(); i++) {
                requiredMP.push_back(modusPonensSteps[(int)step.premises[i]-1]);
            }
        }

        currTerm = originalAssertions[step.clauseId.id];

        // Variable instantiation
        instantiationSteps(i); //pass the currTerm as an argument

        std::shared_ptr<Op> implication = std::dynamic_pointer_cast<Op> (currTerm);

        implicationLHS = implication->getArgs()[0];
        implicationRHS = std::make_shared<Terminal>(logic.printTerm(step.derivedFact), Term::VAR);

        //Implication rule

        notifyObservers(Step(currStep, Step::STEP,
                             packClause(std::make_shared<Op>("not", packClause(implicationLHS)), implicationRHS),
                             "implies", std::vector<int>{currStep-1}));

        int implicationStep = currStep;

        currStep++;

        //Checking if height of LHS is greater than 1
        if (not requiresCong()) {
            //If it is not, the proof is shorter
            noCongRequiredSteps(requiredMP, implicationStep);

        } else {
            //If it is, we require additional steps

            auto termToSimplify = currTerm->accept(&simplifyLocatorVisitor);  //Locating possible simplification
            auto simplificationRule = std::dynamic_pointer_cast<Op> (termToSimplify)->simplifyRule();    //Getting rule for simplification
            //Operating simplification
            auto simplification = termToSimplify->accept(&operateVisitor);

            //Loop if there are more possible simplifications
            while (not (termToSimplify->getTermType() == Term::TERMINAL or termToSimplify->getTermType() == Term::APP)) {

                //If the current term to simplify is at height 0, break the loop to end the proof
                if (std::dynamic_pointer_cast<Op> (currTerm)->getArgs()[0]->accept(&printVisitor) == termToSimplify->accept(&printVisitor)) {
                    break;
                }

                IsPrimaryBranchVisitor isPrimaryBranchVisitor(currTerm->accept(&helperVisitor));  //Checking if the current term is a primary branch / branch of height 1
                bool isPrimaryBranch = currTerm->accept(&isPrimaryBranchVisitor);

                //Apply the simplification rule
                notifyObservers(Step(currStep, Step::STEP,
                                     packClause(std::make_shared<Op>("=", packClause(termToSimplify, simplification))), simplificationRule));

                currStep++;

                //If the current term to simplify is not a primary branch we require additional steps
                if (not isPrimaryBranch) {

                    //Proof simplification from bottom up
                    notLhsPrimaryBranchSteps(simplification);
                }else {
                    //If it is a primary branch

                    //Check if the original primary branch has been applied for transitivity before
                    if (originalLhsPrimaryBranch != nullptr) {

                        //Pass along the information recall the transitivity state one last time
                        notifyObservers(Step(currStep, Step::STEP,
                                             packClause(std::make_shared<Op>("=", packClause(originalLhsPrimaryBranch, simplification))),
                                             "trans", std::vector<int>{transitivityStep, currStep-1}));

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
                simplificationRule = std::dynamic_pointer_cast<Op> (termToSimplify)->simplifyRule();    //Getting rule for simplification
                //Operating simplification
                simplification = termToSimplify->accept(&operateVisitor);
            }

            //If the last term to simplify is a nonLinear operation, proceed differently
            conjunctionSimplification(requiredMP, simplification, termToSimplify, simplificationRule, implicationStep);
        }
    }

    notifyObservers(Step(currStep, Step::STEP,
                         packClause(std::make_shared<Terminal>("(not false)", Term::UNDECLARED)), "false"));

    currStep++;
    //Get empty clause
    notifyObservers(Step(currStep, Step::STEP, "resolution", std::vector<int>{currStep-2, currStep-1}));
}

bool StepHandler::requiresCong() {

    if (implicationLHS->getTermType() == Term::TERMINAL or implicationLHS->getTermType() == Term::APP) {
        return false;
    } else {
      for(auto arg : std::dynamic_pointer_cast<Op>(implicationLHS)->getArgs()) {
            if (not (arg->getTermType() == Term::TERMINAL or arg->getTermType() == Term::APP)) {
                return true;
            }
      }
    }
    return false;
}

void StepHandler::instantiationSteps(int i) {

    auto const & step = derivation[i];

    std::shared_ptr<Term> unusedRem = currTerm->accept(&removeUnusedVisitor);

    int quantStep = static_cast<int>(step.clauseId.id);

    //Getting the instantiated variable-value pairs
    std::vector<std::pair<std::string, std::string>> instPairs = getInstPairs(i, normalizingEqualities[step.clauseId.id]);
    InstantiateVisitor instantiateVisitor(instPairs);

    if (unusedRem->accept(&printVisitor) != currTerm->accept(&printVisitor)) {

        notifyObservers(Step(currStep, Step::STEP,
                             packClause(std::make_shared<Op>("=", packClause(currTerm, unusedRem))),
                             "qnt_rm_unused"));

        currStep++;

        notifyObservers(Step(currStep, Step::STEP,
                             packClause(std::make_shared<Op>("not", packClause(currTerm)), unusedRem),
                             "equiv1", std::vector<int>{currStep-1}));

        currStep++;

        notifyObservers(Step(currStep, Step::STEP,
                             packClause(unusedRem),
                             "resolution", std::vector<int>{quantStep, currStep-1}));

        currStep++;

        currTerm = unusedRem;
        quantStep = currStep-1;
    }

    if (not instPairs.empty()) {

        notifyObservers(Step(currStep, Step::STEP,
                             packClause(std::make_shared<Op>("or", packClause(std::make_shared<Op>("not", packClause(currTerm)), currTerm->accept(&instantiateVisitor)))),
                             "forall_inst", instPairs));

        currStep++;

        notifyObservers(Step(currStep, Step::STEP,
                             packClause(std::make_shared<Op>("not", packClause(currTerm)), currTerm->accept(&instantiateVisitor)),
                             "or", std::vector<int>{currStep-1}));

        currStep++;

        currTerm = currTerm->accept(&instantiateVisitor);

        notifyObservers(Step(currStep, Step::STEP,
                             packClause(currTerm),
                             "resolution", std::vector<int>{currStep-1, quantStep}));

        currStep++;
    }
}

void StepHandler::assumptionSteps() {

    auto assertionSize = originalAssertions.size();
    for (std::size_t i = 1; i <= assertionSize; ++i) {
        Term* potentialLet = originalAssertions[i-1]->accept(&letLocatorVisitor);
        while (potentialLet != nullptr) {
            auto simplifiedLet = potentialLet->accept(&operateLetTermVisitor);
            SimplifyVisitor simplifyLetTermVisitor(simplifiedLet, potentialLet);
            originalAssertions[i-1] = originalAssertions[i-1]->accept(&simplifyLetTermVisitor);
            potentialLet = originalAssertions[i-1]->accept(&letLocatorVisitor);
        }
        notifyObservers(Step(currStep, Step::ASSUME, packClause(originalAssertions[i-1])));

        currStep++;
    }
}

void StepHandler::noCongRequiredSteps(std::vector<int> requiredMP, int implicationStep){

    if (not (implicationLHS->getTermType() == Term::TERMINAL or implicationLHS->getTermType() == Term::APP)) {

        auto termToSimplify = currTerm->accept(&simplifyLocatorVisitor);  //Locating possible simplification
        auto simplificationRule = std::dynamic_pointer_cast<Op> (termToSimplify)->simplifyRule();    //Getting rule for simplification
        auto simplification = termToSimplify->accept(&operateVisitor);

        if (std::dynamic_pointer_cast<Op>(termToSimplify)->getOp() == "and") {
            conjunctionSimplification(requiredMP, simplification, termToSimplify, simplificationRule, implicationStep, false);
            return;
        }

        notifyObservers(Step(currStep, Step::STEP,
                             packClause(std::make_shared<Op>("=", packClause(termToSimplify, simplification))), simplificationRule));

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
                simplificationRule = std::dynamic_pointer_cast<Op> (termToSimplify)->simplifyRule();    //Getting rule for simplification
                simplification = termToSimplify->accept(&operateVisitor);

                notifyObservers(Step(currStep, Step::STEP,
                                     packClause(std::make_shared<Op>("=", packClause(termToSimplify, simplification))), simplificationRule));

                currStep++;

                localParentBranch = std::dynamic_pointer_cast<Op> (currTerm)->getArgs()[0];

                //Simplifying the main LHS tree
                SimplifyVisitor simplifyVisitor(simplification, currTerm->accept(&helperVisitor));
                currTerm = currTerm->accept(&simplifyVisitor);

                if (std::dynamic_pointer_cast<Op> (currTerm)->getArgs()[0]->accept(&printVisitor) == simplification->accept(&printVisitor)) {
                    break;
                }

                SimplifyVisitor simplifyLocalParentBranchVisitor(simplification, localParentBranch->accept(&helperVisitor));

                localParentBranchSimplified = localParentBranch->accept(&simplifyLocalParentBranchVisitor);

                notifyObservers(Step(currStep, Step::STEP,
                                     packClause(std::make_shared<Op>("=", packClause(localParentBranch, localParentBranchSimplified))),
                                     "cong", std::vector<int>{currStep-1}));

                currStep++;

                notifyObservers(Step(currStep, Step::STEP,
                                     packClause(std::make_shared<Op>("=", packClause(implicationLHS, localParentBranchSimplified))),
                                     "trans", std::vector<int>{transitivityStep, currStep-1}));

                transitivityStep = currStep;

                currStep++;
            }

            notifyObservers(Step(currStep, Step::STEP,
                                 packClause(std::make_shared<Op>("=", packClause(implicationLHS, simplification))),
                                 "trans", std::vector<int>{transitivityStep, currStep-1}));

            currStep++;
        }

        notifyObservers(Step(currStep, Step::STEP,
                             packClause(implicationLHS, std::make_shared<Op>("not", packClause(simplification))),
                             "equiv2", std::vector<int>{currStep-1}));

        currStep++;

        if (simplification->accept(&printVisitor) == "true") {

            notifyObservers(Step(currStep, Step::STEP,
                                 packClause(simplification), "true"));

            currStep++;

            notifyObservers(Step(currStep, Step::STEP,
                                 packClause(implicationLHS),
                                 "resolution", std::vector<int>{currStep-2, currStep-1}));

            currStep++;

            notifyObservers(Step(currStep, Step::STEP,
                                 packClause(implicationRHS),
                                 "resolution", std::vector<int>{implicationStep, currStep-1}));

            modusPonensSteps.push_back(currStep);

            currStep++;
        } else {

            notifyObservers(Step(currStep, Step::STEP,
                                 packClause(std::make_shared<Op>("not", packClause(simplification)), implicationRHS),
                                 "resolution", std::vector<int>{implicationStep, currStep-1}));

            currStep++;

            requiredMP.push_back(currStep-1);

            notifyObservers(Step(currStep, Step::STEP,
                                 packClause(implicationRHS),"resolution", requiredMP));

            modusPonensSteps.push_back(currStep);

            currStep++;


        }
    } else {

        if (implicationLHS->getTermType() == Term::APP) {

            requiredMP.push_back(currStep-1);

            notifyObservers(Step(currStep, Step::STEP,
                                 packClause(implicationRHS),"resolution", requiredMP));

            modusPonensSteps.push_back(currStep);

            currStep++;

        } else if (implicationLHS->getTermType() == Term::TERMINAL) {

            notifyObservers(Step(currStep, Step::STEP,
                                 packClause(implicationLHS), "true"));

            currStep++;

            notifyObservers(Step(currStep, Step::STEP,
                                 packClause(implicationRHS),
                                 "resolution", std::vector<int>{implicationStep, currStep-1}));

            modusPonensSteps.push_back(currStep);

            currStep++;
        }
    }
}

void StepHandler::notLhsPrimaryBranchSteps(const std::shared_ptr<Term>& simplification) {

    //Simplifying from bottom up applying congruence to carry information

    GetLocalParentBranchVisitor getLocalParentBranchVisitor(currTerm->accept(&helperVisitor));
    Term* localParentBranch = currTerm->accept(&getLocalParentBranchVisitor);   //Getting the parent branch of the current term for simplification

    SimplifyVisitor simplifyLocalParentBranchVisitor(simplification, localParentBranch->accept(&helperVisitor));
    std::shared_ptr<Term> localParentBranchSimplified = localParentBranch->accept(&simplifyLocalParentBranchVisitor);   //Simplifying said parent branch

    IsPrimaryBranchVisitor localIsPrimary(localParentBranch);  //Checking if the local parent is also a primary branch

    InstantiateVisitor fakeInstantiation;

    //Loop to start carrying the simplification from the bottom up
    while (true) {
        notifyObservers(Step(currStep, Step::STEP,
                             packClause(std::make_shared<Op>("=", packClause(localParentBranch->accept(&fakeInstantiation), localParentBranchSimplified))),
                             "cong", std::vector<int>{currStep-1}));

        currStep++;

        GetLocalParentBranchVisitor newGetLocalParentBranchVisitor(localParentBranch);

        //If we reached the top, break the loop
        if (currTerm->accept(&localIsPrimary)) {
            break;
        } else if (std::dynamic_pointer_cast<Op> (currTerm)->getArgs()[0]->accept(&printVisitor) == currTerm->accept(&newGetLocalParentBranchVisitor)->accept(&printVisitor)) {
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
        notifyObservers(Step(currStep, Step::STEP,
                             packClause(std::make_shared<Op>("=", packClause(originalLhsPrimaryBranch, localParentBranchSimplified))),
                             "trans", std::vector<int>{transitivityStep, currStep-1}));

        transitivityStep = currStep;
        currStep++;
    }
}

void StepHandler::conjunctionSimplification(std::vector<int> requiredMP, const std::shared_ptr<Term>& simplification, const std::shared_ptr<Term>& termToSimplify, std::string simplificationRule, int implicationStep, bool cong) {

    if (cong) {
        notifyObservers(Step(currStep, Step::STEP,
                             packClause(std::make_shared<Op>("=", packClause(implicationLHS, termToSimplify))),
                             "cong", simplificationSteps));
        currStep++;
    }

    notifyObservers(Step(currStep, Step::STEP,
                         packClause(std::make_shared<Op>("=", packClause(termToSimplify, simplification))), std::move(simplificationRule)));

    currStep++;

    if (cong) {
        notifyObservers(Step(currStep, Step::STEP,
                             packClause(std::make_shared<Op>("=", packClause(implicationLHS, simplification))),
                             "trans", std::vector<int>{currStep-2, currStep-1}));

        currStep++;
    }

    notifyObservers(Step(currStep, Step::STEP,
                         packClause(implicationLHS, std::make_shared<Op>("not", packClause(simplification))),
                         "equiv2", std::vector<int>{currStep-1}));

    currStep++;

    if (termToSimplify->accept(&nonLinearVisitor)) {
        notifyObservers(Step(currStep, Step::STEP,
                             packClause(simplification, std::make_shared<Terminal>(simplification->accept(&negatedAndVisitor), Term::UNDECLARED)),
                             "and_neg"));

        currStep++;

        notifyObservers(Step(currStep, Step::STEP,
                             packClause(implicationLHS, std::make_shared<Terminal>(simplification->accept(&negatedAndVisitor), Term::UNDECLARED)),
                             "resolution", std::vector<int>{currStep-2, currStep-1}));

        requiredMP.push_back(currStep);

        currStep++;
    } else {
        requiredMP.push_back(currStep-1);
    }

    if (simplification->accept(&printVisitor) == "true"){

        notifyObservers(Step(currStep, Step::STEP,
                             packClause(simplification), "true"));

        currStep++;

        notifyObservers(Step(currStep, Step::STEP,
                             packClause(implicationLHS),
                             "resolution", std::vector<int>{currStep-2, currStep-1}));

        currStep++;

    } else {

        notifyObservers(Step(currStep, Step::STEP,
                             packClause(implicationLHS),"resolution", requiredMP));

        currStep++;
    }

    notifyObservers(Step(currStep, Step::STEP,
                         packClause(implicationRHS),"resolution", std::vector<int>{implicationStep, currStep-1}));

    modusPonensSteps.push_back(currStep);

    currStep++;
}


std::vector<std::pair<std::string, std::string>> StepHandler::getInstPairs(int stepIndex, vec<Normalizer::Equality> const & stepNormEq) {
    struct VarValPair { PTRef var; PTRef val; };
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
        //Building the pairs
        for (int m = 0; m < formalArgs.size(); m++) {
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
    //Target variables instantiation
    auto concreteArgs = utils.predicateArgsInOrder(step.derivedFact);
    auto targetVertex = originalGraph.getEdge(step.clauseId).to;
    PTRef clauseHead = originalGraph.getNextStateVersion(targetVertex);
    auto formalArgs = utils.predicateArgsInOrder(clauseHead);
    assert(concreteArgs.size() == formalArgs.size());

    //Building the pairs
    for (int m = 0; m < formalArgs.size(); m++){
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
        assert(res == s_True);
        auto model = solver.getCoreSolver().getModel();
        for (PTRef auxVar : auxVars) {
            PTRef val = model->evaluate(auxVar);
            auto it = std::find_if(stepNormEq.begin(), stepNormEq.end(), [&](auto const & eq) {
                return eq.normalizedVar == auxVar;
            });
            if (it == stepNormEq.end()) { throw std::logic_error("Auxiliary variable should have been found in normalizing equalities"); }
            PTRef originalVar = it->originalArg;
            if (processedOriginalArguments.find(originalVar) == processedOriginalArguments.end()) {
                processedOriginalArguments.insert(originalVar);
                instPairsBeforeNormalization.push_back({originalVar, val});
            }
        }
    }

    std::vector<std::pair<std::string, std::string>> res;
    std::transform(instPairsBeforeNormalization.begin(), instPairsBeforeNormalization.end(), std::back_inserter(res), [&](auto const & varVal) {
        assert(logic.isVar(varVal.var));
        std::string varName = logic.getSymName(varVal.var);
        return std::make_pair(varName, logic.printTerm(varVal.val));
    });
    return res;
}
