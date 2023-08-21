/*
 * Copyright (c) 2020-2023, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "Witnesses.h"
#include "TransformationUtils.h"
#include "utils/SmtSolver.h"
#include <memory>

void VerificationResult::printWitness(std::ostream & out, Logic & logic) const {
    if (not hasWitness()) { return; }
    switch (answer) {
        case VerificationAnswer::SAFE: {
            getValidityWitness().print(out, logic);
            return;
        }
        case VerificationAnswer::UNSAFE: {
            getInvalidityWitness().print(out, logic);
            return;
        }
        default:
            return;
    }
}

void VerificationResult::printWitness_(std::ostream & out, Logic & logic, const ChcDirectedHyperGraph & originalGraph,
                                       std::vector<std::shared_ptr<Term>> originalAssertions, std::vector<std::vector<PTRef>> normalizingEqualities) const {

    if (not hasWitness()) { return; }
    switch (answer) {
        case VerificationAnswer::SAFE: {
            return;
        }
        case VerificationAnswer::UNSAFE: {

            getInvalidityWitness().alethePrint(out, logic, originalGraph, originalAssertions, normalizingEqualities);
            return;
        }
        default:
            return;
    }
}

void InvalidityWitness::alethePrint(std::ostream & out, Logic & logic, ChcDirectedHyperGraph const & originalGraph,
                                    std::vector<std::shared_ptr<Term>> originalAssertions, std::vector<std::vector<PTRef>> normalizingEqualities) const {

    auto assertionSize = originalAssertions.size();
    PrintVisitor printVisitor;
    SimplifyLocatorVisitor simpVisitor;
    OperateVisitor opVisitor;
    SimplifyRuleVisitor simplifyRuleVisitor;
    TerminalOrAppVisitor terminalOrAppVisitor;
    ImpFirstTermVisitor impFirstTermVisitor;
    RequiresCongVisitor requiresCongVisitor;

    for (std::size_t i = 1; i <= assertionSize; ++i) {
        // Printing assumptions
        out << "(assume h" << i << ' ' << originalAssertions[i-1]->accept(&printVisitor) << ")\n";
    }

    int currAletheStep = assertionSize;
    auto derivationSize = derivation.size();

    int modusPonensStep;

        for (std::size_t i = 0; i < derivationSize; ++i) {
            auto const & step = derivation[i];
            if (not step.premises.empty()) {

                std::vector<std::pair<std::string, std::string>> instPairs = getInstPairs(i, logic, originalGraph, normalizingEqualities[step.clauseId.id]);
                InstantiateVisitor instVisitor(instPairs);
                std::shared_ptr<Term> term = originalAssertions[step.clauseId.id];
                std::shared_ptr<Term> instTerm = term->accept(&instVisitor);

                //Instantiation
                out << "(step t" << ++currAletheStep << " " << "(cl (or (not " << term->accept(&printVisitor) << ") " << instTerm->accept(&printVisitor) << "))"
                    << " :rule forall_inst" << " :args (";

                for (std::pair<std::string, std::string> pair : instPairs){
                    out << "(:= " << pair.first << " " << pair.second << ")";
                }
                out << "))\n";

                out << "(step t" << ++currAletheStep << " " << "(cl (not " << term->accept(&printVisitor) << ") " << instTerm->accept(&printVisitor) << ")"
                    << " :rule or :premises (t" << currAletheStep-1 << "))\n";

                out << "(step t" << ++currAletheStep << " " << "(cl " << instTerm->accept(&printVisitor) << ") :rule resolution :premises (h"
                    << step.clauseId.id+1 << " t" << currAletheStep-1 << "))\n";

                //Simplification

                std::shared_ptr<Term> impFirstArg = instTerm->accept(&impFirstTermVisitor);

                out << "(step t" << ++currAletheStep << " " << "(cl (not " << impFirstArg->accept(&printVisitor) << ") " << logic.printTerm(step.derivedFact) << ") :rule implies :premises (t"
                    << currAletheStep-1 << "))\n";

                int impliesStep = currAletheStep;
                int modusPonensStep;

                if (not impFirstArg->accept(&requiresCongVisitor)) {

                    while (not instTerm->accept(&simpVisitor)->accept(&terminalOrAppVisitor)){
                        std::shared_ptr<Term> simplifiedTerm = instTerm->accept(&simpVisitor);
                        std::string simplification = simplifiedTerm->accept(&opVisitor);

                        out << "(step t" << ++currAletheStep << " " << "(cl (= " << simplifiedTerm->accept(&printVisitor) << " " << simplification
                            << ")) :rule " << simplifiedTerm->accept(&simplifyRuleVisitor) << ")\n";

                        out << "(step t" << ++currAletheStep << " " << "(cl " << simplifiedTerm->accept(&printVisitor) << " (not " << simplification
                            << ")) :rule equiv2 :premises (t" << currAletheStep-1 << "))\n";

                        if (simplification == "true"){
                            out << "(step t" << ++currAletheStep << " " << "(cl true) :rule true)\n";

                            out << "(step t" << ++currAletheStep << " " << "(cl " << simplifiedTerm->accept(&printVisitor) << ") :rule resolution :premises (t"
                                << currAletheStep-1 << " t" << currAletheStep-2 << "))\n";

                            out << "(step t" << ++currAletheStep << " " << "(cl " << logic.printTerm(step.derivedFact) << ") :rule resolution :premises (t"
                                << impliesStep << " t" << currAletheStep-1 << "))\n";

                            modusPonensStep = currAletheStep;
                        }

                        SimplifyVisitor simplifyVisitor(simplification, simplifiedTerm);

                        instTerm =  instTerm->accept(&simplifyVisitor);

                    }

                } else {

                    std::shared_ptr<Term> finalSimplifiedTerm;
                    std::string finalSimplification;
                    std::string finalRule;

                    std::vector<int> simpSteps;

                    while (not instTerm->accept(&simpVisitor)->accept(&terminalOrAppVisitor)) {

                        std::shared_ptr<Term> simplifiedTerm = instTerm->accept(&simpVisitor);
                        std::string simplification = simplifiedTerm->accept(&opVisitor);
                        std::string rule = simplifiedTerm->accept(&simplifyRuleVisitor);

                        if (rule != "and_simplify"){

                            out << "(step t" << ++currAletheStep << " "
                                << "(cl (= " << simplification << " " << simplifiedTerm->accept(&printVisitor)
                                << ")) :rule " << rule << ")\n";

                            SimplifyVisitor simplifyVisitor(simplification, simplifiedTerm);
                            instTerm = instTerm->accept(&simplifyVisitor);

                            if (rule != "and_simplify" and rule != "equiv_simplify" and rule != "or_simplify" and rule != "comp_simplify"){

                                std::shared_ptr<Term> nextSimplifiedTerm = instTerm->accept(&simpVisitor);
                                std::string nextSimplification = nextSimplifiedTerm->accept(&opVisitor);

                                out << "(step t" << ++currAletheStep << " "
                                    << "(cl " << nextSimplifiedTerm->accept(&printVisitor) << ") :rule refl)\n";

                                out << "(step t" << ++currAletheStep << " "
                                    << "(cl (= (= " << simplification << " " << simplifiedTerm->accept(&printVisitor) << ") " << nextSimplifiedTerm->accept(&printVisitor)
                                    << ")) :rule cong :premises (t" << currAletheStep-2 << " t" << currAletheStep -1<< "))\n";

                                out << "(step t" << ++currAletheStep << " "
                                    << "(cl (= " << nextSimplifiedTerm->accept(&printVisitor) << " " << nextSimplification
                                    << ")) :rule " << nextSimplifiedTerm->accept(&simplifyRuleVisitor) << ")\n";

                                out << "(step t" << ++currAletheStep << " "
                                    << "(cl (= (= " << simplification << " " << simplifiedTerm->accept(&printVisitor)
                                    << ") " << nextSimplification << ")) :rule trans :premises (t" << currAletheStep-2 << " t" << currAletheStep-1 << "))\n";

                                simpSteps.push_back(currAletheStep);

                                SimplifyVisitor newSimplifyVisitor(nextSimplification, nextSimplifiedTerm);
                                instTerm = instTerm->accept(&newSimplifyVisitor);
                            } else {
                                simpSteps.push_back(currAletheStep);
                            }
                        } else {
                            finalRule = rule;
                            finalSimplification = simplification;
                            finalSimplifiedTerm = simplifiedTerm;

                            SimplifyVisitor simplifyVisitor(simplification, simplifiedTerm);
                            instTerm = instTerm->accept(&simplifyVisitor);
                        }
                    }

                    out << "(step t" << ++currAletheStep << " "
                        << "(cl (= " << impFirstArg->accept(&printVisitor) << " "
                        << finalSimplifiedTerm->accept(&printVisitor) << ")) :rule cong :premises (";

                    for (int i = 0; i < simpSteps.size(); i++) {
                        out << "t" << simpSteps[i];
                        if (i != simpSteps.size()-1) {
                            out << " ";
                        }
                    }

                    out << "))\n";

                    out << "(step t" << ++currAletheStep << " "
                        << "(cl (= " << finalSimplifiedTerm->accept(&printVisitor) << " " << finalSimplification
                        << ")) :rule " << finalRule << ")\n";

                    out << "(step t" << ++currAletheStep << " "
                        << "(cl (= " << impFirstArg->accept(&printVisitor) << " "
                        << finalSimplification << ")) :rule trans :premises (t" << currAletheStep-2 << " t" << currAletheStep-1 << "))\n";

                    out << "(step t" << ++currAletheStep << " "
                        << "(cl " << impFirstArg->accept(&printVisitor) << " (not "
                        << finalSimplification << ")) :rule equiv2 :premises (t" << currAletheStep-1 << "))\n";

                    out << "(step t" << ++currAletheStep << " "
                        << "(cl " << impFirstArg->accept(&printVisitor)
                        << ") :rule resolution :premises (t" << currAletheStep-1 << " t" << modusPonensStep << "))\n";

                    out << "(step t" << ++currAletheStep << " " << "(cl " << logic.printTerm(step.derivedFact) << ") :rule resolution :premises (t"
                        << impliesStep << " t" << currAletheStep-1 << "))\n";

                    modusPonensStep = currAletheStep;

                }

                /*
                //Simplification

                int instantionStep = currAletheStep;

                while (not instTerm->accept(&simpVisitor)->accept(&terminalOrAppVisitor)){
                    std::shared_ptr<Term> simplifiedTerm = instTerm->accept(&simpVisitor);
                    std::string simplification = simplifiedTerm->accept(&opVisitor);

                    out << "(step t" << ++currAletheStep << " " << "(cl (= " << simplifiedTerm->accept(&printVisitor) << " " << simplification
                        << ")) :rule " << simplifiedTerm->accept(&simplifyRuleVisitor) << "))\n";

                    SimplifyVisitor simplifyVisitor(simplification, simplifiedTerm);

                    instTerm =  instTerm->accept(&simplifyVisitor);
                    out << "(step t" << ++currAletheStep << " " << "(cl " << instTerm->accept(&printVisitor)
                        << ") :rule substitution :premises (t" << currAletheStep-1 << " t" << instantionStep << "))\n";

                    instantionStep = currAletheStep;
                }

                //Modus Ponens

                out << "(step t" << ++currAletheStep << " (cl (not ";
                for(std::size_t premise : step.premises){
                    out << logic.printTerm(derivation[premise].derivedFact) << ") ";
                }
                out << logic.printTerm(step.derivedFact) << ")) :rule implies :premises (t" << currAletheStep-1 << "))\n";

                int finalImplication = currAletheStep;

                if (i == 1){
                    out << "(step t" << ++currAletheStep << " (cl true) :rule true)\n";
                    modusPonensStep = currAletheStep;
                    out << "(step t" << ++currAletheStep << " (cl " << logic.printTerm(step.derivedFact) << ") :rule resolution :premises (t"
                        << finalImplication << " t" << modusPonensStep << "))\n";
                    modusPonensStep = currAletheStep;
                } else{
                    out << "(step t" << ++currAletheStep << " (cl " << logic.printTerm(step.derivedFact) << ") :rule resolution :premises (t"
                        << finalImplication << " t" << modusPonensStep << "))\n";
                    modusPonensStep = currAletheStep;
                }
                 */

            }
    }

    out << "(step t" << ++currAletheStep << " (cl (not false)) :rule false)\n";
    out << "(step t" << ++currAletheStep << " (cl) :rule resolution :premises (t"
        << currAletheStep-2 << " t" << currAletheStep-1 << "))\n";

}

std::vector<std::pair<std::string, std::string>> InvalidityWitness::getInstPairs(int it, Logic & logic, const ChcDirectedHyperGraph& originalGraph,
                                                        std::vector<PTRef> stepNormEq) const {
    std::vector<PTRef> sourceVariables;
    std::vector<std::pair<std::string, std::string>> instPairs;

    auto const & step = derivation[it];
    TermUtils utils(logic);

    if(it != 1) {
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
    //printing target variables instantiation
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

InvalidityWitness InvalidityWitness::fromErrorPath(ErrorPath const & errorPath, ChcDirectedGraph const & graph) {
    using Derivation = InvalidityWitness::Derivation;
    Logic & logic = graph.getLogic();
    Derivation derivation;
    using DerivationStep = Derivation::DerivationStep;
    auto const & path = errorPath;
    if (path.isEmpty()) { return {}; }
    auto edgeIds = path.getEdges();
    // Compute model for the error path
    auto model = [&]() {
        SMTSolver solverWrapper(logic, SMTSolver::WitnessProduction::ONLY_MODEL);
        auto & solver = solverWrapper.getCoreSolver();
        for (std::size_t i = 0; i < edgeIds.size(); ++i) {
            PTRef fla = graph.getEdgeLabel(edgeIds[i]);
            fla = TimeMachine(logic).sendFlaThroughTime(fla, i);
            solver.insertFormula(fla);
        }
        auto res = solver.check();
        if (res != s_True) { throw std::logic_error("Error in computing model for the error path"); }
        return solver.getModel();
    }();

    struct UPHelper {
        int counter = 0;
        ChcDirectedGraph const & graph;
        LinearPredicateVersioning predicateVersioning;

        PTRef operator()(SymRef vertex) {
            PTRef term = graph.getStateVersion(vertex);
            return predicateVersioning.sendPredicateThroughTime(term, counter++);
        }

        UPHelper(ChcDirectedGraph const & graph, Logic & logic) : graph(graph), predicateVersioning(logic) {}
    };
    assert(graph.getSource(edgeIds[0]) == logic.getSym_true());
    std::vector<SymRef> vertices;
    std::transform(edgeIds.begin(), edgeIds.end(), std::back_inserter(vertices),
                   [&graph](EId eid) { return graph.getSource(eid); });
    vertices.push_back(graph.getTarget(edgeIds.back()));
    std::vector<PTRef> vertexPredicates;
    std::transform(vertices.begin(), vertices.end(), std::back_inserter(vertexPredicates), UPHelper(graph, logic));

    auto instantiate = [&](PTRef predicate) {
        TermUtils utils(logic);
        auto vars = utils.predicateArgsInOrder(predicate);
        TermUtils::substitutions_map subst;
        for (PTRef var : vars) {
            subst.insert({var, model->evaluate(var)});
        }
        return utils.varSubstitute(predicate, subst);
    };

    assert(vertexPredicates.size() == edgeIds.size() + 1);
    std::size_t stepCounter = 0;
    // Make the `true` the first step of the derivation
    derivation.addDerivationStep({.index = stepCounter++, .premises = {},.derivedFact = logic.getTerm_true(), .clauseId = {static_cast<id_t>(-1)}});
    for (std::size_t i = 0; i < edgeIds.size(); ++i) {
        auto id = edgeIds[i];
        DerivationStep step;
        step.index = stepCounter;
        step.clauseId = id;
        step.premises = std::vector<size_t>{stepCounter - 1};
        step.derivedFact = instantiate(vertexPredicates[i + 1]);
        derivation.addDerivationStep(std::move(step));
        ++stepCounter;
    }

    InvalidityWitness witness;
    witness.setDerivation(std::move(derivation));
    return witness;
}

InvalidityWitness InvalidityWitness::fromTransitionSystem(const ChcDirectedGraph & graph, std::size_t unrollings) {
    return fromErrorPath(ErrorPath::fromTransitionSystem(graph, unrollings), graph);
}

void InvalidityWitness::print(std::ostream & out, Logic & logic) const {
    auto derivationSize = derivation.size();
    for (std::size_t i = 0; i < derivationSize; ++i) {
        auto const & step = derivation[i];
        out << i << ":\t";
        out << logic.printTerm(step.derivedFact);
        if (not step.premises.empty()) {
            out << " -> ";
            for (auto index : step.premises) {
                out << ' ' << index;

            }
            out << '\n';
        }
        out << '\n';
    }
    out << std::endl;
}

void ValidityWitness::print(std::ostream & out, Logic & logic) const {
    for (auto && [predicate, definition] : interpretations) {
        if (predicate == logic.getTerm_true() or predicate == logic.getTerm_false()) { continue; }
        out << "  (define-fun " << logic.protectName(logic.getSymRef(predicate)) << " (";
        const auto & args = TermUtils(logic).predicateArgsInOrder(predicate);
        for (std::size_t i = 0; i < args.size(); ++i) {
            auto sortString = logic.printSort(logic.getSortRef(args[i]));
            out << "(" << logic.protectName(logic.getSymRef(args[i])) << " " << sortString << ")" << (i == args.size()-1 ? "" : " ");
        }
        assert(logic.getSortRef(predicate) == logic.getSort_bool());
        out << ")" << " " << logic.printSort(logic.getSortRef(predicate)) << "\n";
        out << "    " << logic.printTerm(definition) << ")\n";
    }
}

ErrorPath ErrorPath::fromTransitionSystem(const ChcDirectedGraph & graph, std::size_t unrollings) {
    if (not isTransitionSystem(graph)) { return {}; }
    auto adjacencyList = AdjacencyListsGraphRepresentation::from(graph);
    auto vertices = graph.getVertices();
    assert(vertices.size() == 3);
    auto loopingVertex = *std::find_if(vertices.begin(), vertices.end(), [&](SymRef sym) {
        return sym != graph.getEntry() and sym != graph.getExit();
    });
    auto loopingVertexIncoming = adjacencyList.getIncomingEdgesFor(loopingVertex);
    auto it = std::find_if(loopingVertexIncoming.begin(), loopingVertexIncoming.end(), [&graph](EId eid) {
        return graph.getSource(eid) == graph.getTarget(eid);
    });
    assert(it != loopingVertexIncoming.end());
    EId loopingEdge = *it;
    EId startEdge = adjacencyList.getOutgoingEdgesFor(graph.getEntry())[0];
    EId finalEdge = adjacencyList.getIncomingEdgesFor(graph.getExit())[0];
    std::vector<EId> pathEdges(unrollings, loopingEdge);
    pathEdges.push_back(finalEdge);
    pathEdges.insert(pathEdges.begin(), startEdge);
    return ErrorPath(std::move(pathEdges));
}

ValidityWitness
ValidityWitness::fromTransitionSystem(Logic & logic, ChcDirectedGraph const & graph,
                                      TransitionSystem const & transitionSystem, PTRef inductiveInvariant) {
    if (not isTransitionSystem(graph)) { return {}; }
    auto vertices = graph.getVertices();
    assert(vertices.size() == 3);
    auto vertex = vertices[2];
    assert(vertex != graph.getEntry() and vertex != graph.getExit());
    TermUtils utils(logic);
    TimeMachine timeMachine(logic);
    TermUtils::substitutions_map subs;
    auto graphVars = utils.predicateArgsInOrder(graph.getStateVersion(vertex));
    auto systemVars = transitionSystem.getStateVars();
    vec<PTRef> unversionedVars;
    assert(graphVars.size() == systemVars.size());
    for (std::size_t i = 0; i < graphVars.size(); ++i) {
        unversionedVars.push(timeMachine.getUnversioned(graphVars[i]));
        subs.insert({systemVars[i], unversionedVars.last()});
    }
    PTRef graphInvariant = utils.varSubstitute(inductiveInvariant, subs);
//    std::cout << "Graph invariant: " << logic.printTerm(graphInvariant) << std::endl;
    PTRef unversionedPredicate = logic.mkUninterpFun(vertex, std::move(unversionedVars));
    ValidityWitness::definitions_t definitions{{unversionedPredicate, graphInvariant}};
    return ValidityWitness(std::move(definitions));
}

VerificationResult
translateTransitionSystemResult(TransitionSystemVerificationResult result, ChcDirectedGraph const & graph, TransitionSystem const & transitionSystem) {
    switch (result.answer) {
        case VerificationAnswer::SAFE:
            return {VerificationAnswer::SAFE, ValidityWitness::fromTransitionSystem(graph.getLogic(), graph, transitionSystem, std::get<PTRef>(result.witness))};
        case VerificationAnswer::UNSAFE:
            return {VerificationAnswer::UNSAFE, InvalidityWitness::fromTransitionSystem(graph, std::get<std::size_t>(result.witness))};
        case VerificationAnswer::UNKNOWN:
            return VerificationResult(VerificationAnswer::UNKNOWN);
    }
    assert(false);
    return VerificationResult(VerificationAnswer::UNKNOWN);
}