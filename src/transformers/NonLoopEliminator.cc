/*
 * Copyright (c) 2022-2023, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "NonLoopEliminator.h"

#include "CommonUtils.h"

void NonLoopEliminator::BackTranslator::notifyRemovedVertex(SymRef sym, ContractionResult && contractionResult) {
    assert(removedNodes.count(sym) == 0);
    removedNodes.insert({sym, std::move(contractionResult)});
}

Transformer::TransformationResult NonLoopEliminator::transform(std::unique_ptr<ChcDirectedHyperGraph> graph) {
    auto backTranslator = std::make_unique<BackTranslator>(graph->getLogic(), graph->predicateRepresentation());
    while(true) {
        auto adjancencyRepresentation = AdjacencyListsGraphRepresentation::from(*graph);
        auto nonLoopingVertices = this->nonloopingVertices(*graph, adjancencyRepresentation);
        auto candidateForRemovalIt = std::find_if(nonLoopingVertices.begin(), nonLoopingVertices.end(), [&](SymRef vertex){
            // Vertex can be contracted if
            // 1. It does not have a self-loop
            // 2. If it does not have a hyperedge; TODO: Remove this constraint
            auto const & outgoing = adjancencyRepresentation.getOutgoingEdgesFor(vertex);
            if (std::any_of(outgoing.begin(), outgoing.end(), [&](EId eid){ return graph->getTarget(eid) == vertex or graph->getSources(eid).size() > 1; })) {
                return false;
            }
            auto const & incoming = adjancencyRepresentation.getIncomingEdgesFor(vertex);
            return std::none_of(incoming.begin(), incoming.end(), [&](EId eid){ return graph->getSources(eid).size() > 1; });
        });
        if (candidateForRemovalIt == nonLoopingVertices.end()) { break; }
        auto vertexToRemove = *candidateForRemovalIt;
        auto contractionResult = graph->contractVertex(vertexToRemove);
        backTranslator->notifyRemovedVertex(vertexToRemove, std::move(contractionResult));
    }
    return {std::move(graph), std::move(backTranslator)};
}

// TODO: Unify the process of backtranslating the replacement of multiple edges with singe edge
//       This is now almost exactly a copy of the process in SimpleChainSummarizer
InvalidityWitness NonLoopEliminator::BackTranslator::translate(InvalidityWitness witness) {
    if (this->removedNodes.empty()) { return witness; }

    using DerivationStep = InvalidityWitness::Derivation::DerivationStep;
    using ContractionInfo = std::pair<DirectedHyperEdge, std::pair<DirectedHyperEdge, DirectedHyperEdge>>;
    auto findContractionInfo = [&](EId eid) -> std::optional<ContractionInfo> {
        for (auto const & [node, contractionResult] : removedNodes) {
            for (auto const & [replacing, inout] : contractionResult.replacing) {
                if (replacing.id == eid) {
                    return std::make_pair(replacing,
                                          std::make_pair(contractionResult.incoming[inout.first],
                                                         contractionResult.outgoing[inout.second])
                                         );
                }
            }
        }
        return std::nullopt;
    };
    while(true) {
        auto & derivation = witness.getDerivation();
        // For each step, check if it uses one of the newly created edges
        bool stepReplaced = false;
        for (auto it = derivation.begin(); it != derivation.end(); ++it) {
            auto eid = it->clauseId;
            if (auto possibleContractInfo = findContractionInfo(eid); possibleContractInfo.has_value()) {
                auto const & contractionInfo = possibleContractInfo.value();
                std::vector<DirectedHyperEdge> chain = {contractionInfo.second.first, contractionInfo.second.second};
                auto const & replacingEdge = contractionInfo.first;
                // Replace this step with the sequence of steps corresponding to the summarized chain
                std::vector<DerivationStep> newSteps;
                // 1. Copy all the steps before the one to be replaced
                std::copy(derivation.begin(), it, std::back_inserter(newSteps));
                std::size_t firstShiftedIndex = newSteps.size();
                // 2. Replace the summarized step
                DerivationStep const & summarizedStep = *it;
                // 2a. Compute instances for the summarized nodes
                // 2aa. Compute path constraint
                vec<PTRef> edgeConstraints;
                std::vector<DirectedEdge> simpleChain;
                EdgeConverter converter(logic, predicateRepresentation);
                std::transform(chain.begin(), chain.end(), std::back_inserter(simpleChain), converter);
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
                SMTConfig config;
                MainSolver solver(logic, config, "");
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
                std::transform(it+1, derivation.end(), std::back_inserter(newSteps), [diff, firstShiftedIndex](auto const & step){
                    auto newStep = step;
                    for (auto & premiseIndex : newStep.premises) {
                        if (premiseIndex >= firstShiftedIndex) {
                            premiseIndex += diff;
                        }
                    }
                    newStep.index += diff;
                    return newStep;
                });
                // 4. Replace the derivation
                InvalidityWitness::Derivation newDerivation(std::move(newSteps));
                witness.setDerivation(std::move(newDerivation));
                stepReplaced = true;
                break;
            }
        }
        if (not stepReplaced) {
            break;
        }
    }
    return witness;
}

ValidityWitness NonLoopEliminator::BackTranslator::translate(ValidityWitness witness) {
    if (this->removedNodes.empty()) { return witness; }
    auto definitions = witness.getDefinitions();

    auto definitionFor = [&](SymRef vertex) {
        if (vertex == logic.getSym_false()) { return logic.getTerm_false(); }
        if (vertex == logic.getSym_true()) { return logic.getTerm_true(); }
        auto it = std::find_if(definitions.begin(), definitions.end(), [&](auto const & entry){
            return logic.getSymRef(entry.first) == vertex;
        });
        return it != definitions.end() ? it->second : PTRef_Undef;
    };
    VersionManager manager(logic);
    TermUtils utils(logic);
    for (auto && [vertex, entry] : this->removedNodes) {
        vec<PTRef> incomingFormulas;
        for (auto const & edge : entry.incoming) {
            if (edge.from.size() != 1) { throw std::logic_error("NonLoopEliminator should not have processed hyperEdges!"); }
            PTRef sourceDef = definitionFor(edge.from[0]);
            assert(sourceDef != PTRef_Undef);
            if (sourceDef == PTRef_Undef) { // Missing definition, cannot backtranslate
                return ValidityWitness{};
            }
            sourceDef = manager.baseFormulaToSource(sourceDef);
            incomingFormulas.push(logic.mkAnd(sourceDef, edge.fla.fla));
        }
        vec<PTRef> outgoingFormulas;
        for (auto const & edge : entry.outgoing) {
            if (edge.from.size() != 1) { throw std::logic_error("NonLoopEliminator should not have processed hyperEdges!"); }
            PTRef targetDef = definitionFor(edge.to);
            assert(targetDef != PTRef_Undef);
            if (targetDef == PTRef_Undef) { // Missing definition, cannot backtranslate
                return ValidityWitness{};
            }
            targetDef = manager.baseFormulaToTarget(targetDef);
            outgoingFormulas.push(logic.mkAnd(edge.fla.fla, logic.mkNot(targetDef)));
        }
        TermUtils::substitutions_map substitutionsMap;
        utils.mapFromPredicate(predicateRepresentation.getSourceTermFor(vertex), predicateRepresentation.getTargetTermFor(vertex), substitutionsMap);
        PTRef incomingPart = logic.mkOr(std::move(incomingFormulas));
        PTRef outgoingPart = logic.mkOr(std::move(outgoingFormulas));
        outgoingPart = utils.varSubstitute(outgoingPart, substitutionsMap);
        SMTConfig config;
        const char * msg;
        config.setOption(SMTConfig::o_produce_models, SMTOption(false), msg);
        config.setOption(SMTConfig::o_produce_inter, SMTOption(true), msg);
        MainSolver solver(logic, config, "solver");
        solver.insertFormula(incomingPart);
        solver.insertFormula(outgoingPart);
        auto res = solver.check();
        if (res != s_False) {
            throw std::logic_error("Error in backtranslating of nonloops elimination");
        }
        auto itpContext = solver.getInterpolationContext();
        vec<PTRef> itps;
        ipartitions_t Amask = 1;
        itpContext->getSingleInterpolant(itps, Amask);
        PTRef vertexSolution = manager.targetFormulaToBase(itps[0]);
        PTRef predicate = manager.sourceFormulaToBase(predicateRepresentation.getSourceTermFor(vertex));
        assert(definitions.count(predicate) == 0);
        definitions.insert({predicate, vertexSolution});
    }
    return ValidityWitness(std::move(definitions));
}

std::vector<SymRef> NonLoopEliminator::nonloopingVertices(ChcDirectedHyperGraph const & graph, AdjacencyListsGraphRepresentation const & adjancencyRepresentation) {
    std::vector<SymRef> nonLoopingVertices;
    ReverseDFS(graph, adjancencyRepresentation).run([&](SymRef vertex){
        if (vertex == graph.getEntry() or vertex == graph.getExit()) { return; }
        auto const & outgoing = adjancencyRepresentation.getOutgoingEdgesFor(vertex);
        if (std::none_of(outgoing.begin(), outgoing.end(), [&](EId eid) { return graph.getTarget(eid) == vertex; })) {
            nonLoopingVertices.push_back(vertex);
        }
    }, [](SymRef){});
    return nonLoopingVertices;
}