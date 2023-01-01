/*
 * Copyright (c) 2022, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "SimpleChainSummarizer.h"

Transformer::TransformationResult SimpleChainSummarizer::transform(std::unique_ptr<ChcDirectedHyperGraph> graph) {
    auto translator = std::make_unique<SimpleChainBackTranslator>(logic, graph->predicateRepresentation());
    while(true) {
        AdjacencyListsGraphRepresentation adjacencyList = AdjacencyListsGraphRepresentation::from(*graph);
        auto isTrivial = [&](SymRef sym) {
            auto const & incoming = adjacencyList.getIncomingEdgesFor(sym);
            if (incoming.size() != 1) { return false; }
            auto const & outgoing = adjacencyList.getOutgoingEdgesFor(sym);
            if (outgoing.size() != 1) { return false; }
            return graph->getSources(outgoing[0]).size() == 1 and graph->getSources(incoming[0]).size() == 1;
        };
        auto vertices = graph->getVertices();
        auto it = std::find_if(vertices.begin(), vertices.end(), isTrivial);
        if (it == vertices.end()) { break; }
        auto trivialVertex = *it;
        auto trivialChain = [&](SymRef vertex) {
            std::vector<EId> edges;
            auto current = vertex;
            do {
                auto const & outgoing = adjacencyList.getOutgoingEdgesFor(current);
                assert(outgoing.size() == 1);
                edges.push_back(outgoing[0]);
                current = graph->getTarget(outgoing[0]);
            } while (isTrivial(current));
            current = vertex;
            do {
                auto const & incoming = adjacencyList.getIncomingEdgesFor(current);
                assert(incoming.size() == 1);
                edges.insert(edges.begin(), incoming[0]);
                auto const & sources = graph->getSources(incoming[0]);
                assert(sources.size() == 1);
                current = sources[0];
            } while (isTrivial(current));
            return edges;
        }(trivialVertex);
        std::vector<DirectedHyperEdge> summarizedChain;
        std::transform(trivialChain.begin(), trivialChain.end(), std::back_inserter(summarizedChain), [&](EId eid) {
//            std::cout << "Edge in chain: " << logic.pp(graph->getEdgeLabel(eid)) << std::endl;
            return graph->getEdge(eid);
        });
        auto summaryEdge = graph->contractTrivialChain(trivialChain);
//        std::cout << "Summary edge: " << logic.pp(summaryEdge.fla.fla) << std::endl;
        translator->addSummarizedChain({summarizedChain, summaryEdge});
    }
    return {std::move(graph), std::move(translator)};
}

namespace{
class EdgeConverter {
    Logic & logic;
    TermUtils utils;
    TimeMachine timeMachine;
    VersionManager manager;
    NonlinearCanonicalPredicateRepresentation const & predicateRepresentation;
public:
    EdgeConverter(Logic & logic, NonlinearCanonicalPredicateRepresentation const & predicateRepresentation) :
    logic(logic), utils(logic), timeMachine(logic), manager(logic), predicateRepresentation(predicateRepresentation) {}

    DirectedEdge operator()(DirectedHyperEdge const & edge) {
        assert(edge.from.size() == 1);
        auto source = edge.from[0];
        auto target = edge.to;
        TermUtils::substitutions_map subst;
        {
            auto sourceVars = utils.predicateArgsInOrder(predicateRepresentation.getSourceTermFor(source));
            for (PTRef sourceVar : sourceVars) {
                PTRef newVar = timeMachine.getVarVersionZero(manager.toBase(sourceVar));
                subst.insert({sourceVar, newVar});
            }
        }
        {
            auto targetVars = utils.predicateArgsInOrder(predicateRepresentation.getTargetTermFor(target));
            for (PTRef targetVar : targetVars) {
                PTRef newVar = timeMachine.sendVarThroughTime(timeMachine.getVarVersionZero(manager.toBase(targetVar)), 1);
                subst.insert({targetVar, newVar});
            }
        }

        PTRef newLabel = TermUtils(logic).varSubstitute(edge.fla.fla, subst);
        return DirectedEdge{.from = edge.from[0], .to = edge.to, .fla = {newLabel}, .id = {edge.id}};
    }
};

class VersionedPredicate {
    Logic & logic;
    TermUtils utils;
    TimeMachine timeMachine;
    VersionManager manager;
    NonlinearCanonicalPredicateRepresentation const & predicateRepresentation;
public:
    VersionedPredicate(Logic & logic, NonlinearCanonicalPredicateRepresentation const & predicateRepresentation) :
        logic(logic), utils(logic), timeMachine(logic), manager(logic), predicateRepresentation(predicateRepresentation) {}

    PTRef operator()(SymRef predicateSymbol) {
        vec<PTRef> baseVars;
            auto sourceVars = utils.predicateArgsInOrder(predicateRepresentation.getSourceTermFor(predicateSymbol));
            for (PTRef sourceVar : sourceVars) {
                PTRef newVar = timeMachine.getVarVersionZero(manager.toBase(sourceVar));
                baseVars.push(newVar);
            }
        return logic.insertTerm(predicateSymbol, std::move(baseVars));
    }
};
}

InvalidityWitness SimpleChainSummarizer::SimpleChainBackTranslator::translate(InvalidityWitness witness) {
    if (summarizedChains.empty()) { return witness; }
    using DerivationStep = InvalidityWitness::Derivation::DerivationStep;

    for (auto const & chain : summarizedChains) {
        auto const & replacingEdge = chain.second;
        EId eid = replacingEdge.id;
        // replace all occurrences of this edge
        while(true) {
            auto const & derivation = witness.getDerivation();
            auto it = std::find_if(derivation.begin(), derivation.end(), [eid](auto const & step){ return step.clauseId == eid; });
            if (it == derivation.end()) { break; }
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
            std::transform(chain.first.begin(), chain.first.end(), std::back_inserter(simpleChain), converter);
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
        }
    }
    return witness;
}

ValidityWitness SimpleChainSummarizer::SimpleChainBackTranslator::translate(ValidityWitness witness) {
    if (summarizedChains.empty()) { return witness; }
    auto definitions = witness.getDefinitions();
    // TODO: assert that we have true and false already
    definitions.insert({logic.getTerm_true(), logic.getTerm_true()});
    definitions.insert({logic.getTerm_false(), logic.getTerm_false()});
    std::reverse(summarizedChains.begin(), summarizedChains.end());
    SMTConfig config;
    const char * msg;
    config.setOption(SMTConfig::o_produce_models, SMTOption(false), msg);
    config.setOption(SMTConfig::o_produce_inter, SMTOption(true), msg);
    TermUtils utils(logic);
    VersionManager manager(logic);
    for (auto && [chain, summary] : summarizedChains) {
        // Compute definitions for vertices on the chain using path interpolants
        MainSolver solver(logic, config, "labeler");
        assert(summary.from.size() == 1);
        PTRef sourceInterpretation = manager.baseFormulaToSource(
            definitions.at(manager.sourceFormulaToBase(predicateRepresentation.getSourceTermFor(summary.from.front())))
        );
        solver.insertFormula(sourceInterpretation);
        for (auto const & edge : chain) {
            TermUtils::substitutions_map substitutionsMap;
            auto target = edge.to;
            utils.mapFromPredicate(predicateRepresentation.getTargetTermFor(target), predicateRepresentation.getSourceTermFor(target), substitutionsMap);
            PTRef updatedLabel = utils.varSubstitute(edge.fla.fla, substitutionsMap);
            solver.insertFormula(updatedLabel);
        }
        PTRef predicate = predicateRepresentation.getSourceTermFor(summary.to);
        // MB: We cannot try to rewrite 0-ary predicates
        PTRef targetInterpretation = logic.isVar(predicate) ? definitions.at(predicate) : manager.baseFormulaToSource(
            definitions.at(manager.sourceFormulaToBase(predicate))
        );
        solver.insertFormula(logic.mkNot(targetInterpretation));
        auto res = solver.check();
        if (res != s_False) {
            //throw std::logic_error("SimpleChainBackTranslator could not recompute solution!");
            std::cerr << "; SimpleChainBackTranslator could not recompute solution! Solver could not prove UNSAT!" << std::endl;
            return ValidityWitness();
        }
        auto itpCtx = solver.getInterpolationContext();
        std::vector<ipartitions_t> partitionings;
        ipartitions_t p = 1;
        for (auto i = 0u; i < chain.size() - 1; ++i) {
            opensmt::setbit(p, i + 1); // MB: +1 for the source interpretation
            partitionings.push_back(p);
        }
        vec<PTRef> itps;
        itpCtx->getPathInterpolants(itps, partitionings);
        for (auto i = 0u; i < chain.size() - 1; ++i) {
            auto target = chain[i].to;
            PTRef predicate = predicateRepresentation.getSourceTermFor(target);
            predicate = logic.getPterm(predicate).size() > 0 ? VersionManager(logic).sourceFormulaToBase(predicate) : predicate;
            if (definitions.count(predicate) > 0) {
                std::cerr << "; Unexpected situation in SimpleChainBackTranslator: Predicate already has a solution!" << std::endl;
                return ValidityWitness();
            }
            definitions.insert({predicate, VersionManager(logic).sourceFormulaToBase(itps[i])});
        }
    }
    return ValidityWitness(std::move(definitions));
}
