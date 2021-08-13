//
// Created by Martin Blicha on 21.08.20.
//

#include "Validator.h"

Validator::Result Validator::validate(const ChcSystem & system, const SystemVerificationResult & result) {
    switch (result.getAnswer()) {
        case VerificationResult::SAFE:
            return validateValidityWitness(system, result.getValidityWitness());
            break;
            case VerificationResult::UNSAFE:
                return validateInvalidityWitness(system, result.getInvalidityWitness());
        default:
            return Validator::Result::NOT_VALIDATED;
    }
    if (result.getAnswer() == VerificationResult::SAFE) {

    }
    return Validator::Result::NOT_VALIDATED;
}

Validator::Result Validator::validateValidityWitness(const ChcDirectedGraph & graph, const ValidityWitness & witness) {
    auto edges = graph.getEdges();
    auto definitions = witness.getDefinitions();
    definitions.insert({logic.getTerm_true(), logic.getTerm_true()});
    definitions.insert({logic.getTerm_false(), logic.getTerm_false()});
    for (auto const & edge : edges) {
        VId from = graph.getSource(edge);
        VId to = graph.getTarget(edge);
        PTRef fla = graph.getEdgeLabel(edge);
        PTRef fromPredicate = graph.getStateVersion(from);
        PTRef toPredicate = graph.getStateVersion(to);
        if (definitions.count(fromPredicate) == 0 || definitions.count(toPredicate) == 0) {
            return Validator::Result::NOT_VALIDATED;
        }
        PTRef fromInterpreted = definitions.at(fromPredicate);
        PTRef toInterpreted = TimeMachine(logic).sendFlaThroughTime(definitions.at(toPredicate), 1);
        //  test validity of implication 'fromInterpreted and fla => toInterpreted'
        // equivalently test satisfiability of 'fromInterepted and fla and not(toInterpreted)'
        PTRef query = logic.mkAnd({fromInterpreted, fla, logic.mkNot(toInterpreted)});
        SMTConfig config;
        MainSolver solver(logic, config, "validator");
        solver.insertFormula(query);
        auto res = solver.check();
        if (res != s_False) {
            return Validator::Result::NOT_VALIDATED;
        }
    }
    return Validator::Result::VALIDATED;
}

Validator::Result Validator::validateValidityWitness(const ChcSystem & system, const ValidityWitness & witness) {
    auto definitions = witness.getDefinitions();
    if (definitions.find(logic.getTerm_false()) == definitions.end()) {
        definitions.insert({logic.getTerm_false(), logic.getTerm_false()});
    }
    TermUtils utils(logic);
    for (auto const & clause : system.getClauses()) {
        // build antecedent
        auto bodyPredicates = clause.body.uninterpretedPart;
        vec<PTRef> antecedentArgs;
        for (auto predicate : bodyPredicates) {
            PTRef predicateTerm = predicate.predicate;
            SymRef predicateSymbol = logic.getSymRef(predicateTerm);
            auto it = std::find_if(definitions.begin(), definitions.end(),
                                   [this, predicateSymbol](decltype(definitions)::value_type const & entry) {
               return logic.getSymRef(entry.first) == predicateSymbol;
            });
            if (it == definitions.end()) {
                std::cerr << ";Missing definition of a predicate " << logic.printTerm(predicateTerm) << std::endl;
                return Validator::Result::NOT_VALIDATED;
            }
            // we need to substitute real arguments in the definition of the predicate
            PTRef definitionTemplate = it->second;
            // build the substitution map
            std::unordered_map<PTRef, PTRef, PTRefHash> subst;
            utils.insertVarPairsFromPredicates(it->first, predicateTerm, subst);
            PTRef interpretedDefinition = utils.varSubstitute(definitionTemplate, subst);
            antecedentArgs.push(interpretedDefinition);
        }
        antecedentArgs.push(clause.body.interpretedPart.fla);
        PTRef antecedent = logic.mkAnd(antecedentArgs);
        // build consequent
        PTRef predicateTerm = clause.head.predicate.predicate;
        SymRef predicateSymbol = logic.getSymRef(predicateTerm);
        auto it = std::find_if(definitions.begin(), definitions.end(),
                               [this, predicateSymbol](decltype(definitions)::value_type const & entry) {
                                   return logic.getSymRef(entry.first) == predicateSymbol;
                               });
        if (it == definitions.end()) {
            std::cerr << ";Missing definition of a predicate " << logic.printTerm(predicateTerm) << std::endl;
            return Validator::Result::NOT_VALIDATED;
        }
        // we need to substitute real arguments in the definition of the predicate
        PTRef definitionTemplate = it->second;
        // build the substitution map
        auto formalArgs = utils.getVarsFromPredicateInOrder(it->first);
        auto realArgs = utils.getVarsFromPredicateInOrder(predicateTerm);
        assert(formalArgs.size() == realArgs.size());
        std::unordered_map<PTRef, PTRef, PTRefHash> subst;
        for (int i = 0; i < formalArgs.size(); ++i) {
            subst.insert({formalArgs[i], realArgs[i]});
        }
        PTRef consequent = utils.varSubstitute(definitionTemplate, subst);
        // check the validity of implication
        PTRef query = logic.mkAnd(antecedent, logic.mkNot(consequent));
        SMTConfig config;
        MainSolver solver(logic, config, "validator");
        solver.insertFormula(query);
        auto res = solver.check();
        if (res != s_False) {

            std::cerr << ";Clause ";
            ChcPrinter(logic, std::cerr).print(clause);
            std::cerr << " not valid" << std::endl;
            return Validator::Result::NOT_VALIDATED;
        }
    }
    return Validator::Result::VALIDATED;
}


namespace{
using Derivation = SystemInvalidityWitness::Derivation;
using DerivationStep = Derivation::DerivationStep;
bool isCorrectlyDerived(DerivationStep const & step, Derivation const & derivation, Logic & logic) {
    assert(step.type == DerivationStep::StepType::DERIVED);
    // Head of this step's clause should be the head of nucleus' head
    DerivationStep const & nucleus = derivation[step.nucleus];
    if (nucleus.clause.head != step.clause.head) { return false; }
    // uninterpreted predicates of nucleus must be the heads of satellites
    std::vector<UninterpretedPredicate> satellites;
    for (auto index : step.satellites) {
        satellites.push_back(derivation[index].clause.head.predicate);
    }
    // there must be exact match between satellites and UPs in body of nucleus
    if (satellites.size() != nucleus.clause.body.uninterpretedPart.size()) { return false; }
    for (auto const & bodyUP : nucleus.clause.body.uninterpretedPart) {
        if (std::find(satellites.begin(), satellites.end(), bodyUP) == satellites.end()) { return false; }
    }
    for (auto const & satellite : satellites) {
        if (std::find(nucleus.clause.body.uninterpretedPart.begin(), nucleus.clause.body.uninterpretedPart.end(), satellite) == nucleus.clause.body.uninterpretedPart.end()) { return false; }
    }
    // uninterpreted part of derived should be the collection of uninterpreted parts of satellites (in our case, actually empty)
    std::vector<UninterpretedPredicate> satellitesUninterpretedBodies;
    for (auto index : step.satellites) {
        for (auto const & UP : derivation[index].clause.body.uninterpretedPart) {
            satellitesUninterpretedBodies.push_back(UP);
        }
    }
    if (satellitesUninterpretedBodies.size() != step.clause.body.uninterpretedPart.size()) { return false; }
    for (std::size_t i = 0; i < satellitesUninterpretedBodies.size(); ++i) {
        if (satellitesUninterpretedBodies[i] != step.clause.body.uninterpretedPart[i]) { return false; }
    }

    // interpreted part must match
    vec<PTRef> interpretedParts;
    for (auto index : step.satellites) {
        interpretedParts.push(derivation[index].clause.body.interpretedPart.fla);
    }
    interpretedParts.push(nucleus.clause.body.interpretedPart.fla);
    return logic.mkAnd(interpretedParts) == step.clause.body.interpretedPart.fla;
}
}

Validator::Result
Validator::validateInvalidityWitness(const ChcSystem & system, const SystemInvalidityWitness & witness) {
    auto & derivation = witness.getDerivation();
    auto & model = witness.getModel();
    auto derivationSize = derivation.size();
    if (derivationSize == 0) { return Result::NOT_VALIDATED; }
    for (std::size_t i = 0; i < derivationSize; ++i) {
        auto & step = derivation[i];
        bool stepValidated = false;
        switch (step.type) {
            case decltype(step.type)::INPUT:
                // validate input clause
                stepValidated = isPresentInSystem(step.clause, system);
                break;
            case decltype(step.type)::DERIVED:
                // validate derived clause
                stepValidated = isCorrectlyDerived(step, derivation, logic);
                break;
            default:
                assert(false);
                return Validator::Result::NOT_VALIDATED;
        }
        if (not stepValidated) { return Validator::Result::NOT_VALIDATED; }
    }
    // check if the last clause is interpreted formula and model falsifies it
    ChClause const & derived = derivation.last().clause;
    bool hasOnlyInterpretedBody = [this](ChClause const & clause) {
        auto const & uninterpreted = clause.body.uninterpretedPart;
        return uninterpreted.empty() || (uninterpreted.size() == 1 && uninterpreted[0].predicate == logic.getTerm_true());
    }(derived);
    bool hasEmptyHead = derived.head.predicate.predicate == logic.getTerm_false();
    if (not hasOnlyInterpretedBody || not hasEmptyHead) { return Validator::Result::NOT_VALIDATED; }
    // Now we know it is of form '\phi \implies \bot' (in other words 'F => false')
    // This is falsified if the interpreted part is satisfied
    PTRef value = model.evaluate(derived.body.interpretedPart.fla);
    if (value != logic.getTerm_true()) { return Validator::Result::NOT_VALIDATED; }
    return Validator::Result::VALIDATED;
}

namespace {
// return true if 'c1' is an instance of 'c2'
bool isInstanceOf(const ChClause & c1, const ChClause & c2, Logic & logic) {
    if (c1.body.uninterpretedPart.size() != c2.body.uninterpretedPart.size()) { return false; }
    using UPPair = std::pair<UninterpretedPredicate, UninterpretedPredicate>;
    std::vector<UPPair> upsToProcess;
    upsToProcess.emplace_back(c1.head.predicate, c2.head.predicate);
    std::transform(c1.body.uninterpretedPart.begin(), c1.body.uninterpretedPart.end(),
                   c2.body.uninterpretedPart.begin(), std::back_inserter(upsToProcess),
                   [](UninterpretedPredicate up1, UninterpretedPredicate up2) {
       return std::make_pair(up1, up2);
    });
    auto hasSameSymbol = [&logic](UPPair const & pair) {
        return logic.getSymRef(pair.first.predicate) == logic.getSymRef(pair.second.predicate);
    };
    bool predicatesMatch = std::all_of(upsToProcess.begin(), upsToProcess.end(), hasSameSymbol);
    if (not predicatesMatch) { return false; }
    TimeMachine timeMachine(logic);
    TermUtils utils(logic);

    using subst_map = std::unordered_map<PTRef, PTRef, PTRefHash>;
    subst_map subst; // substitution map from c2 -> c1
    for (auto const & uppair : upsToProcess) {
        utils.insertVarPairsFromPredicates(uppair.second.predicate, uppair.first.predicate, subst);
    }
    // c1 and c2 should be the same, up to renaming of the variables
    // Here we enforce stronger invariant: they have just different version of the variables
    std::vector<int> versionDiffs;
    std::transform(subst.begin(), subst.end(), std::back_inserter(versionDiffs),
                   [&timeMachine](decltype(subst)::value_type const & entry) {
       int version = timeMachine.getVersionNumber(entry.first); // version in c2
       return version - timeMachine.getVersionNumber(entry.second); // c2 - c1
    });
    if (versionDiffs.empty()) {
        // ??? What to do in this case?
        return false;
    }
    int expectedVersionDiff = versionDiffs[0]; // version diff of (c2 - c1) => c2 = c1 + versionDiff
    if (std::any_of(versionDiffs.begin(), versionDiffs.end(), [expectedVersionDiff](int diff) { return diff != expectedVersionDiff; })) {
        return false;
    }
    PTRef modified_c1 = timeMachine.sendFlaThroughTime(c1.body.interpretedPart.fla, expectedVersionDiff);
    return c2.body.interpretedPart.fla == modified_c1;

}
}

bool Validator::isPresentInSystem(const ChClause & clause, const ChcSystem & system) const {
    for (auto const systemClause : system.getClauses()) {
        if (isInstanceOf(clause, systemClause, logic)) { return true; }
    }
    return false;
}
