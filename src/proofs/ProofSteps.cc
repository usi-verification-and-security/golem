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

    if (type == StepType::ASSUME) {
        ss << "assume t";
    } else if (type == StepType::STEP) {
        ss << "step t";
    }

    ss << stepId;

    if (type != StepType::ASSUME) { ss << " (cl"; }

    if (not clause.empty()) {
        ss << " ";
        for (std::size_t i = 0; i < clause.size(); i++) {
            ss << clause[i]->printTerm();
            if (i != clause.size() - 1) { ss << " "; }
        }
    }

    if (type != StepType::ASSUME) { ss << ")"; }

    if (rule != " ") { ss << " :rule " << rule; }

    auto const & premiseNumbers = premises.premises;
    if (not premiseNumbers.empty()) {
        ss << " :premises (";
        for (std::size_t i = 0; i < premiseNumbers.size(); i++) {
            ss << "t" << premiseNumbers[i];
            if (i != premiseNumbers.size() - 1) { ss << " "; }
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

    if (not premises.premises.empty()) {
        ss << " :premises ";
        for (auto premise : premises.premises) {
            ss << premise << " ";
        }
    }

    ss << "\n";

    return ss.str();
}

namespace {
std::vector<std::shared_ptr<Term>> literals(std::shared_ptr<Term> const & term) {
    return std::vector{term};
}

std::vector<std::shared_ptr<Term>> literals(std::shared_ptr<Term> const & term1, std::shared_ptr<Term> const & term2) {
    return std::vector{term1, term2};
}

std::vector<std::shared_ptr<Term>> args(std::shared_ptr<Term> const & term1, std::shared_ptr<Term> const & term2) {
    return std::vector{term1, term2};
}

std::shared_ptr<Term> negate(std::shared_ptr<Term> const & arg) {
    return std::make_shared<Op>("not", std::vector{arg});
}

std::shared_ptr<Terminal> makeName(std::string name) {
    return std::make_shared<Terminal>(std::move(name), Terminal::UNDECLARED);
}
} // namespace

void StepHandler::recordStep(std::vector<TermPtr> && clause, std::string rule, Step::Premises && premises) {
    notifyObservers(Step{currentStep++, Step::StepType::STEP, std::move(clause), std::move(rule), std::move(premises)});
}

void StepHandler::recordForallInstStep(std::vector<TermPtr> && clause, InstantiationPairs && instantiationPairs) {
    notifyObservers(
        Step{currentStep++, Step::StepType::STEP, std::move(clause), "forall_inst", std::move(instantiationPairs)});
}

void StepHandler::recordAssumption(std::vector<std::shared_ptr<Term>> && clause) {
    notifyObservers(Step{currentStep++, Step::StepType::ASSUME, std::move(clause)});
}

void StepHandler::buildIntermediateProof() {
    std::unordered_map<std::size_t, std::size_t> coarseStepToIntermediateStep;
    auto derivationSize = derivation.size();

    for (std::size_t i = 0; i < derivationSize; ++i) {
        auto const & step = derivation[i];

        if (step.premises.empty()) { continue; }

        auto clause = originalAssertions[step.clauseId.id];
        auto instPairs = getInstPairs(i, normalizingEqualities[step.clauseId.id]);

        auto instantiated = clause;
        if (not instPairs.empty()) {
            notifyObservers(Step(currentStep, Step::StepType::STEP, literals(clause), "forall_inst", instPairs));
            currentStep++;
            InstantiateVisitor instantiateVisitor(instPairs);
            instantiated = clause->accept(&instantiateVisitor);
        }
        notifyObservers(Step(currentStep, Step::StepType::STEP, literals(instantiated)));
        currentStep++;

        std::stringstream premises;
        for (std::size_t j = 0; j < step.premises.size(); j++) {
            premises << logic.printTerm(derivation[step.premises[j]].derivedFact);
            if (j < step.premises.size() - 1) { premises << ' '; }
        }

        notifyObservers(
            Step(currentStep, Step::StepType::STEP,
                 literals(std::make_shared<Op>(
                     "=>", literals(std::make_shared<Terminal>(premises.str(), Term::VAR),
                                    std::make_shared<Terminal>(logic.printTerm(step.derivedFact), Term::VAR))))));
        currentStep++;

        std::vector<std::size_t> requiredMP;
        for (std::size_t premise : step.premises) {
            if (premise == 0) { continue; } // This is the helper fact "true", we do not include it in the proof
            assert(coarseStepToIntermediateStep.find(premise) != coarseStepToIntermediateStep.end());
            requiredMP.push_back(coarseStepToIntermediateStep.at(premise));
        }

        notifyObservers(Step(currentStep, Step::StepType::STEP,
                             literals(std::make_shared<Terminal>(logic.printTerm(step.derivedFact), Term::VAR)),
                             "resolution", Step::Premises{std::move(requiredMP)}));

        coarseStepToIntermediateStep.insert({i, currentStep});
        currentStep++;
    }
}

/**
 * Constructs Alethe proof from the coarse derivation.
 * Each step of the coarse derivation knows what fact it derived, what were the premises and what clause was used.
 *
 * Prelude: Construct the assumption steps. These are just copied original assertions (we currently inline lets)
 * Main proof: Expand each step from the coarse proof in the following way:
 *  1. Insert steps to derive required instance of the used clause (this may require removing unused quantifiers first)
 *  2. Turn the implication into a clause with "implies" rule. TODO: What if it is not an implication?
 *  3. Add steps to prove that "LHS = LHS simplified"
 *  4. Add a step to derive LHS simplified (with already derived premises recorded in the coarse-proof step)
 *  5. Add a step to derive LHS
 *  6. Add a step to derive RHS from 5. and 2.
 *  7. Add steps to prove that "RHS = RHS simplified"
 *  8. Derive RHS simplified from 6. and 7. (this a the derived fact of the coarse-proof step)
 */
void StepHandler::buildAletheProof() {

    buildAssumptionSteps();

    auto derivationSize = derivation.size();
    // MB: This could be a vector, but we have extra step in the coarse proof, so we would have to be careful about -1
    std::unordered_map<std::size_t, std::size_t> coarseStepToAletheStep;

    for (std::size_t i = 0; i < derivationSize; ++i) {
        auto const & step = derivation[i];
        assert(step.index == i);

        // Skip the helper step of deriving "true"
        if (step.premises.empty()) {
            assert(step.derivedFact == logic.getTerm_true());
            continue;
        }

        auto instantiatedClause = instantiationSteps(i, originalAssertions[step.clauseId.id]);
        auto implication = std::dynamic_pointer_cast<Op>(instantiatedClause);
        auto implicationLHS = implication->getArgs()[0];
        auto implicationRHS = implication->getArgs()[1];

        recordStep(literals(negate(std::make_shared<Op>(
                                "!", literals(implicationLHS, makeName(":named @LHS" + std::to_string(i - 1))))),
                            implicationRHS),
                   "implies", Step::Premises{lastStep()});
        auto implicationStep = lastStep();

        std::shared_ptr<Term> renamedImpLHS = makeName("@LHS" + std::to_string(i - 1));

        std::vector<std::size_t> requiredMP;
        for (auto premise : step.premises) {
            if (premise == 0) { continue; } // This is the helper fact "true", we do not include it in the proof
            assert(coarseStepToAletheStep.find(premise) != coarseStepToAletheStep.end());
            requiredMP.push_back(coarseStepToAletheStep.at(premise));
        }
        auto simplificationResult = simplify(implicationLHS, renamedImpLHS);
        std::size_t LHSderivationStep = 0;
        if (simplificationResult) { // LHS has been simplified
            auto simplifiedLHS = simplificationResult->first;
            auto equivStep = lastStep();
            auto simplifiedLHSderivationStep = deriveLHSWithoutConstraint(simplifiedLHS, std::move(requiredMP));
            recordStep(literals(renamedImpLHS, negate(simplifiedLHS)), "equiv2", Step::Premises{equivStep});
            recordStep(literals(renamedImpLHS), "resolution", Step::Premises{simplifiedLHSderivationStep, lastStep()});
            LHSderivationStep = lastStep();
        } else {
            // TODO: Use name whenever possible
            LHSderivationStep = deriveLHSWithoutConstraint(implicationLHS, std::move(requiredMP));
        }

        // We have derived LHS, now derive RHS with resolution
        recordStep(literals(implicationRHS), "resolution", Step::Premises{implicationStep, LHSderivationStep});
        auto RHSderivationStep = lastStep();
        // Now derive simplified RHS, which is the fact of the coarse-proof step
        auto rhsSimplificationResult = simplify(implicationRHS);
        if (rhsSimplificationResult) {
            auto simplifiedRHS = rhsSimplificationResult->first;
            assert(simplifiedRHS->printTerm() == logic.printTerm(step.derivedFact));
            recordStep(literals(negate(implicationRHS), simplifiedRHS), "equiv1", Step::Premises{lastStep()});
            recordStep(literals(simplifiedRHS), "resolution", Step::Premises{lastStep(), RHSderivationStep});
        }
        coarseStepToAletheStep.insert({i, lastStep()});
    }

    recordStep(literals(std::make_shared<Terminal>("(not false)", Term::UNDECLARED)), "false", {});
    // Final step deriving empty clause
    recordStep({}, "resolution", Step::Premises{currentStep - 2, currentStep - 1});
}

StepHandler::SimplifyResult StepHandler::simplify(TermPtr const & term, std::optional<TermPtr> name) {
    auto type = term->getTermType();
    if (type == Term::LET or type == Term::QUANT) {
        throw std::logic_error("Let and quantified term should not occur here anymore!");
    }
    if (type == Term::TERMINAL) { return std::nullopt; }
    assert(type == Term::APP or type == Term::OP);
    // Recursively simplify all arguments
    auto simplifyArgs = [this](std::vector<TermPtr> const & args) {
        std::vector<SimplifyResult> results;
        for (auto const & arg : args) {
            auto res = simplify(arg);
            results.push_back(std::move(res));
        }
        return results;
    };

    // Create simplified
    auto processResults = [this](TermPtr const & term, std::optional<TermPtr> & name,
                                 std::vector<SimplifyResult> const & results) {
        bool isApp = term->getTermType() == Term::APP;
        auto const & args =
            isApp ? std::dynamic_pointer_cast<App>(term)->getArgs() : std::dynamic_pointer_cast<Op>(term)->getArgs();
        std::vector<TermPtr> newArgs;
        Step::Premises premises;
        for (std::size_t i = 0; i < results.size(); ++i) {
            auto const & res = results[i];
            if (res) {
                premises.premises.push_back(res->second);
                newArgs.push_back(res->first);
            } else {
                newArgs.push_back(args[i]);
            }
        }
        TermPtr simplifiedTerm =
            term->getTermType() == Term::APP
                ? std::static_pointer_cast<Term>(
                      std::make_shared<App>(std::dynamic_pointer_cast<App>(term)->getFun(), std::move(newArgs)))
                : std::static_pointer_cast<Term>(
                      std::make_shared<Op>(std::dynamic_pointer_cast<Op>(term)->getOp(), std::move(newArgs)));
        auto namedTerm = name.has_value()
                             ? name.value()
                             : std::make_shared<Op>(
                                   "!", std::vector<TermPtr>{term, makeName(":named @T" + std::to_string(nameIndex))});
        if (not name.has_value()) { name = makeName("@T" + std::to_string(nameIndex++)); }
        auto congruenceTerm = std::make_shared<Op>("=", std::vector<TermPtr>{namedTerm, simplifiedTerm});
        recordStep(literals(congruenceTerm), "cong", std::move(premises));
        return simplifiedTerm;
    };
    if (type == Term::APP) { // Uninterpreted predicate
        auto app = std::dynamic_pointer_cast<App>(term);
        auto const & args = app->getArgs();
        auto results = simplifyArgs(args);
        if (std::none_of(results.begin(), results.end(), [](auto const & result) { return result.has_value(); })) {
            return std::nullopt;
        }
        auto simplifiedTerm = processResults(term, name, results);
        return std::make_pair(simplifiedTerm, lastStep());
    }
    if (type == Term::OP) {
        // First recursively simplify arguments
        auto op = std::dynamic_pointer_cast<Op>(term);
        if (op->getOp() == "ite") { return shortCircuitSimplifyITE(op); }
        auto const & args = op->getArgs();
        auto results = simplifyArgs(args);
        bool changed =
            std::any_of(results.begin(), results.end(), [](auto const & result) { return result.has_value(); });
        TermPtr opWithArgsSimplified = op;
        std::size_t firstEquivStep = -1;
        if (changed) {
            opWithArgsSimplified = processResults(term, name, results);
            firstEquivStep = lastStep();
        }
        auto evaluatedTerm = simplifyOpDirect(std::dynamic_pointer_cast<Op>(opWithArgsSimplified));
        if (changed) { // Derive that the original op is equiv to evaluatedTerm by transitivity
            assert(firstEquivStep != static_cast<std::size_t>(-1));
            assert(name.has_value());
            recordStep(literals(std::make_shared<Op>("=", std::vector<TermPtr>{name.value(), evaluatedTerm})), "trans",
                       {firstEquivStep, lastStep()});
        }
        return std::make_pair(evaluatedTerm, lastStep());
    }
    assert(false);
    throw std::logic_error("Unreachable!");
}

StepHandler::SimplifyResult StepHandler::shortCircuitSimplifyITE(std::shared_ptr<Op> const & ite) {
    assert(ite->getOp() == "ite");
    auto const & args = ite->getArgs();
    assert(args.size() == 3);
    Step::Premises finalPremises;
    // First evaluate the condition
    auto res = simplify(args[0]);
    auto conditionSimplified = args[0];
    auto iteSimplified = ite;
    if (res) {
        conditionSimplified = res->first;
        iteSimplified = std::make_shared<Op>("ite", std::vector{conditionSimplified, args[1], args[2]});
        recordStep(literals(std::make_shared<Op>("=", std::vector<TermPtr>{ite, iteSimplified})), "cong",
                   Step::Premises{res->second});
        finalPremises.premises.push_back(lastStep());
    }
    assert(conditionSimplified->getTermType() == Term::TERMINAL and
           conditionSimplified->getTerminalType() == Term::BOOL);
    auto const & val = std::dynamic_pointer_cast<Terminal>(conditionSimplified)->getVal();
    assert(val == "true" or val == "false");
    auto branch = val == "true" ? args[1] : args[2];
    recordStep(literals(std::make_shared<Op>("=", std::vector<TermPtr>{iteSimplified, branch})), "ite_simplify", {});
    finalPremises.premises.push_back(lastStep());
    auto branchSimplificationResult = simplify(branch);
    auto simplified = branch;
    if (branchSimplificationResult) {
        simplified = branchSimplificationResult->first;
        finalPremises.premises.push_back(branchSimplificationResult->second);
    }
    if (branchSimplificationResult or res) {
        assert(finalPremises.premises.size() >= 2);
        recordStep(literals(std::make_shared<Op>("=", std::vector<TermPtr>{ite, simplified})), "trans",
                   std::move(finalPremises));
    }
    return std::make_pair(simplified, lastStep());
}

namespace {
// NOTE: The semantics of div and modulo operation in OpenSMT's FastRationals is different from the semantics defined by
// SMT-LIB. We must use the computation according to SMT-LIB.
// See notes in // https://smtlib.cs.uiowa.edu/theories-Ints.shtml

// "Regardless of sign of m,
//  when n is positive, (div m n) is the floor of the rational number m/n;
//  when n is negative, (div m n) is the ceiling of m/n."
//  Remainder is then always a positive number r such that m = n * q + r, r < abs(n)

struct DivModPair {
    FastRational div;
    FastRational mod;
};
auto smtlib_divmod(FastRational const & m, FastRational const & n) -> DivModPair {
    auto ratio = m / n;
    auto q = n > 0 ? ratio.floor() : ratio.ceil();
    auto r = m - n * q;
    assert(r.isInteger() and r.sign() >= 0 and r < abs(n));
    return {q, r};
}

} // namespace

StepHandler::TermPtr StepHandler::simplifyOpDirect(std::shared_ptr<Op> const & opTerm) {
    auto const & op = opTerm->getOp();
    auto const & args = opTerm->getArgs();

    auto argAsNumber = [](auto const & arg) -> FastRational {
        assert(arg->getTerminalType() == Term::REAL or arg->getTerminalType() == Term::INT);
        auto const & str = std::dynamic_pointer_cast<Terminal>(arg)->getVal();
        // We have negated numbers represented in SMT-LIB format :(
        if (str.rfind("(-", 0) == 0) {
            auto positive = str.substr(3);
            assert(positive.size() > 0);
            positive.pop_back();
            return -FastRational(positive.c_str());
        }
        return FastRational(str.c_str());
    };
    auto argsAsNumbers = [&]() -> std::pair<FastRational, FastRational> {
        assert(args.size() == 2);
        return std::make_pair(argAsNumber(args[0]), argAsNumber(args[1]));
    };

    auto boolToString = [](bool b) { return b ? "true" : "false"; };

    auto numberAsTerminal = [](FastRational && num, Term::terminalType type) {
        if (isNegative(num)) {
            num.negate();
            return std::make_shared<Terminal>("(- " + num.get_str() + ")", type);
        }
        return std::make_shared<Terminal>(num.get_str(), type);
    };

    TermPtr simplified;
    std::string rule;

    if (op == "=") {
        assert(args[0]->getTermType() == Term::TERMINAL and args[0]->getTerminalType() != Term::VAR);
        assert(args[1]->getTermType() == Term::TERMINAL and args[1]->getTerminalType() != Term::VAR);
        bool equal = args[0]->printTerm() == args[1]->printTerm();
        simplified = std::make_shared<Terminal>(boolToString(equal), Term::BOOL);
        rule = args[0]->getTerminalType() == Term::BOOL ? "equiv_simplify" : "eq_simplify";
    } else if (op == "<" or op == "<=") {
        auto [lhs, rhs] = argsAsNumbers();
        bool isTrue = lhs < rhs or (op == "<=" and lhs == rhs);
        simplified = std::make_shared<Terminal>(boolToString(isTrue), Term::BOOL);
        rule = "comp_simplify";
    } else if (op == ">") {
        auto inner = std::make_shared<Op>("<=", args);
        auto negated = std::make_shared<Op>("not", std::vector<std::shared_ptr<Term>>{inner});
        recordStep(literals(std::make_shared<Op>("=", std::vector<TermPtr>{opTerm, negated})), "comp_simplify", {});
        auto firstEq = lastStep();
        auto innerSimplified = simplifyOpDirect(inner);
        auto innerSimplifiedNegated = std::make_shared<Op>("not", std::vector<std::shared_ptr<Term>>{innerSimplified});
        recordStep(literals(std::make_shared<Op>("=", std::vector<TermPtr>{negated, innerSimplifiedNegated})), "cong",
                   {lastStep()});
        auto secondEq = lastStep();
        simplified = simplifyOpDirect(innerSimplifiedNegated);
        recordStep(literals(std::make_shared<Op>("=", std::vector<TermPtr>{opTerm, simplified})), "trans",
                   {firstEq, secondEq, lastStep()});
        return simplified;
    } else if (op == ">=") {
        assert(args.size() == 2);
        auto swapped = std::make_shared<Op>("<=", std::vector{args[1], args[0]});
        recordStep(literals(std::make_shared<Op>("=", std::vector<TermPtr>{opTerm, swapped})), "comp_simplify", {});
        auto firstEq = lastStep();
        simplified = simplifyOpDirect(swapped);
        recordStep(literals(std::make_shared<Op>("=", std::vector<TermPtr>{opTerm, simplified})), "trans",
                   Step::Premises{firstEq, lastStep()});
        return simplified;
    } else if (op == "and") {
        std::vector<std::shared_ptr<Term>> newArgs;
        for (auto const & arg : args) {
            if (arg->getTermType() == Term::TERMINAL and arg->getTerminalType() != Term::VAR) {
                assert(arg->getTerminalType() == Term::BOOL);
                auto const & val = std::dynamic_pointer_cast<Terminal>(arg)->getVal();
                assert(val == "true" or val == "false");
                if (val == "false") {
                    recordStep(literals(std::make_shared<Op>("=", ::args(opTerm, arg))), "and_simplify", {});
                    return arg;
                }
                // We skip "true" argument
            } else {
                newArgs.push_back(arg);
            }
        }
        if (newArgs.empty()) {
            simplified = std::make_shared<Terminal>("true", Term::BOOL);
        } else if (newArgs.size() == 1) {
            simplified = newArgs[0];
        } else {
            simplified = std::make_shared<Op>("and", std::move(newArgs));
        }
        rule = "and_simplify";
    } else if (op == "or") {
        bool isTrue = std::any_of(args.begin(), args.end(), [](auto const & arg) {
            return arg->getTerminalType() == Term::BOOL and
                   std::dynamic_pointer_cast<Terminal>(arg)->getVal() == "true";
        });
        if (not isTrue) {
            assert(std::all_of(args.begin(), args.end(), [](auto const & arg) {
                return arg->getTerminalType() == Term::BOOL and
                       std::dynamic_pointer_cast<Terminal>(arg)->getVal() == "false";
            }));
        }
        simplified = std::make_shared<Terminal>(boolToString(isTrue), Term::BOOL);
        rule = "or_simplify";
    } else if (op == "not") {
        assert(args[0]->getTermType() == Term::TERMINAL and args[0]->getTerminalType() == Term::BOOL);
        auto const & val = std::dynamic_pointer_cast<Terminal>(args[0])->getVal();
        assert(val == "true" or val == "false");
        simplified = std::make_shared<Terminal>(val == "false" ? "true" : "false", Term::BOOL);
        rule = "not_simplify";
    } else if (op == "ite") {
        assert(args[0]->getTermType() == Term::TERMINAL and args[0]->getTerminalType() == Term::BOOL);
        auto const & val = std::dynamic_pointer_cast<Terminal>(args[0])->getVal();
        simplified = val == "true" ? args[1] : args[2];
        rule = "ite_simplify";
    } else if (op == "+") {
        FastRational result = 0;
        for (auto const & arg : args) {
            result += argAsNumber(arg);
        }
        Term::terminalType type = args[0]->getTerminalType();
        simplified = numberAsTerminal(std::move(result), type);
        rule = "sum_simplify";
    } else if (op == "-") {
        auto [lhs, rhs] = argsAsNumbers();
        Term::terminalType type = args[0]->getTerminalType();
        FastRational result = lhs - rhs;
        simplified = numberAsTerminal(std::move(result), type);
        rule = "minus_simplify";
    } else if (op == "/") {
        auto [lhs, rhs] = argsAsNumbers();
        FastRational result = lhs / rhs;
        simplified = numberAsTerminal(std::move(result), Term::REAL);
        rule = "div_simplify";
    } else if (op == "*") {
        auto [lhs, rhs] = argsAsNumbers();
        Term::terminalType type = args[0]->getTerminalType();
        FastRational result = lhs * rhs;
        simplified = numberAsTerminal(std::move(result), type);
        rule = "prod_simplify";
    } else if (op == "mod") {
        auto [lhs, rhs] = argsAsNumbers();
        FastRational result = smtlib_divmod(lhs, rhs).mod;
        simplified = std::make_shared<Terminal>(result.get_str(), Term::INT);
        rule = "mod_simplify";
    } else if (op == "div") {
        auto [lhs, rhs] = argsAsNumbers();
        FastRational result = smtlib_divmod(lhs, rhs).div;
        simplified = numberAsTerminal(std::move(result), Term::INT);
        rule = "div_simplify";
    } else {
        throw std::logic_error("Unhandled case in simplifying Op");
    }
    recordStep(literals(std::make_shared<Op>("=", std::vector<TermPtr>{opTerm, simplified})), std::move(rule), {});
    return simplified;
}

namespace {
class CollectVariables : public VoidVisitor {
public:
    std::unordered_set<std::string> varsInUse;

    void visit(Terminal * term) override {
        if (term->getTerminalType() == Term::VAR) {
            auto termStr = term->printTerm();
            varsInUse.insert(termStr);
        }
    }

    void visit(Op * term) override {
        for (auto const & arg : term->getArgs()) {
            arg->accept(this);
        }
    }

    void visit(App * term) override {
        for (auto const & arg : term->getArgs()) {
            arg->accept(this);
        }
    }
    void visit(Quant *) override { throw std::logic_error("Should not encounter quantifier at this point!"); };
    void visit(Let *) override { throw std::logic_error("Should not encounter let terms here!"); }
};

std::pair<std::shared_ptr<Term>, bool> removeUnusedQuantifiers(std::shared_ptr<Term> const & term) {
    if (term->getTermType() != Term::QUANT) { return {term, false}; }
    auto quantifiedTerm = std::dynamic_pointer_cast<Quant>(term);
    CollectVariables collector;
    quantifiedTerm->getCoreTerm()->accept(&collector);
    auto const & varsInUse = collector.varsInUse;

    std::vector<std::shared_ptr<Term>> newVars;
    std::vector<std::shared_ptr<Term>> newSorts;
    auto const & vars = quantifiedTerm->getVars();
    auto const & sorts = quantifiedTerm->getSorts();
    for (std::size_t i = 0; i < vars.size(); ++i) {
        auto varStr = vars[i]->printTerm();
        auto it = varsInUse.find(varStr);
        if (it != varsInUse.end()) {
            newVars.push_back(vars[i]);
            newSorts.push_back(sorts[i]);
        }
    }
    if (newVars.empty()) { return {quantifiedTerm->getCoreTerm(), true}; }
    if (newVars.size() == vars.size()) { return {term, false}; }
    return {std::make_shared<Quant>(quantifiedTerm->getQuant(), std::move(newVars), std::move(newSorts),
                                    quantifiedTerm->getCoreTerm()),
            true};
}

} // namespace

StepHandler::TermPtr StepHandler::instantiationSteps(std::size_t i, TermPtr quantifiedTerm) {

    auto const & step = derivation[i];

    std::shared_ptr<Term> namedAssumption = makeName("@a" + std::to_string(step.clauseId.id));
    std::shared_ptr<Term> instantiationReNamedTerm = makeName("@i" + std::to_string(i - 1));

    auto [clearedTerm, hasChanged] = removeUnusedQuantifiers(quantifiedTerm);
    std::size_t quantStep = step.clauseId.id;

    if (hasChanged) {
        recordStep(literals(std::make_shared<Op>("=", std::vector{namedAssumption, clearedTerm})), "qnt_rm_unused", {});
        recordStep(literals(negate(namedAssumption), clearedTerm), "equiv1", Step::Premises{currentStep - 1});
        recordStep(literals(clearedTerm), "resolution", Step::Premises{quantStep, currentStep - 1});

        namedAssumption = clearedTerm;
        quantStep = currentStep - 1;
    }

    // Getting the instantiated variable-value pairs
    auto instPairs = getInstPairs(i, normalizingEqualities[step.clauseId.id]);

    if (instPairs.empty()) { return clearedTerm; }

    InstantiateVisitor instantiateVisitor(instPairs);
    auto instantiatedTerm = clearedTerm->accept(&instantiateVisitor);
    recordForallInstStep(
        literals(std::make_shared<Op>(
            "or", literals(negate(namedAssumption),
                           std::make_shared<Op>(
                               "!", literals(instantiatedTerm,
                                             makeName(":named " + instantiationReNamedTerm->printTerm())))))),
        std::move(instPairs));

    recordStep(literals(negate(namedAssumption), instantiationReNamedTerm), "or", Step::Premises{currentStep - 1});
    recordStep(literals(instantiationReNamedTerm), "resolution", Step::Premises{currentStep - 1, quantStep});
    return instantiatedTerm;
}

void StepHandler::buildAssumptionSteps() {
    for (auto & assertion : originalAssertions) {
        // We eliminate all let terms (and rely on Carcara's option --expand-let-bindings for proof checking)
        // TODO: simplify!
        LetLocatorVisitor letLocatorVisitor;
        Term * potentialLet = assertion->accept(&letLocatorVisitor);
        while (potentialLet != nullptr) {
            OperateLetTermVisitor operateLetTermVisitor;
            auto simplifiedLet = potentialLet->accept(&operateLetTermVisitor);
            SimplifyVisitor simplifyLetTermVisitor(simplifiedLet, potentialLet);
            assertion = assertion->accept(&simplifyLetTermVisitor);
            potentialLet = assertion->accept(&letLocatorVisitor);
        }
        recordAssumption(
            literals(std::make_shared<Op>("!", args(assertion, makeName(":named @a" + std::to_string(currentStep))))));
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
        recordStep(std::move(andNegArgs), "and_neg", Step::Premises{});

        predicatePremises.push_back(currentStep - 1);
        recordStep(literals(simplifiedLHS), "resolution", Step::Premises{std::move(predicatePremises)});
        return currentStep - 1;
    } else if (simplifiedLHS->getTermType() == Term::APP or
               (simplifiedLHS->getTermType() == Term::TERMINAL and simplifiedLHS->getTerminalType() == Term::VAR)) {
        // single predicate, including 0-ary predicate as a special case
        assert(predicatePremises.size() == 1);
        return predicatePremises[0];
    } else if (simplifiedLHS->getTermType() == Term::TERMINAL and simplifiedLHS->getTerminalType() == Term::BOOL) {
        // no predicate => constant true
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
        solver.assertProp(instantiatedConstraint);
        auto res = solver.check();
        if (res != SMTSolver::Answer::SAT) {
            assert(false);
            throw std::logic_error("Formula should have been satisfiable");
        }
        auto model = solver.getModel();
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
        trueRuleStep = currentStep;
        recordStep(literals(std::make_shared<Terminal>("true", Terminal::terminalType::BOOL)), "true", {});
    }
    return trueRuleStep;
}
