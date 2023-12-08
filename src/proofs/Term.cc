/*
 * Copyright (c) 2023, Matias Barandiaran <matias.barandiaran03@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "Term.h"
#include "FastRational.h"
#include <cassert>
#include <memory>
#include <string>

bool Op::nonLinearity() const {
    if (operation == "and") {
        auto predicates = std::count_if(args.begin(), args.end(), [](auto const & arg) {
            return arg->getTermType() == Term::APP or arg->getTerminalType() == Terminal::VAR;
        });
        return predicates >= 2;
    }
    return false;
}

std::string Op::nonLinearSimplification() const {
    std::stringstream ss;
    if (operation == "and") {
        for (std::size_t i = 0; i < args.size(); i++) {
            ss << "(not " << args[i]->printTerm() << ")";
            if (i != args.size() - 1) { ss << " "; }
        }
        return ss.str();
    } else {
        throw std::logic_error("This is not a non-linear case!");
    }
}

std::string Term::printTerm() {
    PrintVisitor printVisitor;
    this->accept(&printVisitor);
    return printVisitor.getString();
}

void PrintVisitor::visit(Terminal * term) {
    ss << term->getVal();
}

void PrintVisitor::visit(Op * term) {
    ss << "(" << term->getOp();
    for (auto const & arg : term->getArgs()) {
        ss << " ";
        arg->accept(this);
    }
    ss << ")";
}

void PrintVisitor::visit(App * term) {
    ss << "(" << term->getFun();
    for (std::shared_ptr<Term> const & arg : term->getArgs()) {
        ss << " ";
        arg->accept(this);
    }
    ss << ")";
}

void PrintVisitor::visit(Quant * term) {
    ss << "(" << term->getQuant() << " (";
    for (std::size_t i = 0; i < term->getVars().size(); i++) {
        ss << "(";
        term->getVars()[i]->accept(this);
        ss << " ";
        term->getSorts()[i]->accept(this);
        ss << ")";
        if (i + 1 != term->getVars().size()) { ss << " "; }
    }
    ss << ") ";
    term->getCoreTerm()->accept(this);
    ss << ")";
}

void PrintVisitor::visit(Let * term) {
    auto names = term->getTermNames();
    ss << "(let (";
    for (std::size_t i = 0; i < names.size(); i++) {
        ss << "(" << names[i] << " ";
        term->getDeclarations()[i]->accept(this);
        ss << ")";
        if (i + 1 != names.size()) { ss << " "; }
    }
    ss << ") ";
    term->getApplication()->accept(this);
    ss << ")";
}

std::shared_ptr<Term> CongChainVisitor::visit(Terminal * term) {
    return std::make_shared<Terminal>(term->getVal(), term->getType());
}

std::shared_ptr<Term> CongChainVisitor::visit(Op * term) {

    transCase = 0;
    bool canSimplify = true;

    for (auto const & arg : term->getArgs()) {
        if (not(arg->getTermType() == Term::TERMINAL or arg->getTermType() == Term::APP)) {
            canSimplify = false;
            break;
        }
    }

    if (canSimplify) {
        std::vector<std::size_t> premises;
        auto simplification = term->operate();
        steps.emplace_back(
            currentStep,
            std::make_shared<Op>("=", std::vector<std::shared_ptr<Term>>{term->asSharedPtr(), term->operate()}),
            premises, term->simplifyRule());
        currentStep++;
        if (term->getOp() == ">") {
            assert(simplification->getTermType() == Term::OP);
            auto simplificationOp = std::dynamic_pointer_cast<Op>(simplification);
            assert(simplificationOp->getOp() == "not");
            auto lessOrEq = simplificationOp->getArgs()[0];
            assert(lessOrEq->getTermType() == Term::OP and std::dynamic_pointer_cast<Op>(lessOrEq)->getOp() == "<=");
            auto innerWorking = std::dynamic_pointer_cast<Op>(lessOrEq)->operate();
            steps.emplace_back(currentStep,
                               std::make_shared<Op>("=", std::vector<std::shared_ptr<Term>>{lessOrEq, innerWorking}),
                               premises, std::dynamic_pointer_cast<Op>(lessOrEq)->simplifyRule());
            currentStep++;
            auto innerSimplified =
                std::make_shared<Op>(simplificationOp->getOp(), std::vector<std::shared_ptr<Term>>{innerWorking});
            auto cong = std::make_shared<Op>("=", std::vector<std::shared_ptr<Term>>{simplification, innerSimplified});

            steps.emplace_back(currentStep, cong, std::vector<std::size_t>{currentStep - 1}, "cong");
            currentStep++;
            auto outerWorking = innerSimplified->operate();
            steps.emplace_back(
                currentStep,
                std::make_shared<Op>("=", std::vector<std::shared_ptr<Term>>{innerSimplified, outerWorking}), premises,
                innerSimplified->simplifyRule());

            currentStep++;
            auto trans = std::make_shared<Op>("=", std::vector<std::shared_ptr<Term>>{simplification, outerWorking});
            steps.emplace_back(currentStep, trans, std::vector<std::size_t>{currentStep - 2, currentStep - 1}, "trans");
            currentStep++;
            trans = std::make_shared<Op>("=", std::vector<std::shared_ptr<Term>>{term->asSharedPtr(), outerWorking});
            steps.emplace_back(currentStep, trans, std::vector<std::size_t>{currentStep - 5, currentStep - 1}, "trans");
            currentStep++;
            return outerWorking;
        } else if (term->getOp() == ">=") {
            transCase = 1;
            auto simplified = std::dynamic_pointer_cast<Op>(simplification)->operate();
            steps.emplace_back(
                currentStep, std::make_shared<Op>("=", std::vector<std::shared_ptr<Term>>{simplification, simplified}),
                premises, std::dynamic_pointer_cast<Op>(simplification)->simplifyRule());
            currentStep++;
            auto trans = std::make_shared<Op>("=", std::vector<std::shared_ptr<Term>>{term->asSharedPtr(), simplified});
            steps.emplace_back(currentStep, trans, std::vector<std::size_t>{currentStep - 2, currentStep - 1}, "trans");
            currentStep++;
            return simplified;
        }
        return simplification;
    } else {
        std::vector<std::size_t> premises;
        std::vector<std::shared_ptr<Term>> newArgs;
        for (auto const & arg : term->getArgs()) {
            newArgs.push_back(arg->accept(this));
            if (arg->getTermType() == Term::OP) { premises.push_back(currentStep - 1); }
        }
        auto modifiedTerm = std::make_shared<Op>(term->getOp(), std::move(newArgs));
        auto cong = std::make_shared<Op>("=", std::vector<std::shared_ptr<Term>>{term->asSharedPtr(), modifiedTerm});
        steps.emplace_back(currentStep, cong, premises, "cong");
        currentStep++;
        auto furtherSimplification = modifiedTerm->accept(this);
        auto trans =
            std::make_shared<Op>("=", std::vector<std::shared_ptr<Term>>{term->asSharedPtr(), furtherSimplification});
        std::size_t predecessor;
        if (transCase == 1) {
            predecessor = currentStep - 4;
            transCase = 0;
        } else {
            predecessor = currentStep - 2;
        }
        steps.emplace_back(currentStep, trans, std::vector<std::size_t>{predecessor, currentStep - 1}, "trans");
        currentStep++;
        return furtherSimplification;
    }
}

std::shared_ptr<Term> CongChainVisitor::visit(App * term) {
    return std::make_shared<App>(term->getFun(), term->getArgs());
}

std::string Op::simplifyRule() const {
    std::string op = operation;
    if (op == "=") {
        if ((args[0]->printTerm().find_first_not_of("( )-0123456789") == std::string::npos) and
            (args[1]->printTerm().find_first_not_of("( )-0123456789") == std::string::npos)) {
            return "eq_simplify";
        } else {
            return "equiv_simplify";
        }
    } else if ((op == ">") or (op == "<") or (op == "<=") or (op == ">=")) {
        return "comp_simplify";
    } else if (op == "and") {
        return "and_simplify";
    } else if (op == "or") {
        return "or_simplify";
    } else if (op == "+") {
        return "sum_simplify";
    } else if (op == "-") {
        return "minus_simplify";
    } else if (op == "/" or op == "div") {
        return "div_simplify";
    } else if (op == "*") {
        return "prod_simplify";
    } else if (op == "not") {
        return "not_simplify";
    } else if (op == "ite") {
        return "ite_simplify";
    } else if (op == "mod") {
        return "mod_simplify";
    }
    throw std::logic_error("Unhandled case in Op::simplifyRule");
}

std::shared_ptr<Term> InstantiateVisitor::visit(Terminal * term) {
    auto val = term->getVal();
    auto type = term->getType();
    if (type != Term::VAR) { return std::make_shared<Terminal>(val, type); }
    for (std::pair<std::string, std::string> const & pair : instPairs) {
        if (val == pair.first) {
            if (pair.second == "true" or pair.second == "false") {
                return std::make_shared<Terminal>(pair.second, Term::BOOL);
            } else if (pair.second.find('.') != std::string::npos) {
                return std::make_shared<Terminal>(pair.second, Term::REAL);
            } else {
                return std::make_shared<Terminal>(pair.second, Term::INT);
            }
        }
    }
    return std::make_shared<Terminal>(val, type);
}

std::shared_ptr<Term> InstantiateVisitor::visit(Op * term) {
    std::vector<std::shared_ptr<Term>> args;
    std::string opcode = term->getOp();
    for (std::shared_ptr<Term> const & arg : term->getArgs()) {
        args.push_back(arg->accept(this));
    }
    return std::make_shared<Op>(opcode, args);
}

std::shared_ptr<Term> InstantiateVisitor::visit(App * term) {
    std::vector<std::shared_ptr<Term>> args;
    std::string fun = term->getFun();
    for (std::shared_ptr<Term> const & arg : term->getArgs()) {
        args.push_back(arg->accept(this));
    }
    return std::make_shared<App>(fun, args);
}

std::shared_ptr<Term> InstantiateVisitor::visit(Quant * term) {
    std::shared_ptr<Term> coreTerm = term->getCoreTerm()->accept(this);
    return coreTerm;
}

std::shared_ptr<Term> InstantiateVisitor::visit(Let * term) {
    std::vector<std::shared_ptr<Term>> declarations;
    auto application = term->getApplication();
    for (std::shared_ptr<Term> const & dec : term->getDeclarations()) {
        declarations.push_back(dec->accept(this));
    }
    application->accept(this);
    return std::make_shared<Let>(term->getTermNames(), declarations, application);
}

std::shared_ptr<Term> RemoveUnusedVisitor::visit(Quant * term) {
    auto coreTerm = term->getCoreTerm();
    coreTerm->accept(this);

    std::vector<std::shared_ptr<Term>> newVars;
    std::vector<std::shared_ptr<Term>> newSorts;
    auto const & vars = term->getVars();
    auto const & sorts = term->getSorts();
    for (std::size_t i = 0; i < vars.size(); ++i) {
        auto varStr = vars[i]->printTerm();
        auto it = varsInUse.find(varStr);
        if (it != varsInUse.end()) {
            newVars.push_back(vars[i]);
            newSorts.push_back(sorts[i]);
        }
    }
    if (newVars.empty()) { return term->getCoreTerm(); }
    return std::make_shared<Quant>(term->getQuant(), std::move(newVars), std::move(newSorts), term->getCoreTerm());
}

std::shared_ptr<Term> RemoveUnusedVisitor::visit(Terminal * term) {
    if (term->getTerminalType() == Term::VAR) {
        auto termStr = term->printTerm();
        varsInUse.insert(termStr);
    }
    return nullptr;
}

std::shared_ptr<Term> RemoveUnusedVisitor::visit(Op * term) {
    for (auto const & arg : term->getArgs()) {
        arg->accept(this);
    }
    return nullptr;
}

std::shared_ptr<Term> RemoveUnusedVisitor::visit(App * term) {
    for (auto const & arg : term->getArgs()) {
        arg->accept(this);
    }
    return nullptr;
}

std::shared_ptr<Term> SimplifyVisitor::visit(Terminal * term) {
    return std::make_shared<Terminal>(term->getVal(), term->getType());
}

std::shared_ptr<Term> SimplifyVisitor::visit(Op * term) {

    if (operation == term) {
        return simplification;
    } else {
        std::vector<std::shared_ptr<Term>> newArgs;
        for (auto const & arg : term->getArgs()) {
            newArgs.push_back(arg->accept(this));
        }
        return std::make_shared<Op>(term->getOp(), newArgs);
    }
}

std::shared_ptr<Term> SimplifyVisitor::visit(App * term) {
    return std::make_shared<App>(term->getFun(), term->getArgs());
}

std::shared_ptr<Term> SimplifyVisitor::visit(Quant * term) {

    return std::make_shared<Quant>(term->getQuant(), term->getVars(), term->getSorts(),
                                   term->getCoreTerm()->accept(this));
}

std::shared_ptr<Term> SimplifyVisitor::visit(Let * term) {

    if (operation == term) {
        return simplification;
    } else {
        return std::make_shared<Let>(term->getTermNames(), term->getDeclarations(),
                                     term->getApplication()->accept(this));
    }
}

std::shared_ptr<Term> Op::operate() const {
    std::vector<std::shared_ptr<Term>> newArgs;
    std::string firstStr;
    std::string secondStr;
    FastRational firstTerm;
    FastRational secondTerm;

    if (operation == "<" or operation == "<=" or operation == "-" or operation == "*" or operation == "/" or
        operation == "mod" or operation == "div") {
        assert(args[0]->getTerminalType() != Term::VAR);
        assert(args[1]->getTerminalType() != Term::VAR);
        firstStr = args[0]->printTerm();
        secondStr = args[1]->printTerm();
        firstStr.erase(remove(firstStr.begin(), firstStr.end(), '('), firstStr.end());
        firstStr.erase(remove(firstStr.begin(), firstStr.end(), ')'), firstStr.end());
        firstStr.erase(remove(firstStr.begin(), firstStr.end(), ' '), firstStr.end());
        secondStr.erase(remove(secondStr.begin(), secondStr.end(), '('), secondStr.end());
        secondStr.erase(remove(secondStr.begin(), secondStr.end(), ')'), secondStr.end());
        secondStr.erase(remove(secondStr.begin(), secondStr.end(), ' '), secondStr.end());
        firstTerm = FastRational(&firstStr[0], 10);
        secondTerm = FastRational(&secondStr[0], 10);
    }

    if (operation == "=") {
        assert(args[0]->getTerminalType() != Term::VAR);
        assert(args[1]->getTerminalType() != Term::VAR);
        if (args[0]->printTerm() == args[1]->printTerm()) {
            return std::make_shared<Terminal>("true", Term::BOOL);
        } else {
            return std::make_shared<Terminal>("false", Term::BOOL);
        }
    } else if (operation == ">") {
        return std::make_shared<Op>("not", std::vector<std::shared_ptr<Term>>{std::make_shared<Op>("<=", args)});
    } else if (operation == "<") {
        if (firstTerm < secondTerm) {
            return std::make_shared<Terminal>("true", Term::BOOL);
        } else {
            return std::make_shared<Terminal>("false", Term::BOOL);
        }
    } else if (operation == "<=") {
        if (firstTerm <= secondTerm) {
            return std::make_shared<Terminal>("true", Term::BOOL);
        } else {
            return std::make_shared<Terminal>("false", Term::BOOL);
        }
    } else if (operation == ">=") {
        newArgs.push_back(args[1]);
        newArgs.push_back(args[0]);
        return std::make_shared<Op>("<=", newArgs);
    } else if (operation == "and") {
        int trues = 0;
        std::vector<std::shared_ptr<Term>> predicates;

        for (auto const & arg : args) {
            //           assert(arg->getTerminalType() != Term::VAR);
            if (arg->printTerm() == "false") { return std::make_shared<Terminal>("false", Term::BOOL); }
            if (arg->printTerm() == "true") { trues++; }
            if (arg->printTerm() != "true") { predicates.push_back(arg); }
        }
        if (trues == int(args.size())) { return std::make_shared<Terminal>("true", Term::BOOL); }
        if (predicates.size() == 1) {
            return predicates[0];
        } else {
            for (auto const & predicate : predicates) {
                newArgs.push_back(predicate);
            }
            return std::make_shared<Op>("and", newArgs);
        }
    } else if (operation == "or") {
        for (auto const & arg : args) {
            assert(arg->getTerminalType() != Term::VAR);
            if (arg->printTerm() == "true") { return std::make_shared<Terminal>("true", Term::BOOL); }
        }
        return std::make_shared<Terminal>("false", Term::BOOL);
    } else if (operation == "+") {
        FastRational result = 0;
        for (auto const & arg : args) {
            assert(arg->getTerminalType() != Term::VAR);
            std::string str = arg->printTerm();
            str.erase(remove(str.begin(), str.end(), '('), str.end());
            str.erase(remove(str.begin(), str.end(), ')'), str.end());
            str.erase(remove(str.begin(), str.end(), ' '), str.end());
            FastRational temp(str.c_str(), 10);
            result += temp;
        }
        if (result < 0) {
            result *= -1;
            return std::make_shared<Terminal>("(- " + result.get_str() + ")", Term::INT);
        } else {
            return std::make_shared<Terminal>(result.get_str(), Term::INT);
        }
    } else if (operation == "-") {
        FastRational result = firstTerm - secondTerm;
        if (result < 0) {
            result *= -1;
            return std::make_shared<Terminal>("(- " + result.get_str() + ")", Term::INT);
        } else {
            return std::make_shared<Terminal>(result.get_str(), Term::INT);
        }
    } else if (operation == "/") {
        FastRational result = firstTerm / secondTerm;
        if (result < 0) {
            result *= -1;
            return std::make_shared<Terminal>("(- " + result.get_str() + ")", Term::INT);
        } else {
            return std::make_shared<Terminal>(result.get_str(), Term::INT);
        }
    } else if (operation == "*") {
        FastRational result = firstTerm * secondTerm;
        if (result < 0) {
            result *= -1;
            return std::make_shared<Terminal>("(- " + result.get_str() + ")", Term::INT);
        } else {
            return std::make_shared<Terminal>(result.get_str(), Term::INT);
        }
    } else if (operation == "not") {
        assert(args[0]->getTerminalType() != Term::VAR);
        if (args[0]->printTerm() == "false") {
            return std::make_shared<Terminal>("true", Term::BOOL);
        } else {
            return std::make_shared<Terminal>("false", Term::BOOL);
        }
    } else if (operation == "ite") {
        assert(args[0]->getTerminalType() != Term::VAR);
        assert(args[1]->getTerminalType() != Term::VAR);
        assert(args[2]->getTerminalType() != Term::VAR);
        if (args[0]->printTerm() == "true") {
            return args[1];
        } else {
            return args[2];
        }
    } else if (operation == "mod") {
        // NOTE: The semantics of modulo operation in OpenSMT's FastRationals is different from the semantics defined by
        // SMT-LIB. We must use the computation of the remainder according to SMT-LIB.
        // See notes in // https://smtlib.cs.uiowa.edu/theories-Ints.shtml

        // "Regardless of sign of m,
        //  when n is positive, (div m n) is the floor of the rational number m/n;
        //  when n is negative, (div m n) is the ceiling of m/n."

        // Remainder is then always a positive number r such that m = n * q + r, r < abs(n)
        auto smtlib_modulo = [](auto const & m, auto const & n) -> FastRational {
            auto ratio = m / n;
            auto q = n > 0 ? ratio.floor() : ratio.ceil();
            auto r = m - n * q;
            assert(r.isInteger() and r.sign() >= 0 and r < abs(n));
            return r;
        };
        FastRational result = smtlib_modulo(firstTerm, secondTerm);
        return std::make_shared<Terminal>(result.get_str(), Term::INT);
    } else if (operation == "div") {
        FastRational result = firstTerm / secondTerm;
        if (result < 0) {
            result *= -1;
            return std::make_shared<Terminal>("(- " + result.ceil().get_str() + ")", Term::INT);
        } else {
            return std::make_shared<Terminal>(result.floor().get_str(), Term::INT);
        }
    }
    throw std::logic_error("Unhandled case in Op::operate()");
}

std::shared_ptr<Term> OperateLetTermVisitor::visit(Terminal * term) {

    for (std::size_t i = 0; i < terms.size(); i++) {
        if (term->getVal() == terms[i]) { return substitutions[i]; }
    }
    return std::make_shared<Terminal>(term->getVal(), term->getType());
}

std::shared_ptr<Term> OperateLetTermVisitor::visit(Op * term) {
    std::vector<std::shared_ptr<Term>> args;
    std::string opcode = term->getOp();
    for (std::shared_ptr<Term> const & arg : term->getArgs()) {
        args.push_back(arg->accept(this));
    }
    return std::make_shared<Op>(opcode, args);
}

std::shared_ptr<Term> OperateLetTermVisitor::visit(App * term) {
    std::vector<std::shared_ptr<Term>> args;
    std::string fun = term->getFun();
    for (std::shared_ptr<Term> const & arg : term->getArgs()) {
        args.push_back(arg->accept(this));
    }
    return std::make_shared<App>(fun, args);
}

std::shared_ptr<Term> OperateLetTermVisitor::visit(Let * term) {
    terms = term->getTermNames();
    substitutions = term->getDeclarations();
    return term->getApplication()->accept(this);
}

Term * LetLocatorVisitor::visit(Quant * term) {
    return term->getCoreTerm()->accept(this);
}

Term * LetLocatorVisitor::visit(Op * term) {
    auto args = term->getArgs();
    for (auto const & arg : args) {
        auto locatedTerm = arg->accept(this);
        if (locatedTerm != nullptr) { return locatedTerm; }
    }
    return nullptr;
}

Term * LetLocatorVisitor::visit(Let * term) {
    auto locatedTerm = term->getApplication()->accept(this);
    if (locatedTerm == nullptr) { return term; }
    return locatedTerm;
}

std::shared_ptr<Term> Terminal::accept(LogicVisitor * visitor) {
    return visitor->visit(this);
}

std::shared_ptr<Term> Op::accept(LogicVisitor * visitor) {
    return visitor->visit(this);
}

std::shared_ptr<Term> App::accept(LogicVisitor * visitor) {
    return visitor->visit(this);
}

std::shared_ptr<Term> Quant::accept(LogicVisitor * visitor) {
    return visitor->visit(this);
}

std::shared_ptr<Term> Let::accept(LogicVisitor * visitor) {
    return visitor->visit(this);
}

void Terminal::accept(VoidVisitor * visitor) {
    visitor->visit(this);
}

void Op::accept(VoidVisitor * visitor) {
    visitor->visit(this);
}

void App::accept(VoidVisitor * visitor) {
    visitor->visit(this);
}

void Quant::accept(VoidVisitor * visitor) {
    visitor->visit(this);
}

void Let::accept(VoidVisitor * visitor) {
    visitor->visit(this);
}

Term * Terminal::accept(PointerVisitor * visitor) {
    return visitor->visit(this);
}

Term * Op::accept(PointerVisitor * visitor) {
    return visitor->visit(this);
}

Term * App::accept(PointerVisitor * visitor) {
    return visitor->visit(this);
}

Term * Quant::accept(PointerVisitor * visitor) {
    return visitor->visit(this);
}

Term * Let::accept(PointerVisitor * visitor) {
    return visitor->visit(this);
}
