/*
 * Copyright (c) 2023, Matias Barandiaran <matias.barandiaran03@gmail.com>
 * Copyright (c) 2024, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "Term.h"

#include "osmt_terms.h"

#include <cassert>
#include <memory>
#include <string>

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

std::shared_ptr<Term> OperateLetTermVisitor::visit(Terminal * term) {
    for (std::size_t i = 0; i < terms.size(); i++) {
        if (term->getVal() == terms[i]) { return substitutions[i]; }
    }
    return term->asSharedPtr();
}

std::shared_ptr<Term> OperateLetTermVisitor::visit(Op * term) {
    std::vector<std::shared_ptr<Term>> args;
    for (std::shared_ptr<Term> const & arg : term->getArgs()) {
        args.push_back(arg->accept(this));
    }
    return std::make_shared<Op>(term->getOp(), std::move(args));
}

std::shared_ptr<Term> OperateLetTermVisitor::visit(App * term) {
    std::vector<std::shared_ptr<Term>> args;
    for (std::shared_ptr<Term> const & arg : term->getArgs()) {
        args.push_back(arg->accept(this));
    }
    return std::make_shared<App>(term->getFun(), std::move(args));
}

std::shared_ptr<Term> OperateLetTermVisitor::visit(Let * term) {
    terms = term->getTermNames();
    substitutions = term->getDeclarations();
    return term->getApplication()->accept(this);
}

std::shared_ptr<Term> OperateLetTermVisitor::visit(Quant *) {
    throw std::logic_error("Let term transform should never visit quantified term");
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
