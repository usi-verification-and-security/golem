/*
 * Copyright (c) 2023, Matias Barandiaran <matias.barandiaran03@gmail.com>
 * Copyright (c) 2024-2025, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef GOLEM_TERM_H
#define GOLEM_TERM_H

#include <memory>
#include <sstream>
#include <string>
#include <unordered_set>
#include <utility>
#include <vector>

namespace golem {
class Term : public std::enable_shared_from_this<Term> {
public:
    enum termType { APP, OP, TERMINAL, QUANT, LET };
    enum terminalType { VAR, REAL, INT, SORT, BOOL, UNDECLARED };
    virtual termType getTermType() const = 0;
    virtual terminalType getTerminalType() const = 0;
    virtual void accept(class VoidVisitor *) = 0;
    virtual std::shared_ptr<Term> accept(class LogicVisitor *) = 0;
    virtual Term * accept(class PointerVisitor *) = 0;
    virtual std::string printTerm();
    std::shared_ptr<Term> asSharedPtr() { return shared_from_this(); }
    virtual ~Term() = default;
};

class Terminal : public Term {
    std::string val;
    terminalType type;

public:
    Terminal(std::string val, terminalType t) : val(std::move(val)), type(t) {}
    std::string const & getVal() { return val; }
    terminalType const & getType() { return type; }
    termType getTermType() const override { return TERMINAL; }
    terminalType getTerminalType() const override { return type; }

    std::shared_ptr<Term> accept(LogicVisitor *) override;
    Term * accept(PointerVisitor *) override;
    void accept(VoidVisitor *) override;
};

class Op : public Term {
    std::string operation;
    std::vector<std::shared_ptr<Term>> args;

public:
    Op(std::string opcode, std::vector<std::shared_ptr<Term>> args)
        : operation(std::move(opcode)), args(std::move(args)) {}
    std::string const & getOp() const { return operation; }
    std::vector<std::shared_ptr<Term>> const & getArgs() const { return args; }
    termType getTermType() const override { return OP; }
    terminalType getTerminalType() const override { return UNDECLARED; }

    std::shared_ptr<Term> accept(LogicVisitor *) override;
    Term * accept(PointerVisitor *) override;
    void accept(VoidVisitor *) override;
};

class App : public Term {
    std::string fun;
    std::vector<std::shared_ptr<Term>> args;

public:
    App(std::string fun, std::vector<std::shared_ptr<Term>> args) : fun(std::move(fun)), args(std::move(args)) {}
    std::string const & getFun() { return fun; }
    std::vector<std::shared_ptr<Term>> const & getArgs() { return args; }
    termType getTermType() const override { return APP; }
    terminalType getTerminalType() const override { return UNDECLARED; }

    std::shared_ptr<Term> accept(LogicVisitor *) override;
    Term * accept(PointerVisitor *) override;
    void accept(VoidVisitor *) override;
};

class Quant : public Term {
    std::string quant;
    std::vector<std::shared_ptr<Term>> vars;
    std::vector<std::shared_ptr<Term>> sorts;
    std::shared_ptr<Term> coreTerm;

public:
    Quant(std::string quant, std::vector<std::shared_ptr<Term>> vars, std::vector<std::shared_ptr<Term>> sorts,
          std::shared_ptr<Term> coreTerm)
        : quant(std::move(quant)), vars(std::move(vars)), sorts(std::move(sorts)), coreTerm(std::move(coreTerm)) {}
    std::string const & getQuant() { return quant; }
    std::vector<std::shared_ptr<Term>> const & getVars() { return vars; }
    std::vector<std::shared_ptr<Term>> const & getSorts() { return sorts; }
    std::shared_ptr<Term> getCoreTerm() { return coreTerm; }
    termType getTermType() const override { return QUANT; }
    terminalType getTerminalType() const override { return UNDECLARED; }

    std::shared_ptr<Term> accept(LogicVisitor *) override;
    Term * accept(PointerVisitor *) override;
    void accept(VoidVisitor *) override;
};

class Let : public Term {
    std::vector<std::string> termNames;
    std::vector<std::shared_ptr<Term>> declarations;
    std::shared_ptr<Term> application;

public:
    Let(std::vector<std::string> termNames, std::vector<std::shared_ptr<Term>> declarations,
        std::shared_ptr<Term> application)
        : termNames(std::move(termNames)), declarations(std::move(declarations)), application(std::move(application)) {}
    std::vector<std::shared_ptr<Term>> const & getDeclarations() { return declarations; }
    std::shared_ptr<Term> const & getApplication() { return application; }
    std::vector<std::string> const & getTermNames() { return termNames; }
    termType getTermType() const override { return LET; }
    terminalType getTerminalType() const override { return UNDECLARED; }

    std::shared_ptr<Term> accept(LogicVisitor *) override;
    Term * accept(PointerVisitor *) override;
    void accept(VoidVisitor *) override;
};

// Visitors

class LogicVisitor {
public:
    virtual std::shared_ptr<Term> visit(Terminal *) = 0;
    virtual std::shared_ptr<Term> visit(Quant *) = 0;
    virtual std::shared_ptr<Term> visit(Op *) = 0;
    virtual std::shared_ptr<Term> visit(App *) = 0;
    virtual std::shared_ptr<Term> visit(Let *) = 0;
    virtual ~LogicVisitor() = default;
};

class InstantiateVisitor : public LogicVisitor {
    std::vector<std::pair<std::string, std::string>> instPairs;

public:
    explicit InstantiateVisitor(std::vector<std::pair<std::string, std::string>> instPairs)
        : instPairs(std::move(instPairs)) {}
    explicit InstantiateVisitor() = default;

    std::shared_ptr<Term> visit(Terminal *) override;
    std::shared_ptr<Term> visit(Quant *) override;
    std::shared_ptr<Term> visit(Op *) override;
    std::shared_ptr<Term> visit(App *) override;
    std::shared_ptr<Term> visit(Let *) override;
};

class OperateLetTermVisitor : public LogicVisitor {
    std::vector<std::string> terms;
    std::vector<std::shared_ptr<Term>> substitutions;

public:
    std::shared_ptr<Term> visit(Terminal *) override;
    std::shared_ptr<Term> visit(Quant *) override;
    std::shared_ptr<Term> visit(Op *) override;
    std::shared_ptr<Term> visit(App *) override;
    std::shared_ptr<Term> visit(Let *) override;
};

class SimplifyVisitor : public LogicVisitor {
    std::shared_ptr<Term> simplification;
    Term * operation;

public:
    SimplifyVisitor(std::shared_ptr<Term> simplification, Term * operation)
        : simplification(std::move(simplification)), operation(operation) {}
    std::shared_ptr<Term> visit(Terminal *) override;
    std::shared_ptr<Term> visit(Quant *) override;
    std::shared_ptr<Term> visit(Op *) override;
    std::shared_ptr<Term> visit(App *) override;
    std::shared_ptr<Term> visit(Let *) override;
};

class VoidVisitor {
public:
    virtual void visit(Terminal *) = 0;
    virtual void visit(Quant *) = 0;
    virtual void visit(Op *) = 0;
    virtual void visit(App *) = 0;
    virtual void visit(Let *) = 0;
    virtual ~VoidVisitor() = default;
};

class PrintVisitor : public VoidVisitor {
    std::stringstream ss;

public:
    void visit(Terminal *) override;
    void visit(Quant *) override;
    void visit(Op *) override;
    void visit(App *) override;
    void visit(Let *) override;
    std::string getString() { return ss.str(); }
};

class PointerVisitor {
public:
    virtual Term * visit(Terminal *) = 0;
    virtual Term * visit(Quant *) = 0;
    virtual Term * visit(Op *) = 0;
    virtual Term * visit(App *) = 0;
    virtual Term * visit(Let *) = 0;
    virtual ~PointerVisitor() = default;
};

class LetLocatorVisitor : public PointerVisitor {
public:
    Term * visit(Terminal *) override { return nullptr; };
    Term * visit(Quant *) override;
    Term * visit(Op *) override;
    Term * visit(App *) override { return nullptr; };
    Term * visit(Let *) override;
};
} // namespace golem

#endif // GOLEM_TERM_H
