/*
 * Copyright (c) 2023, Matias Barandiaran <matias.barandiaran03@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef GOLEM_TERM_H
#define GOLEM_TERM_H
#include "utils/SmtSolver.h"
#include <memory>
#include <utility>

class Term {
public:
    enum termType { APP, OP, TERMINAL, QUANT, LET };
    enum terminalType { VAR, REAL, INT, SORT, BOOL, UNDECLARED };
    virtual termType getTermType() = 0;
    virtual terminalType getTerminalType() = 0;
    virtual void accept(class PrintVisitor *) = 0;
    virtual std::shared_ptr<Term> accept(class LogicVisitor *) = 0;
    virtual std::string accept(class StringVisitor *) = 0;
    virtual bool accept(class BooleanVisitor *) = 0;
    virtual Term * accept(class PointerVisitor *) = 0;
    virtual std::string printTerm();
    virtual ~Term() = default;
};

class Terminal : public Term {
    std::string val;
    terminalType type;

public:
    Terminal(std::string val, terminalType t) : val(std::move(val)), type(t) {}
    std::string const & getVal() { return val; }
    terminalType const & getType() { return type; }
    termType getTermType() override { return TERMINAL; }
    terminalType getTerminalType() override { return type; }

    std::shared_ptr<Term> accept(LogicVisitor *) override;
    std::string accept(StringVisitor *) override;
    bool accept(BooleanVisitor *) override;
    Term * accept(PointerVisitor *) override;
    void accept(PrintVisitor *) override;
};

class Op : public Term {
    std::string operation;
    std::vector<std::shared_ptr<Term>> args;

public:
    Op(std::string opcode, std::vector<std::shared_ptr<Term>> args)
        : operation(std::move(opcode)), args(std::move(args)) {}
    std::string const & getOp() { return operation; }
    std::vector<std::shared_ptr<Term>> const & getArgs() { return args; }
    termType getTermType() override { return OP; }
    terminalType getTerminalType() override { return UNDECLARED; }
    std::string simplifyRule();
    bool nonLinearity();
    std::string nonLinearSimplification();

    std::shared_ptr<Term> accept(LogicVisitor *) override;
    std::string accept(StringVisitor *) override;
    bool accept(BooleanVisitor *) override;
    Term * accept(PointerVisitor *) override;
    void accept(PrintVisitor *) override;
};

class App : public Term {
    std::string fun;
    std::vector<std::shared_ptr<Term>> args;

public:
    App(std::string fun, std::vector<std::shared_ptr<Term>> args) : fun(std::move(fun)), args(std::move(args)) {}
    std::string const & getFun() { return fun; }
    std::vector<std::shared_ptr<Term>> const & getArgs() { return args; }
    termType getTermType() override { return APP; }
    terminalType getTerminalType() override { return UNDECLARED; }

    std::shared_ptr<Term> accept(LogicVisitor *) override;
    std::string accept(StringVisitor *) override;
    bool accept(BooleanVisitor *) override;
    Term * accept(PointerVisitor *) override;
    void accept(PrintVisitor *) override;
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
    termType getTermType() override { return QUANT; }
    terminalType getTerminalType() override { return UNDECLARED; }

    std::shared_ptr<Term> accept(LogicVisitor *) override;
    std::string accept(StringVisitor *) override;
    bool accept(BooleanVisitor *) override;
    Term * accept(PointerVisitor *) override;
    void accept(PrintVisitor *) override;
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
    termType getTermType() override { return LET; }
    terminalType getTerminalType() override { return UNDECLARED; }

    std::shared_ptr<Term> accept(LogicVisitor *) override;
    std::string accept(StringVisitor *) override;
    bool accept(BooleanVisitor *) override;
    Term * accept(PointerVisitor *) override;
    void accept(PrintVisitor *) override;
};

// Visitors

class LogicVisitor {
public:
    virtual std::shared_ptr<Term> visit(Terminal *) = 0;
    virtual std::shared_ptr<Term> visit(Quant *) = 0;
    virtual std::shared_ptr<Term> visit(Op *) = 0;
    virtual std::shared_ptr<Term> visit(App *) = 0;
    virtual std::shared_ptr<Term> visit(Let *) = 0;
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

class SimplifyLocatorVisitor : public LogicVisitor {
public:
    std::shared_ptr<Term> visit(Terminal *) override;
    std::shared_ptr<Term> visit(Quant *) override;
    std::shared_ptr<Term> visit(Op *) override;
    std::shared_ptr<Term> visit(App *) override;
    std::shared_ptr<Term> visit(Let *) override;
};

class RemoveUnusedVisitor : public LogicVisitor {
    std::vector<std::string> varsInUse;

public:
    std::shared_ptr<Term> visit(Terminal *) override;
    std::shared_ptr<Term> visit(Quant *) override;
    std::shared_ptr<Term> visit(Op *) override;
    std::shared_ptr<Term> visit(App *) override;
    std::shared_ptr<Term> visit(Let *) override { return nullptr; }; // because we have already got rid of the let terms
};

class OperateVisitor : public LogicVisitor {
public:
    std::shared_ptr<Term> visit(Terminal *) override { return std::make_shared<Terminal>("Error", Term::UNDECLARED); };
    std::shared_ptr<Term> visit(Quant *) override { return std::make_shared<Terminal>("Error", Term::UNDECLARED); };
    std::shared_ptr<Term> visit(Op *) override;
    std::shared_ptr<Term> visit(App *) override { return std::make_shared<Terminal>("Error", Term::UNDECLARED); };
    std::shared_ptr<Term> visit(Let *) override { return std::make_shared<Terminal>("Error", Term::UNDECLARED); };
};

class OperateLetTermVisitor : public LogicVisitor {
    std::vector<std::string> terms;
    std::vector<std::shared_ptr<Term>> substitutions;

public:
    std::shared_ptr<Term> visit(Terminal *) override;
    std::shared_ptr<Term> visit(Quant *) override { return std::make_shared<Terminal>("Error", Term::UNDECLARED); };
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

class StringVisitor {
public:
    virtual std::string visit(Terminal *) = 0;
    virtual std::string visit(Quant *) = 0;
    virtual std::string visit(Op *) = 0;
    virtual std::string visit(App *) = 0;
    virtual std::string visit(Let *) = 0;
};

class PrintVisitor {
    std::stringstream ss;

public:
    void visit(Terminal *);
    void visit(Quant *);
    void visit(Op *);
    void visit(App *);
    void visit(Let *);
    std::string getString() { return ss.str(); }
};

class BooleanVisitor {
public:
    virtual bool visit(Terminal *) = 0;
    virtual bool visit(Quant *) = 0;
    virtual bool visit(Op *) = 0;
    virtual bool visit(App *) = 0;
    virtual bool visit(Let *) = 0;
};

class IsPrimaryBranchVisitor : public BooleanVisitor {
    Term * branch;

public:
    explicit IsPrimaryBranchVisitor(Term * b) : branch(b) {}
    bool visit(Terminal *) override { return false; };
    bool visit(Quant *) override { return false; };
    bool visit(Op *) override;
    bool visit(App *) override { return false; };
    bool visit(Let *) override { return false; };
};

class PointerVisitor {
public:
    virtual Term * visit(Terminal *) = 0;
    virtual Term * visit(Quant *) = 0;
    virtual Term * visit(Op *) = 0;
    virtual Term * visit(App *) = 0;
    virtual Term * visit(Let *) = 0;
};

class SimplifyHelperVisitor : public PointerVisitor {
public:
    Term * visit(Terminal *) override;
    Term * visit(Quant *) override;
    Term * visit(Op *) override;
    Term * visit(App *) override;
    Term * visit(Let *) override;
};

class LetLocatorVisitor : public PointerVisitor {
public:
    Term * visit(Terminal *) override { return nullptr; };
    Term * visit(Quant *) override;
    Term * visit(Op *) override;
    Term * visit(App *) override { return nullptr; };
    Term * visit(Let *) override;
};

class GetLocalParentBranchVisitor : public PointerVisitor {
    Term * operation;

public:
    explicit GetLocalParentBranchVisitor(Term * o) : operation(o) {}
    void setOperation(Term * o) { operation = o; }
    Term * visit(Terminal *) override { return nullptr; };
    Term * visit(Quant *) override { return nullptr; };
    Term * visit(Op *) override;
    Term * visit(App *) override { return nullptr; };
    Term * visit(Let *) override { return nullptr; };
};

#endif // GOLEM_TERM_H
