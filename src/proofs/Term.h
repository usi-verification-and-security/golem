//
// Created by mambo on 8/14/23.
//
#ifndef TERM_H  // Replace TERM_H with the actual name of your header file
#define TERM_H
#include <utility>
#include "utils/SmtSolver.h"
#include <memory>

class Term {
public:
    enum terminalType{ VAR, REAL, INT, SORT, UNDECLARED};
    virtual std::shared_ptr<Term> accept(class LogicVisitor*) = 0;
    virtual std::string accept(class StringVisitor*) = 0;
    virtual bool accept(class BooleanVisitor*) = 0;
};

class Terminal : public Term {
    std::string val;
    terminalType type;
public:
    Terminal(std::string  val, terminalType t) : val(std::move(val)), type(t) {}
    std::string getVal() { return val;}
    terminalType getType() {return type;}

    std::shared_ptr<Term> accept(LogicVisitor*) override;
    std::string accept(StringVisitor*) override;
    bool accept(BooleanVisitor*) override;
};

class Op : public Term {
    std::string operation;
    std::vector<std::shared_ptr<Term>> args;
public:
    Op(std::string  opcode, std::vector<std::shared_ptr<Term>> args) : operation(std::move(opcode)), args(std::move(args)) {}
    std::string getOp() { return operation;}
    std::vector<std::shared_ptr<Term>> getArgs() {return args;}

    std::shared_ptr<Term> accept(LogicVisitor*) override;
    std::string accept(StringVisitor*) override;
    bool accept(BooleanVisitor*) override;
};

class App : public Term {
    std::string fun;
    std::vector<std::shared_ptr<Term>> args;
public:
    App(std::string  fun, std::vector<std::shared_ptr<Term>> args) : fun(std::move(fun)), args(std::move(args)){}
    std::string getFun() {return fun;}
    std::vector<std::shared_ptr<Term>> getArgs() {return args;}

    std::shared_ptr<Term> accept(LogicVisitor*) override;
    std::string accept(StringVisitor*) override;
    bool accept(BooleanVisitor*) override;
};

class Quant : public Term {
    std::string quant;
    std::vector<std::shared_ptr<Term>> vars;
    std::vector<std::shared_ptr<Term>> sorts;
    std::shared_ptr<Term> coreTerm;
public:
    Quant(std::string quant, std::vector<std::shared_ptr<Term>> vars, std::vector<std::shared_ptr<Term>> sorts, std::shared_ptr<Term> coreTerm) :  quant(std::move(quant)),
          vars(std::move(vars)), sorts(std::move(sorts)), coreTerm(std::move(coreTerm)){}
    std::string getQuant() {return quant;}
    std::vector<std::shared_ptr<Term>> getVars() {return vars;}
    std::vector<std::shared_ptr<Term>> getSorts() {return sorts;}
    std::shared_ptr<Term> getCoreTerm() {return coreTerm;}
    std::shared_ptr<Term> accept(LogicVisitor*) override;
    std::string accept(StringVisitor*) override;
    bool accept(BooleanVisitor*) override;
};

class LogicVisitor {
public:
    virtual std::shared_ptr<Term> visit(Terminal*) = 0;
    virtual std::shared_ptr<Term> visit(Quant*) = 0;
    virtual std::shared_ptr<Term> visit(Op*) = 0;
    virtual std::shared_ptr<Term> visit(App*) = 0;
};

class InstantiateVisitor : public LogicVisitor{
    std::vector<std::pair<std::string, std::string>> instPairs;
public:
    explicit InstantiateVisitor (std::vector<std::pair<std::string, std::string>> instPairs) : instPairs(std::move(instPairs)) {}

    std::shared_ptr<Term> visit(Terminal*) override;
    std::shared_ptr<Term> visit(Quant*) override;
    std::shared_ptr<Term> visit(Op*) override;
    std::shared_ptr<Term> visit(App*) override;
};

class SimplifyLocatorVisitor : public LogicVisitor{
public:
    std::shared_ptr<Term> visit(Terminal*) override;
    std::shared_ptr<Term> visit(Quant*) override;
    std::shared_ptr<Term> visit(Op*) override;
    std::shared_ptr<Term> visit(App*) override;
};

class SimplifyVisitor : public LogicVisitor {
    std::string simplification;
    std::shared_ptr<Term> operation;
public:
    SimplifyVisitor(std::string s, std::shared_ptr<Term> o) : simplification(std::move(s)), operation(std::move(o)) {}
    std::shared_ptr<Term> visit(Terminal*) override;
    std::shared_ptr<Term> visit(Quant*) override;
    std::shared_ptr<Term> visit(Op*) override;
    std::shared_ptr<Term> visit(App*) override;
};

class ImpFirstTermVisitor : public LogicVisitor {
public:
    std::shared_ptr<Term> visit(Terminal*) override;
    std::shared_ptr<Term> visit(Quant*) override;
    std::shared_ptr<Term> visit(Op*) override;
    std::shared_ptr<Term> visit(App*) override;
};

class GetLocalParentBranchVisitor : public LogicVisitor {
    std::shared_ptr<Term> operation;
public:
    GetLocalParentBranchVisitor(std::shared_ptr<Term> o) : operation(std::move(o)) {}
    std::shared_ptr<Term> visit(Terminal*) override;
    std::shared_ptr<Term> visit(Quant*) override;
    std::shared_ptr<Term> visit(Op*) override;
    std::shared_ptr<Term> visit(App*) override;
};

class StringVisitor {
public:
    virtual std::string visit(Terminal*) = 0;
    virtual std::string visit(Quant*) = 0;
    virtual std::string visit(Op*) = 0;
    virtual std::string visit(App*) = 0;
};

class PrintVisitor : public StringVisitor {
public:
    std::string visit(Terminal*) override;
    std::string visit(Quant*) override;
    std::string visit(Op*) override;
    std::string visit(App*) override;
};

class OperateVisitor : public StringVisitor {
public:
    std::string visit(Terminal*) override;
    std::string visit(Quant*) override;
    std::string visit(Op*) override;
    std::string visit(App*) override;
};

class SimplifyRuleVisitor : public StringVisitor {
public:
    std::string visit(Terminal*) override;
    std::string visit(Quant*) override;
    std::string visit(Op*) override;
    std::string visit(App*) override;
};

class BooleanVisitor {
public:
    virtual bool visit(Terminal*) = 0;
    virtual bool visit(Quant*) = 0;
    virtual bool visit(Op*) = 0;
    virtual bool visit(App*) = 0;
};

class TerminalOrAppVisitor : public BooleanVisitor {
public:
    bool visit(Terminal*) override;
    bool visit(Quant*) override;
    bool visit(Op*) override;
    bool visit(App*) override;
};

class RequiresCongVisitor : public BooleanVisitor {
public:
    bool visit(Terminal*) override;
    bool visit(Quant*) override;
    bool visit(Op*) override;
    bool visit(App*) override;
};

class IsPrimaryBranchVisitor : public BooleanVisitor {
    std::shared_ptr<Term> branch;
public:
    explicit IsPrimaryBranchVisitor(std::shared_ptr<Term> b) : branch(std::move(b)) {}
    bool visit(Terminal*) override;
    bool visit(Quant*) override;
    bool visit(Op*) override;
    bool visit(App*) override;
    void setBranch(std::shared_ptr<Term> b) { branch = std::move(b);}
};

#endif // TERM_H

