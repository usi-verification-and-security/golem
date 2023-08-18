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
    enum terminalType{ VAR, REAL, INT, SORT };
    virtual std::string string() = 0;
    virtual std::string stringInst(std::vector<std::vector<std::string>> instPairs) = 0;
};

class Terminal : public Term {
    std::string val;
    terminalType type;
public:
    Terminal(std::string  val, terminalType t) : val(std::move(val)), type(t) {}
    std::string string() override { return val;}
    std::string stringInst(std::vector<std::vector<std::string>> instPairs) override {
        for (std::vector<std::string> pair : inst)
    }
};

class Op : public Term {
    std::string operation;
    std::vector<std::shared_ptr<Term>> args;
public:
    Op(std::string  opcode, std::vector<std::shared_ptr<Term>> args) : operation(std::move(opcode)), args(std::move(args)) {}
    std::string string() override {
        std::stringstream ss;
        ss << "(" << operation;
        for (const std::shared_ptr<Term>& arg : args){
            ss << " " << arg->string();
        }
        ss << ")";
        return ss.str();
    }
    std::string stringInst(std::vector<std::vector<std::string>> instPairs) override {
        std::stringstream ss;
        ss << "(" << operation;
        for (const std::shared_ptr<Term>& arg : args){
            ss << " " << arg->stringInst(instPairs);
        }
        ss << ")";
        return ss.str();
    }
};

class App : public Term {
    std::string fun;
    std::vector<std::shared_ptr<Term>> args;
public:
    App(std::string  fun, std::vector<std::shared_ptr<Term>> args) : fun(std::move(fun)), args(std::move(args)){}
    std::string string() override {
        std::stringstream ss;
        ss << "(" << fun;
        for (const std::shared_ptr<Term>& arg : args){
            ss << " " << arg->string();
        }
        ss << ")";
        return ss.str();
    }
    std::string stringInst(std::vector<std::vector<std::string>> instPairs) override {
        std::stringstream ss;
        ss << "(" << fun;
        for (const std::shared_ptr<Term>& arg : args){
            ss << " " << arg->stringInst(instPairs);
        }
        ss << ")";
        return ss.str();
    }
};

class Quant : public Term {
    std::string quant;
    std::vector<std::shared_ptr<Term>> vars;
    std::vector<std::shared_ptr<Term>> sorts;
    std::shared_ptr<Term> coreTerm;
public:
    Quant(std::string quant, std::vector<std::shared_ptr<Term>> vars, std::vector<std::shared_ptr<Term>> sorts, std::shared_ptr<Term> coreTerm) :  quant(std::move(quant)),
          vars(std::move(vars)), sorts(std::move(sorts)), coreTerm(std::move(coreTerm)){}
    std::string string() override {
        std::stringstream ss;
        ss << "(" << quant << "(";
        for (int i = 0; i < vars.size(); i++){
            ss << "(" << vars[i]->string() << " " << sorts[i]->string() << ")";
            if(i+1 != vars.size()){
                ss << " ";
            }
        }
        ss << ")" << " " << coreTerm->string() << ")";
        return ss.str();
    }
    std::string stringInst(std::vector<std::vector<std::string>> instPairs) override {
        std::stringstream ss;
        ss << "(" << quant << "(";
        for (int i = 0; i < vars.size(); i++){
            ss << "(" << vars[i]->string() << " " << sorts[i]->string() << ")";
            if(i+1 != vars.size()){
                ss << " ";
            }
        }
        ss << ")" << " " << coreTerm->stringInst(instPairs) << ")";
        return ss.str();
    }
};

#endif // TERM_H

