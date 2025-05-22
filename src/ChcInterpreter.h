/*
 * Copyright (c) 2020-2025, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef GOLEM_CHCINTERPRETER_H
#define GOLEM_CHCINTERPRETER_H

#include "ChcSystem.h"
#include "Normalizer.h"
#include "Options.h"

#include "proofs/Term.h"
#include "transformers/Transformer.h"

#include "osmt_parser.h"

#include <memory>
#include <optional>

namespace golem {
class LetBinder {
    PTRef currentValue;
    std::vector<PTRef> * shadowedValues;

public:
    explicit LetBinder(PTRef val) : currentValue(val), shadowedValues(nullptr) {}
    ~LetBinder() { delete shadowedValues; }
    LetBinder(const LetBinder &) = delete;
    LetBinder & operator=(const LetBinder &) = delete;
    LetBinder(LetBinder &&) = default;
    LetBinder & operator=(LetBinder &&) = default;
    PTRef getValue() const { return currentValue; }
    bool hasShadowValue() const { return shadowedValues && !shadowedValues->empty(); }
    void restoreShadowedValue() {
        assert(hasShadowValue());
        currentValue = shadowedValues->back();
        shadowedValues->pop_back();
    }
    void addValue(PTRef val) {
        if (not shadowedValues) { shadowedValues = new std::vector<PTRef>(); }
        shadowedValues->push_back(currentValue);
        currentValue = val;
    }
};

class LetRecords {
    std::unordered_map<const char *, LetBinder, StringHash, Equal<const char *>> letBinders;
    std::vector<const char *> knownBinders;
    std::vector<std::size_t> frameLimits;

    bool has(const char * name) const { return letBinders.count(name) != 0; }

public:
    PTRef getOrUndef(const char * letSymbol) const {
        auto it = letBinders.find(letSymbol);
        if (it != letBinders.end()) { return it->second.getValue(); }
        return PTRef_Undef;
    }
    void pushFrame() { frameLimits.push_back(knownBinders.size()); }
    void popFrame() {
        auto limit = frameLimits.back();
        frameLimits.pop_back();
        while (knownBinders.size() > limit) {
            const char * binder = knownBinders.back();
            knownBinders.pop_back();
            assert(this->has(binder));
            auto & values = letBinders.at(binder);
            if (values.hasShadowValue()) {
                values.restoreShadowedValue();
            } else {
                letBinders.erase(binder);
            }
        }
    }

    void addBinding(const char * name, PTRef arg) {
        knownBinders.push_back(name);
        if (not this->has(name)) {
            letBinders.insert(std::make_pair(name, LetBinder(arg)));
        } else {
            letBinders.at(name).addValue(arg);
        }
    }
};

class ChcInterpreterContext {
public:
    std::unique_ptr<ChcSystem> interpretSystemAst(const ASTNode * root);
    ChcInterpreterContext(ArithLogic & logic, Options const & opts) : logic(logic), opts(opts) {}

    std::vector<std::string> operators = {"+", "-",  "/",  "*", "and", "or",  "=>",  "not",
                                          "=", ">=", "<=", ">", "<",   "ite", "mod", "div"};

    bool isOperator(const std::string & val) {
        for (const std::string & op : operators) {
            if (op == val) { return true; }
        }
        return false;
    }

private:
    ArithLogic & logic;
    Options const & opts;
    std::unique_ptr<ChcSystem> system;
    std::vector<std::shared_ptr<Term>> originalAssertions;
    bool doExit = false;
    LetRecords letRecords;

    void interpretCommand(ASTNode & node);

    void interpretDeclareFun(ASTNode & node);

    void interpretAssert(ASTNode & node);

    void interpretCheckSat();

    static void reportError(std::string const & msg);

    VerificationResult solve(std::string const & engine, ChcDirectedHyperGraph const & hyperGraph);

    [[nodiscard]] bool hasWorkAfterAnswer() const;

    void doWorkAfterAnswer(VerificationResult result, ChcDirectedHyperGraph const & originalGraph,
                           WitnessBackTranslator & translator,
                           Normalizer::Equalities const & normalizingEqualities) const;

    void solveWithMultipleEngines(std::string const & engines, std::unique_ptr<ChcDirectedHyperGraph> hyperGraph,
                                  std::unique_ptr<ChcDirectedHyperGraph> originalGraph,
                                  std::unique_ptr<WitnessBackTranslator> translator,
                                  Normalizer::Equalities const & normalizingEqualities);

    [[nodiscard]] SRef sortFromASTNode(ASTNode const & node) const;

    PTRef parseTopLevelAssertion(ASTNode const & node);
    PTRef parseTerm(ASTNode const & node);

    std::shared_ptr<Term> ASTtoTerm(ASTNode const & node);

    // Building CHCs and helper methods

    std::optional<ChClause> chclauseFromPTRef(PTRef ref);

    bool isUninterpretedPredicate(PTRef ref) const;
};

class ChcInterpreter {
public:
    std::unique_ptr<ChcSystem> interpretSystemAst(ArithLogic & logic, const ASTNode * root);

    explicit ChcInterpreter(Options const & opts) : opts(opts) {}

private:
    Options const & opts;
};
} // namespace golem

#endif // GOLEM_CHCINTERPRETER_H
