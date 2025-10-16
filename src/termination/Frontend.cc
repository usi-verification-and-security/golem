/*
 * Copyright (c) 2025, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "ChcSystem.h"
#include "LassoDetector.h"
#include "Normalizer.h"
#include "ReachabilityTerm.h"
#include "ReachabilityNonterm.h"
#include "TransformationUtils.h"

#include "graph/ChcGraphBuilder.h"
#include "transformers/ConstraintSimplifier.h"
#include "transformers/EdgeInliner.h"
#include "transformers/FalseClauseRemoval.h"
#include "transformers/MultiEdgeMerger.h"
#include "transformers/NodeEliminator.h"
#include "transformers/RemoveUnreachableNodes.h"
#include "transformers/SimpleChainSummarizer.h"
#include "transformers/SingleLoopTransformation.h"
#include "transformers/TransformationPipeline.h"
#include "transformers/TrivialEdgePruner.h"

#include <cassert>
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>
#include <unordered_map>
#include <variant>
#include <vector>

namespace golem::termination {

struct SExpression {
    using args_t = std::vector<SExpression>;
    std::variant<std::string, args_t> data;

    [[nodiscard]] std::string toString() const;
};

inline bool isAtom(SExpression const & expr) {
    return std::holds_alternative<std::string>(expr.data);
}

inline std::string const & asAtom(SExpression const & expr) {
    assert(isAtom(expr));
    return std::get<std::string>(expr.data);
}

inline auto const & asSubExpressions(SExpression const & expr) {
    assert(!isAtom(expr));
    return std::get<SExpression::args_t>(expr.data);
}

inline auto & asSubExpressions(SExpression & expr) {
    assert(!isAtom(expr));
    return std::get<SExpression::args_t>(expr.data);
}

class SExpressionParser {
public:
    class ParsingException {};

    explicit SExpressionParser(std::istream & _input) : m_input(_input), m_token(static_cast<char>(m_input.get())) {}

    SExpression parseExpression();

    bool isEOF() {
        skipWhitespace();
        return m_input.eof();
    }

private:
    std::string parseToken();

    void skipWhitespace();

    [[nodiscard]] char token() const { return m_token; }

    void advance();

    std::istream & m_input;
    char m_token = 0;
};

struct LocationDeclaration {
    std::string name;
    std::vector<std::string> argTypes;
    std::string returnType;
};

struct Location {
    std::string name;
    std::vector<std::string> arguments;
};

struct Expr {
    enum struct Kind { And, Or, Eq, Leq, Geq, Lt, Gt, Add, Sub, Mul, Var, Const } kind;
    std::vector<std::shared_ptr<Expr>> children;
    std::string value;
};

struct Rule {
    Location lhs;
    Location rhs;
    std::shared_ptr<Expr> guard;
};

struct ITS {
    std::string format;
    std::string theory;
    std::unordered_map<std::string, LocationDeclaration> locations;
    std::string entrypoint;
    std::vector<Rule> rules;

    void resolve(SExpression const & topLevelDeclaration);
    static LocationDeclaration parseFun(SExpression const &);
    static Location parseLocationInstance(SExpression const &);
    static Rule parseRule(SExpression const &);
    static std::shared_ptr<Expr> parseExpr(SExpression const &);
    ChcSystem asChcs(ArithLogic & logic) const;
    ChcSystem asSafetyChcs(ArithLogic & logic) const;
};

ITS parseITS(std::istream & input) {
    ITS its;
    SExpressionParser parser(input);
    assert(not parser.isEOF());
    while (not parser.isEOF()) {
        auto expression = parser.parseExpression();
        its.resolve(expression);
    }
    return its;
}

/*
 *	Implementation
 */

std::string SExpression::toString() const {
    return std::visit(
        []<typename V>(V const & value) -> std::string {
            if constexpr (std::same_as<std::decay_t<V>, std::string>) {
                return value;
            } else if constexpr (std::same_as<std::decay_t<V>, args_t>) {
                std::stringstream result;
                result << '(';
                bool first = true;
                for (auto const & arg : value) {
                    if (!first) result << ' ';
                    result << arg.toString();
                    first = false;
                }
                result << ")";
                return result.str();
            }
        },
        data);
}

SExpression SExpressionParser::parseExpression() {
    skipWhitespace();
    if (token() == '(') {
        advance();
        skipWhitespace();
        std::vector<SExpression> subExpressions;
        while (token() != 0 && token() != ')') {
            subExpressions.emplace_back(parseExpression());
            skipWhitespace();
        }
        if (token() != ')') throw ParsingException{};
        // Simulate whitespace because we do not want to read the next token since it might block.
        m_token = ' ';
        return {std::move(subExpressions)};
    } else
        return {parseToken()};
}

namespace {
bool isWhiteSpace(char c) {
    return c == ' ' || c == '\n' || c == '\t' || c == '\r';
}
} // namespace

std::string SExpressionParser::parseToken() {
    std::string result;

    skipWhitespace();
    bool isPipe = token() == '|';
    if (isPipe) advance();
    while (token() != 0) {
        char c = token();
        if (isPipe && c == '|') {
            advance();
            break;
        } else if (!isPipe && (isWhiteSpace(c) || c == '(' || c == ')'))
            break;
        result.push_back(c);
        advance();
    }
    return result;
}

void SExpressionParser::advance() {
    if (!m_input.good()) throw ParsingException{};
    m_token = static_cast<char>(m_input.get());
    if (token() == ';')
        while (token() != '\n' && token() != 0)
            m_token = static_cast<char>(m_input.get());
}

void SExpressionParser::skipWhitespace() {
    while (isWhiteSpace(token()))
        advance();
}

void ITS::resolve(SExpression const & topLevelDeclaration) {
    if (isAtom(topLevelDeclaration)) { throw SExpressionParser::ParsingException{}; }
    auto const & expressions = asSubExpressions(topLevelDeclaration);
    if (expressions.empty()) { throw SExpressionParser::ParsingException{}; }
    auto const & keyword = asAtom(expressions[0]);
    if (keyword == "format") {
        this->format = asAtom(expressions[1]);
    } else if (keyword == "theory") {
        this->theory = asAtom(expressions[1]);
    } else if (keyword == "fun") {
        auto declaration = parseFun(topLevelDeclaration);
        this->locations.insert({declaration.name, declaration});
    } else if (keyword == "entrypoint") {
        this->entrypoint = asAtom(expressions[1]);
    } else if (keyword == "rule") {
        this->rules.push_back(parseRule(topLevelDeclaration));
    } else {
        throw SExpressionParser::ParsingException{};
    }
}

LocationDeclaration ITS::parseFun(SExpression const & expr) {
    const auto & args = asSubExpressions(expr);
    if (args.size() != 3 or asAtom(args[0]) != "fun") throw std::runtime_error("Invalid (fun ...) form");

    auto const & name = asAtom(args[1]);
    auto [argTypes,
          returnType] = [](SExpression const & typesExpr) -> std::pair<std::vector<std::string>, std::string> {
        if (isAtom(typesExpr)) {
            assert(asAtom(typesExpr) == "Int");
            return {{}, asAtom(typesExpr)};
        }
        auto const & arrowExpr = asSubExpressions(typesExpr);

        if (asAtom(arrowExpr[0]) != "->") throw std::runtime_error("Function type must use (-> ...)");

        std::vector<std::string> argTypes;
        for (size_t i = 1; i < arrowExpr.size() - 1; ++i) {
            argTypes.push_back(asAtom(arrowExpr[i]));
        }
        std::string const returnType = asAtom(arrowExpr.back());
        return {argTypes, returnType};
    }(args[2]);

    return {name, argTypes, returnType};
}

Location ITS::parseLocationInstance(SExpression const & expr) {
    if (isAtom(expr)) return {asAtom(expr), {}};

    auto const & args = asSubExpressions(expr);
    if (args.empty()) throw std::runtime_error("Location instance cannot be empty");

    std::string name = asAtom(args[0]);
    std::vector<std::string> arguments;
    for (size_t i = 1; i < args.size(); ++i) {
        arguments.push_back(asAtom(args[i]));
    }

    return {name, arguments};
}

Rule ITS::parseRule(SExpression const & expr) {
    auto const & args = asSubExpressions(expr);
    if (args.empty() or asAtom(args[0]) != "rule") throw std::runtime_error("Expected rule");

    if (args.size() < 3) throw std::runtime_error("Rule must define source and target term!");

    Location lhs = parseLocationInstance(args[1]);
    Location rhs = parseLocationInstance(args[2]);
    if (args.size() == 3) { return {lhs, rhs, nullptr}; }

    if (args.size() != 5) throw std::runtime_error("Invalid rule format: invalid guard!");

    if (asAtom(args[3]) != ":guard") throw std::runtime_error("Expected :guard keyword");
    auto parsedGuard = parseExpr(args[4]);

    return {lhs, rhs, parsedGuard};
}

std::shared_ptr<Expr> ITS::parseExpr(SExpression const & expr) {
    if (isAtom(expr)) {
        auto const & val = asAtom(expr);
        if (isdigit(val[0]) or (val[0] == '-' && val.size() > 1))
            return std::make_shared<Expr>(Expr{Expr::Kind::Const, {}, val});
        else
            return std::make_shared<Expr>(Expr{Expr::Kind::Var, {}, val});
    }

    assert(not isAtom(expr));
    auto const & args = asSubExpressions(expr);
    if (args.empty()) throw std::runtime_error("Empty expression");

    std::string const op = asAtom(args[0]);
    if (op == "exists") { // We can get away with parsing just the inner expression, because we all variables are Ints
        // args[1] are the bounded variables
        // args[2] is the inner expression
        return parseExpr(args[2]);
    }
    Expr::Kind kind;
    if (op == "and")
        kind = Expr::Kind::And;
    else if (op == "or")
        kind = Expr::Kind::Or;
    else if (op == "=")
        kind = Expr::Kind::Eq;
    else if (op == "+")
        kind = Expr::Kind::Add;
    else if (op == "-")
        kind = Expr::Kind::Sub;
    else if (op == "*")
        kind = Expr::Kind::Mul;
    else if (op == "<=")
        kind = Expr::Kind::Leq;
    else if (op == ">=")
        kind = Expr::Kind::Geq;
    else if (op == "<")
        kind = Expr::Kind::Lt;
    else if (op == ">")
        kind = Expr::Kind::Gt;
    else
        throw std::runtime_error("Unknown operator: " + op);

    std::vector<std::shared_ptr<Expr>> children;
    for (size_t i = 1; i < args.size(); ++i) {
        children.push_back(parseExpr(args[i]));
    }

    return std::make_shared<Expr>(Expr{kind, std::move(children), ""});
}

namespace {
PTRef translate(ArithLogic & logic, Expr const & expr);

vec<PTRef> translate(ArithLogic & logic, decltype(Expr::children) const & args) {
    vec<PTRef> pargs;
    for (auto const & arg : args) {
        pargs.push(translate(logic, *arg));
    }
    return pargs;
}

PTRef translate(ArithLogic & logic, Expr const & expr) {
    switch (expr.kind) {
        case Expr::Kind::Const:
            return logic.mkConst(logic.getSort_int(), expr.value.c_str());
        case Expr::Kind::Var:
            return logic.mkIntVar(expr.value.c_str());
        case Expr::Kind::Add:
            return logic.mkPlus(translate(logic, expr.children));
        case Expr::Kind::Sub:
            return logic.mkMinus(translate(logic, expr.children));
        case Expr::Kind::Mul:
            return logic.mkTimes(translate(logic, expr.children));
        case Expr::Kind::Eq:
            return logic.mkEq(translate(logic, expr.children));
        case Expr::Kind::Leq:
            return logic.mkLeq(translate(logic, expr.children));
        case Expr::Kind::Geq:
            return logic.mkGeq(translate(logic, expr.children));
        case Expr::Kind::Lt:
            return logic.mkLt(translate(logic, expr.children));
        case Expr::Kind::Gt:
            return logic.mkGt(translate(logic, expr.children));
        case Expr::Kind::And:
            return logic.mkAnd(translate(logic, expr.children));
        case Expr::Kind::Or:
            return logic.mkOr(translate(logic, expr.children));
    }
    return PTRef_Undef;
}
} // namespace

ChcSystem ITS::asChcs(ArithLogic & logic) const {
    assert(this->format == "LCTRS");
    assert(this->theory == "Ints");
    ChcSystem chcs;
    std::unordered_map<std::string, SymRef> locationsToPredicates;
    for (auto && [_, locationDeclaration] : this->locations) {
        assert(std::all_of(locationDeclaration.argTypes.begin(), locationDeclaration.argTypes.end(),
                           [](auto const & typeName) { return typeName == "Int"; }));
        auto const predicate = logic.declareFun(locationDeclaration.name, logic.getSort_bool(),
                                                std::vector(locationDeclaration.argTypes.size(), logic.getSort_int()));
        locationsToPredicates.insert({locationDeclaration.name, predicate});
        chcs.addUninterpretedPredicate(predicate);
    }

    for (auto const & rule : this->rules) {
        auto source = locationsToPredicates.at(rule.lhs.name);
        auto target = locationsToPredicates.at(rule.rhs.name);
        ChClause clause;
        {
            vec<PTRef> args;
            for (auto const & argName : rule.rhs.arguments) {
                args.push(logic.mkIntVar(argName.c_str()));
            }
            clause.head = {logic.mkUninterpFun(target, std::move(args))};
        }
        ChcBody body;
        {
            vec<PTRef> args;
            for (auto const & argName : rule.lhs.arguments) {
                args.push(logic.mkIntVar(argName.c_str()));
            }
            PTRef bodyPredicate = logic.mkUninterpFun(source, std::move(args));
            PTRef constraint = rule.guard ? translate(logic, *rule.guard) : logic.getTerm_true();
            clause.body = ChcBody{.interpretedPart = {constraint}, .uninterpretedPart = {{bodyPredicate}}};
        }
        chcs.addClause(std::move(clause));
    }

    {
        auto entryPredicateSym = locationsToPredicates.at(this->entrypoint);
        auto entryLoc = this->locations.at(this->entrypoint);
        vec<PTRef> auxArgs;
        unsigned counter = 0u;
        for (auto const & argType : entryLoc.argTypes) {
            assert(argType == "Int");
            (void)argType;
            auto argName = "e" + std::to_string(counter++);
            auxArgs.push(logic.mkIntVar(argName.c_str()));
        }
        PTRef entryPredicate = logic.mkUninterpFun(entryPredicateSym, std::move(auxArgs));
        chcs.addClause(ChcHead{.predicate = {entryPredicate}},
                       ChcBody{.interpretedPart = {logic.getTerm_true()}, .uninterpretedPart = {}});
    }
    return chcs;
}

// This function encodes termination problem as safety - every predicate which is not a



// source of some clause gets corresponding query clause.


// If there is no such predicate, then safety-based termination doesn't make sense as it requires


// some sort of loop guard


ChcSystem ITS::asSafetyChcs(ArithLogic & logic) const {
    assert(this->format == "LCTRS");
    assert(this->theory == "Ints");
    ChcSystem chcs;
    std::unordered_map<std::string, int> exit_locations;
    std::unordered_map<std::string, SymRef> locationsToPredicates;
    for (auto && [_, locationDeclaration] : this->locations) {
        assert(std::all_of(locationDeclaration.argTypes.begin(), locationDeclaration.argTypes.end(),
                           [](auto const & typeName) { return typeName == "Int"; }));
        auto const predicate = logic.declareFun(locationDeclaration.name, logic.getSort_bool(),
                                                std::vector(locationDeclaration.argTypes.size(), logic.getSort_int()));
        locationsToPredicates.insert({locationDeclaration.name, predicate});
        chcs.addUninterpretedPredicate(predicate);
    }

    int i = 0;
    for (auto const & rule : this->rules) {
        auto source = locationsToPredicates.at(rule.lhs.name);
        auto target = locationsToPredicates.at(rule.rhs.name);
        exit_locations[rule.lhs.name] = -1;

        if (!exit_locations.contains(rule.rhs.name)) {
            exit_locations[rule.rhs.name] = i;
        }
        i++;
        ChClause clause;
        {
            vec<PTRef> args;
            for (auto const & argName : rule.rhs.arguments) {
                args.push(logic.mkIntVar(argName.c_str()));
            }
            clause.head = {logic.mkUninterpFun(target, std::move(args))};
        }
        ChcBody body;
        {
            vec<PTRef> args;
            for (auto const & argName : rule.lhs.arguments) {
                args.push(logic.mkIntVar(argName.c_str()));
            }
            PTRef bodyPredicate = logic.mkUninterpFun(source, std::move(args));
            PTRef constraint = rule.guard ? translate(logic, *rule.guard) : logic.getTerm_true();
            clause.body = ChcBody{.interpretedPart = {constraint}, .uninterpretedPart = {{bodyPredicate}}};
        }
        chcs.addClause(std::move(clause));
    }
    {
        auto entryPredicateSym = locationsToPredicates.at(this->entrypoint);
        auto entryLoc = this->locations.at(this->entrypoint);
        vec<PTRef> auxArgs;
        unsigned counter = 0u;
        for (auto const & argType : entryLoc.argTypes) {
            assert(argType == "Int");
            (void)argType;
            auto argName = "e" + std::to_string(counter++);
            auxArgs.push(logic.mkIntVar(argName.c_str()));
        }
        PTRef entryPredicate = logic.mkUninterpFun(entryPredicateSym, std::move(auxArgs));
        chcs.addClause(ChcHead{.predicate = {entryPredicate}},
                       ChcBody{.interpretedPart = {logic.getTerm_true()}, .uninterpretedPart = {}});
    }
    bool exists_exit = false;
    for (auto [pred, exit]: exit_locations) {
        if (exit != -1) {
            vec<PTRef> args;
            for (auto const & argName : rules[exit].rhs.arguments) {
                args.push(logic.mkIntVar(argName.c_str()));
            }
            PTRef exitPredicate = logic.mkUninterpFun(locationsToPredicates[pred], std::move(args));
            chcs.addClause(ChcHead{logic.getTerm_false()},
                           ChcBody{.interpretedPart = {logic.getTerm_true()}, .uninterpretedPart = {{exitPredicate}}});
            exists_exit = true;
        }
    }
    if (!exists_exit) {
        for (auto [pred, exit]: exit_locations) {
                vec<PTRef> args;
                for (auto const & argName : rules[exit].rhs.arguments) {
                    args.push(logic.mkIntVar(argName.c_str()));
                }
                PTRef exitPredicate = logic.mkUninterpFun(locationsToPredicates[pred], std::move(args));
                chcs.addClause(ChcHead{logic.getTerm_false()},
                               ChcBody{.interpretedPart = {logic.getTerm_true()}, .uninterpretedPart = {{exitPredicate}}});
        }
    }
    return chcs;
}



void run(std::string const & filename, Options const & options) {
    std::ifstream input(filename);
    if (input.bad()) { throw std::logic_error{"Unable to process input file: " + filename}; }
    ITS its = parseITS(input);
    ArithLogic logic(Logic_t::QF_LIA);
    try {
        auto chcs = its.asChcs(logic);
        // ChcPrinter{logic, std::cout}.print(chcs);
        Normalizer normalizer(logic);
        auto normalizedSystem = normalizer.normalize(chcs);

        auto hypergraph = ChcGraphBuilder(logic).buildGraph(normalizedSystem);
        assert(hypergraph->isNormalGraph());
        TransformationPipeline::pipeline_t stages;
        stages.push_back(std::make_unique<ConstraintSimplifier>());
        stages.push_back(std::make_unique<SimpleChainSummarizer>());
        stages.push_back(std::make_unique<RemoveForwardUnreachableNodes>());
        stages.push_back(std::make_unique<SimpleNodeEliminator>());
        stages.push_back(std::make_unique<EdgeInliner>());
        stages.push_back(std::make_unique<FalseClauseRemoval>());
        stages.push_back(std::make_unique<MultiEdgeMerger>());
        stages.push_back(std::make_unique<SimpleChainSummarizer>());
        stages.push_back(std::make_unique<TrivialEdgePruner>());
        auto [transformedGraph, _] = TransformationPipeline(std::move(stages)).transform(std::move(hypergraph));
        assert(transformedGraph->isNormalGraph());
        auto graph = transformedGraph->toNormalGraph();
        auto ts = [&]() -> std::unique_ptr<TransitionSystem> {
            if (isTransitionSystemWithoutQuery(*graph)) { return toTransitionSystem(*graph, true); }
            auto [ts, bt] = SingleLoopTransformation{}.transform(*graph);
            return std::move(ts);
        }();
        // auto res = ReachabilityTerm{options}.termination(*ts);
        // if (res == ReachabilityTerm::Answer::YES) {
        //     std::cout << "YES" << std::endl;
        // } else if (res == ReachabilityTerm::Answer::UNKNOWN) {
        //     auto res = LassoDetector{options}.find_lasso(*ts);
        //     if (res == LassoDetector::Answer::LASSO) {
        //         std::cout << "NO" << std::endl;
        //     } else if (res == LassoDetector::Answer::NO_LASSO) {
                auto res = ReachabilityNonterm{options}.nontermination(*ts);
                if (res == ReachabilityNonterm::Answer::YES) {
                    std::cout << "YES" << std::endl;
                } else if (res == ReachabilityNonterm::Answer::NO) {
                    std::cout << "NO" << std::endl;
                } else if (res == ReachabilityNonterm::Answer::UNKNOWN) {
                    std::cout << "MAYBE\n;(no lasso exists)" << std::endl;
                } else {
                    std::cout << "ERROR (when doing reachability procedure)" << std::endl;
                }
    //     } else {
    //         std::cout << "ERROR (when searching for lasso in the system)" << std::endl;
    //     }
    // } else {
    //     std::cout << "ERROR (when searching for termination in the system)" << std::endl;
    // }
    } catch (LANonLinearException const &) {
        std::cout << "MAYBE\n;(Nonlinear arithmetic expression in the input)" << std::endl;
    }
}

} // namespace golem::termination
