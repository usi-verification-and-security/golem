#include "FrontEnd.h"

#include "StepCounter.h"

#include "ChcSystem.h"
#include "Normalizer.h"
#include "engine/EngineFactory.h"
#include "graph/ChcGraphBuilder.h"
#include "transformers/ConstraintSimplifier.h"
#include "transformers/TransformationPipeline.h"
#include "utils/SExpressions.h"

#include <osmt_terms.h>

#include <fstream>
#include <string>

namespace golem::vmt {

namespace {
using CommandArgs = std::vector<SExpression>;
CommandArgs dropOne(std::vector<SExpression> const & args) {
    return {args.begin() + 1, args.end()};
}

enum Command { ASSERT, DECLARE_FUN, DEFINE_FUN, SET_INFO };
const std::map<std::string_view, Command> nameToCommand{
    {"assert", ASSERT}, {"declare-fun", DECLARE_FUN}, {"define-fun", DEFINE_FUN}, {"set-info", SET_INFO}};
std::optional<Command> asCommand(std::string_view str) {
    auto it = nameToCommand.find(str);
    return it != nameToCommand.end() ? std::optional<Command>{it->second} : std::nullopt;
}
} // namespace

class VMTModel {
public:
    VMTModel(std::shared_ptr<opensmt::ArithLogic> logic, std::vector<PTRef> stateVars, std::vector<PTRef> nextStateVars,
             PTRef init, PTRef transition, std::map<unsigned, PTRef> invarProperties,
             std::map<unsigned, PTRef> liveProperties)
        : logic(std::move(logic)),
          stateVars(std::move(stateVars)),
          nextStateVars(std::move(nextStateVars)),
          init(init),
          transition(transition),
          invarProperties(std::move(invarProperties)),
          liveProperties(std::move(liveProperties)) {}

    [[nodiscard]] ChcSystem asChcs() const;
    [[nodiscard]] TransitionSystem asLivenessProblem() const;
    [[nodiscard]] ArithLogic & getLogic() const { return *logic; }
    [[nodiscard]] bool isSafetyProblem() const { return invarProperties.size() == 1 and liveProperties.empty(); }
    [[nodiscard]] bool isLivenessProblem() const { return liveProperties.size() == 1 and invarProperties.empty(); }

private:
    std::shared_ptr<opensmt::ArithLogic> logic;
    std::vector<PTRef> stateVars;
    std::vector<PTRef> nextStateVars;
    PTRef init;
    PTRef transition;
    std::map<unsigned, PTRef> invarProperties;
    std::map<unsigned, PTRef> liveProperties;
};

class VMTModelBuilder {
public:
    void resolve(SExpression const &);
    VMTModel build();

private:
    void resolveDeclareFun(CommandArgs const &);
    void resolveDefineFun(CommandArgs const &);
    void resolveAssert(SExpression const &);

    void newVariable(std::string name, std::string type) {
        vars.push_back({.name = std::move(name), .type = std::move(type)});
    }

    struct Var {
        std::string name;
        std::string type;
    };

    struct Defs {
        std::string name;
        std::string type;
        SExpression value;
    };
    std::vector<Var> vars;
    std::vector<Defs> defs;
};

VMTModel parse(std::istream & input) {
    VMTModelBuilder builder;
    SExpressionParser parser(input);
    assert(not parser.isEOF());
    while (not parser.isEOF()) {
        auto expression = parser.parseExpression();
        builder.resolve(expression);
    }
    return builder.build();
}

void VMTModelBuilder::resolve(SExpression const & command) {
    if (isAtom(command)) { throw std::logic_error("Unexpected command: " + command.toString()); }
    auto const & args = asSubExpressions(command);
    assert(not args.empty());
    auto const & commandNameExpr = args[0];
    if (not isAtom(commandNameExpr)) { throw std::logic_error("Unknown command: " + commandNameExpr.toString()); }
    auto const & commandName = asAtom(commandNameExpr);
    auto maybeKnownCommand = asCommand(commandName);
    if (not maybeKnownCommand) { throw std::logic_error("Unknown command: " + commandName); }
    switch (maybeKnownCommand.value()) {
        case DECLARE_FUN:
            return resolveDeclareFun(dropOne(args));
        case DEFINE_FUN:
            return resolveDefineFun(dropOne(args));
        case ASSERT: {
            assert(args.size() == 2);
            return resolveAssert(args[1]);
        }
        case SET_INFO:
            // TODO: Do something?
            return;
        default:
            assert(false);
            throw std::logic_error("UNREACHABLE");
    }
}

void VMTModelBuilder::resolveDeclareFun(CommandArgs const & args) {
    assert(args.size() == 3);
    assert(not isAtom(args[1]) and asSubExpressions(args[1]).empty());
    newVariable(asAtom(args[0]), asAtom(args[2]));
}

void VMTModelBuilder::resolveDefineFun(CommandArgs const & args) {
    assert(args.size() == 4);
    assert(isAtom(args[0]));
    auto const & name = asAtom(args[0]);
    assert(not isAtom(args[1]));
    if (not asSubExpressions(args[1]).empty()) {
        throw std::logic_error("define-fun with parameters is not yet handled!");
    }
    assert(isAtom(args[2]));
    auto const & type = asAtom(args[2]);
    defs.push_back({.name = name, .type = type, .value = args[3]});
}

void VMTModelBuilder::resolveAssert(SExpression const &) {
    // Ignore for now
}

VMTModel VMTModelBuilder::build() {
    auto logic = [this]() -> std::unique_ptr<ArithLogic> {
        struct {
            bool reals{false};
            bool ints{false};
            bool other{false};
        } requestedTypes;
        for (auto const & [_, type] : vars) {
            if (type == "Real") {
                requestedTypes.reals = true;
            } else if (type == "Int") {
                requestedTypes.ints = true;
            } else if (type != "Bool") {
                requestedTypes.other = true;
            }
        }
        for (auto const & [_, type, def] : defs) {
            if (type == "Real") {
                requestedTypes.reals = true;
            } else if (type == "Int") {
                requestedTypes.ints = true;
            } else if (type != "Bool") {
                requestedTypes.other = true;
            }
        }
        if (requestedTypes.other) { throw std::logic_error("Cannot handle input theory!"); }
        if (requestedTypes.reals and requestedTypes.ints) { throw std::logic_error("Cannot handle mixed arithmetic!"); }
        if (requestedTypes.reals) { return std::make_unique<ArithLogic>(opensmt::Logic_t::QF_LRA); }
        if (requestedTypes.ints) { return std::make_unique<ArithLogic>(opensmt::Logic_t::QF_LIA); }
        // Only bools
        return std::make_unique<ArithLogic>(opensmt::Logic_t::QF_LRA);
    }();

    struct {
        std::map<std::string, PTRef> nameToVar;
        std::vector<std::pair<PTRef, PTRef>> currentNextPairs;
        std::vector<PTRef> auxiliaryVars;
        std::map<std::string, PTRef> nameToDef;
        PTRef init{PTRef_Undef};
        PTRef trans{PTRef_Undef};
        std::map<unsigned, PTRef> invarProperties;
        std::map<unsigned, PTRef> liveProperties;
    } gatherer;

    for (auto const & var : vars) {
        PTRef varTerm = [&]() -> PTRef {
            if (var.type == "Int") {
                return logic->mkIntVar(var.name.c_str());
            } else if (var.type == "Real") {
                return logic->mkRealVar(var.name.c_str());
            } else if (var.type == "Bool") {
                return logic->mkBoolVar(var.name.c_str());
            }
            return PTRef_Undef;
        }();
        gatherer.nameToVar.insert({var.name, varTerm});
    }

    auto tryParseConstant = [](std::string const & str, ArithLogic & logic) {
        PTRef val = logic.mkConst(str.c_str());
        return val == PTRef_Undef ? std::nullopt : std::optional<PTRef>{val};
    };

    // TODO: Simplify with deducing this in C++23
    auto parseTerm = [&](SExpression const & sexpr) -> PTRef {
        auto impl = [&](SExpression const & sexpr, auto & impl_ref) {
            if (isAtom(sexpr)) {
                if (auto const it = gatherer.nameToVar.find(asAtom(sexpr)); it != gatherer.nameToVar.end()) {
                    return it->second;
                }
                if (auto const it = gatherer.nameToDef.find(asAtom(sexpr)); it != gatherer.nameToDef.end()) {
                    return it->second;
                }
                std::optional<PTRef> maybeConstant = tryParseConstant(asAtom(sexpr), *logic);
                if (maybeConstant.has_value()) { return maybeConstant.value(); }
                return PTRef_Undef;
            }
            auto subexpressions = asSubExpressions(sexpr);
            auto const & op = asAtom(subexpressions[0]);
            vec<PTRef> args;
            for (unsigned i = 1; i < subexpressions.size(); ++i) {
                args.push(impl_ref(subexpressions[i], impl_ref));
            }
            if (op == "and") {
                return logic->mkAnd(std::move(args));
            } else if (op == "or") {
                return logic->mkOr(std::move(args));
            } else if (op == "not") {
                return logic->mkNot(std::move(args));
            } else if (op == "=") {
                return logic->mkEq(std::move(args));
            } else if (op == "<=") {
                return logic->mkLeq(std::move(args));
            } else if (op == "+") {
                return logic->mkPlus(std::move(args));
            } else if (op == "-") {
                assert(args.size() <= 2 and args.size() >= 1);
                if (args.size() == 1) { return logic->mkNeg(args[0]); }
                return logic->mkMinus(std::move(args));
            } else if (op == "*") {
                return logic->mkTimes(std::move(args));
            }
            throw std::logic_error("UNIMPLEMENTED operator " + op);
            return PTRef_Undef;
        };
        return impl(sexpr, impl);
    };

    for (auto const & [name, type, def] : defs) {
        // TODO: Use proper term parsing, with symbol table and stuff
        auto const & subExpressions = asSubExpressions(def);
        assert(isAtom(subExpressions[0]));
        auto const & op = asAtom(subExpressions[0]);
        PTRef term = [&]() -> PTRef {
            if (op == "!") {
                PTRef term = parseTerm(subExpressions[1]);
                // process annotations
                for (unsigned i = 2; i < subExpressions.size(); ++i) {
                    auto const & annotation = asAtom(subExpressions[i]);
                    if (annotation == ":init") {
                        gatherer.init = term;
                    } else if (annotation == ":trans") {
                        gatherer.trans = term;
                    } else if (annotation == ":invar-property") {
                        ++i;
                        unsigned index = std::stoull(asAtom(subExpressions[i]));
                        gatherer.invarProperties.insert({index, term});
                    } else if (annotation == ":live-property") {
                        ++i;
                        unsigned index = std::stoull(asAtom(subExpressions[i]));
                        gatherer.liveProperties.insert({index, term});
                    } else if (annotation == ":next") {
                        ++i;
                        auto const & nextVarName = asAtom(subExpressions[i]);
                        auto it = gatherer.nameToVar.find(nextVarName);
                        if (it == gatherer.nameToVar.end()) {
                            auto [it2, inserted] = gatherer.nameToVar.insert(
                                {nextVarName, logic->mkVar(logic->getSortRef(term), nextVarName.c_str())});
                            assert(inserted);
                            it = it2;
                        }
                        assert(it != gatherer.nameToVar.end());
                        gatherer.currentNextPairs.emplace_back(term, it->second);
                    }
                }
                return term;
            }
            return parseTerm(def);
        }();
        gatherer.nameToDef.insert({name, term});
    }

    std::vector<PTRef> stateVars;
    std::vector<PTRef> nextStateVars;
    for (auto const & [current, next] : gatherer.currentNextPairs) {
        stateVars.push_back(current);
        nextStateVars.push_back(next);
    }
    return {std::move(logic),
            std::move(stateVars),
            std::move(nextStateVars),
            gatherer.init,
            gatherer.trans,
            std::move(gatherer.invarProperties),
            std::move(gatherer.liveProperties)};
}

ChcSystem VMTModel::asChcs() const {
    ChcSystem chcs;
    std::vector<SRef> argTypes;
    std::transform(stateVars.begin(), stateVars.end(), std::back_inserter(argTypes),
                   [&](PTRef var) { return logic->getSortRef(var); });
    SymRef predicate = logic->declareFun("P", logic->getSort_bool(), argTypes);
    PTRef statePredicate = logic->mkUninterpFun(predicate, stateVars);

    ChClause init = {.head = {statePredicate}, .body = {.interpretedPart = {this->init}, .uninterpretedPart = {}}};

    ChClause tr = {.head = {logic->mkUninterpFun(predicate, nextStateVars)},
                   .body = {.interpretedPart = {this->transition}, .uninterpretedPart = {{statePredicate}}}};

    assert(this->invarProperties.size() == 1);
    PTRef property = invarProperties.at(0);
    ChClause query = {.head = {logic->getTerm_false()},
                      .body = {.interpretedPart = {logic->mkNot(property)}, .uninterpretedPart = {{statePredicate}}}};

    chcs.addClause(std::move(init));
    chcs.addClause(std::move(tr));
    chcs.addClause(std::move(query));
    return chcs;
}

TransitionSystem VMTModel::asLivenessProblem() const {
    if (liveProperties.size() != 1) { throw std::logic_error("Cannot interpret VMT model as liveness problem!"); }
    PTRef property = liveProperties.begin()->second;
    // TODO: Auxiliary variables?
    return {*logic, std::make_unique<SystemType>(stateVars, std::vector<PTRef>{}, *logic), init, transition, property};
}

void printLivenessAnswer(StepCounter::Answer answer) {
    switch (answer) {
        case StepCounter::Answer::YES: {
            std::cout << "valid" << std::endl;
            break;
        }
        case StepCounter::Answer::UNKNOWN: {
            std::cout << "unknown" << std::endl;
            break;
        }
        case StepCounter::Answer::ERROR: {
            std::cout << "error" << std::endl;
            break;
        }
    }
}

void printAnswer(VerificationAnswer answer) {
    switch (answer) {
        case VerificationAnswer::SAFE: {
            std::cout << "safe" << std::endl;
            break;
        }
        case VerificationAnswer::UNSAFE: {
            std::cout << "unsafe" << std::endl;
            break;
        }
        case VerificationAnswer::UNKNOWN:
            std::cout << "unknown" << std::endl;
            break;
    }
}

void solveSafetyProblem(VMTModel const & vmtModel, Options const & options) {
    try {
        auto chcSystem = vmtModel.asChcs();
        auto & logic = vmtModel.getLogic();
        auto normalizedSystem = Normalizer{logic}.normalize(chcSystem);
        auto hypergraph = ChcGraphBuilder(logic).buildGraph(normalizedSystem);
        assert(hypergraph->isNormalGraph());
        TransformationPipeline::pipeline_t stages;
        stages.push_back(std::make_unique<ConstraintSimplifier>());
        auto [transformedGraph, _] = TransformationPipeline(std::move(stages)).transform(std::move(hypergraph));
        auto engineName = options.getOrDefault(Options::ENGINE, "spacer");
        auto engine = EngineFactory(logic, options).getEngine(engineName);
        auto result = engine->solve(*transformedGraph);
        printAnswer(result.getAnswer());
    } catch (LANonLinearException const &) {
        std::cout << "unknown\n;(Nonlinear arithmetic expression in the input)" << std::endl;
    }
}

void solveLivenessProblem(VMTModel const & vmtModel, Options const & options) {
    auto const ts = vmtModel.asLivenessProblem();
    auto res = StepCounter(options).checkLiveness(ts);
    printLivenessAnswer(res);
}

void run(std::string const & filename, Options const & options) {
    std::ifstream input(filename);
    if (input.bad()) { throw std::logic_error{"Unable to process input file: " + filename}; }
    VMTModel const vmtModel = parse(input);
    if (vmtModel.isSafetyProblem()) {
        solveSafetyProblem(vmtModel, options);
    } else if (vmtModel.isLivenessProblem()) {
        solveLivenessProblem(vmtModel, options);
    } else {
        printAnswer(VerificationAnswer::UNKNOWN);
    }
}

} // namespace golem::vmt
