/*
 * Copyright (c) 2025, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "LassoDetector.h"

#include "ChcSystem.h"
#include "Normalizer.h"
#include "TermUtils.h"
#include "engine/EngineFactory.h"
#include "graph/ChcGraphBuilder.h"

namespace golem::termination {
LassoDetector::Answer LassoDetector::find_lasso(TransitionSystem const & system) {
    ArithLogic & logic = dynamic_cast<ArithLogic &>(system.getLogic());
    ChcSystem chcs;
    SymRef predicate = [&]() -> SymRef {
        vec<SRef> argSorts;
        for (PTRef var : system.getStateVars()) {
            argSorts.push(logic.getSortRef(var));
        }
        for (PTRef var : system.getStateVars()) {
            argSorts.push(logic.getSortRef(var));
        }
        argSorts.push(logic.getSort_bool());
        return logic.declareFun("L", logic.getSort_bool(), std::move(argSorts));
    }();
    chcs.addUninterpretedPredicate(predicate);
    // Init clause
    auto notYetSaved = [&]() -> PTRef {
        vec<PTRef> args;
        for (PTRef var : system.getStateVars()) {
            args.push(var);
        }
        for (PTRef var : system.getStateVars()) {
            args.push(logic.getDefaultValuePTRef(logic.getSortRef(var)));
        }
        args.push(logic.getTerm_false());
        return logic.mkUninterpFun(predicate, std::move(args));
    }();
    chcs.addClause(ChcHead{UninterpretedPredicate{notYetSaved}}, ChcBody{InterpretedFla{system.getInit()}, {}});
    // no saving
    {
        std::vector<PTRef> storedCopy;
        for (PTRef var : system.getStateVars()) {
            TimeMachine tm(logic);
            storedCopy.push_back(tm.sendVarThroughTime(var, -1));
        }
        PTRef flag = logic.mkBoolVar("stored");
        PTRef body = [&]() -> PTRef {
            vec<PTRef> args;
            for (PTRef var : system.getStateVars()) {
                args.push(var);
            }
            for (PTRef var : storedCopy) {
                args.push(var);
            }
            args.push(flag);
            return logic.mkUninterpFun(predicate, std::move(args));
        }();
        PTRef head = [&]() -> PTRef {
            vec<PTRef> args;
            for (PTRef var : system.getNextStateVars()) {
                args.push(var);
            }
            for (PTRef var : storedCopy) {
                args.push(var);
            }
            args.push(flag);
            return logic.mkUninterpFun(predicate, std::move(args));
        }();
        chcs.addClause(ChcHead{UninterpretedPredicate{head}},
                       ChcBody{InterpretedFla{system.getTransition()}, {UninterpretedPredicate{body}}});
    }
    // saving
    {
        PTRef head = [&]() -> PTRef {
            vec<PTRef> args;
            for (PTRef var : system.getNextStateVars()) {
                args.push(var);
            }
            for (PTRef var : system.getStateVars()) {
                args.push(var);
            }
            args.push(logic.getTerm_true());
            return logic.mkUninterpFun(predicate, std::move(args));
        }();
        chcs.addClause(ChcHead{head},
                       ChcBody{InterpretedFla{system.getTransition()}, {UninterpretedPredicate{notYetSaved}}});
    }
    // query
    {
        PTRef body = [&]() -> PTRef {
            vec<PTRef> args;
            for (PTRef var : system.getStateVars()) {
                args.push(var);
            }
            for (PTRef var : system.getStateVars()) {
                args.push(var);
            }
            args.push(logic.getTerm_true());
            return logic.mkUninterpFun(predicate, std::move(args));
        }();
        chcs.addClause(ChcHead{logic.getTerm_false()},
                       ChcBody{InterpretedFla{logic.getTerm_true()}, {UninterpretedPredicate{body}}});
    }

    // Copied from interpreter. TODO: Refactor!
    Normalizer normalizer(logic);
    auto normalizedSystem = normalizer.normalize(chcs);
    auto hypergraph = ChcGraphBuilder(logic).buildGraph(normalizedSystem);
    assert(hypergraph->isNormalGraph());
    // TODO: preprocessing

    auto engine = EngineFactory(logic, options).getEngine(options.getOrDefault(Options::ENGINE, "spacer"));
    auto res = engine->solve(*hypergraph);
    switch (res.getAnswer()) {
        case VerificationAnswer::SAFE:
            return Answer::NO_LASSO;
        case VerificationAnswer::UNSAFE:
            return Answer::LASSO;
        case VerificationAnswer::UNKNOWN:
            return Answer::UNKNOWN;
    }
    assert(false && "Unreachable!");
    return Answer::ERROR;
}

} // namespace golem::termination
