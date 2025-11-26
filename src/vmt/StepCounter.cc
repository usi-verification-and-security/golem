/*
 * Copyright (c) 2025, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "StepCounter.h"

#include "TermUtils.h"
#include "engine/EngineFactory.h"
#include "graph/ChcGraphBuilder.h"

namespace golem::vmt {

StepCounter::Answer StepCounter::checkLiveness(TransitionSystem const & ts) {
    auto & logic = dynamic_cast<ArithLogic &>(ts.getLogic());
    auto vars = ts.getStateVars();
    // TODO: Check that liveness constraint does not contain auxiliary variables

    // Adding a counter variable
    PTRef counter = logic.mkIntVar("counter");
    PTRef counter0 = TimeMachine(logic).getVarVersionZero(counter);
    PTRef counter1 = TimeMachine(logic).sendVarThroughTime(counter0, 1);
    // initial condition: counter > max(0, x_1, -x_1, x_2, -x_2, ..., x_n, -x_n)
    vec<PTRef> lowerBounds;
    lowerBounds.push(logic.getTerm_IntZero()); // Needed in case there are no int variables
    for (auto var : vars) {
        if (logic.isSortInt(logic.getSortRef(var))) {
            lowerBounds.push(var);
            lowerBounds.push(logic.mkNeg(var));
        }
    }
    vec<PTRef> lowerConstraints;
    for (PTRef bound : lowerBounds) {
        lowerConstraints.push(logic.mkGt(counter0, bound));
    }
    vars.push_back(counter0);
    PTRef max = logic.mkAnd(std::move(lowerConstraints));
    // init = init /\ counter > max(0, x_1, -x_1, x_2, -x_2, ..., x_n, -x_n)
    PTRef init = logic.mkAnd(ts.getInit(), max);
    PTRef livenessSignal = ts.getQuery();
    // We create two transitions, one when liveness signal is true and one where liveness signal is false
    PTRef counterDec = logic.mkEq(counter1, logic.mkMinus(counter0, logic.getTerm_IntOne()));
    PTRef counterSame = logic.mkEq(counter1, counter0);
    PTRef transitionWithSignalFalse = logic.mkAnd({ts.getTransition(), livenessSignal, counterDec});
    PTRef transitionWithSignalTrue = logic.mkAnd({ts.getTransition(), logic.mkNot(livenessSignal), counterSame});
    // query = counter < 0
    PTRef query = logic.mkLt(counter0, logic.getTerm_IntZero());

    ChcSystem chcs;
    SymRef predicateSymbol = [&]() -> SymRef {
        vec<SRef> argSorts;
        for (PTRef var : vars) {
            argSorts.push(logic.getSortRef(var));
        }
        return logic.declareFun("P", logic.getSort_bool(), std::move(argSorts));
    }();
    chcs.addUninterpretedPredicate(predicateSymbol);

    auto pred = [&]() -> PTRef {
        vec<PTRef> args;
        for (PTRef var : vars) {
            args.push(var);
        }
        return logic.mkUninterpFun(predicateSymbol, std::move(args));
    }();
    auto predNext = [&]() -> PTRef {
        vec<PTRef> args;
        TimeMachine tm(logic);
        for (PTRef var : vars) {
            args.push(tm.sendVarThroughTime(var, 1));
        }
        return logic.mkUninterpFun(predicateSymbol, std::move(args));
    }();
    chcs.addClause(ChcHead{UninterpretedPredicate{pred}}, ChcBody{InterpretedFla{init}, {}});
    chcs.addClause(ChcHead{UninterpretedPredicate{predNext}},
                   ChcBody{InterpretedFla{transitionWithSignalTrue}, {UninterpretedPredicate{pred}}});
    chcs.addClause(ChcHead{UninterpretedPredicate{predNext}},
                   ChcBody{InterpretedFla{transitionWithSignalFalse}, {UninterpretedPredicate{pred}}});
    chcs.addClause(ChcHead{UninterpretedPredicate{logic.getTerm_false()}},
                   ChcBody{InterpretedFla{query}, {UninterpretedPredicate{pred}}});

    Normalizer normalizer(logic);
    auto normalizedSystem = normalizer.normalize(chcs);
    auto hypergraph = ChcGraphBuilder(logic).buildGraph(normalizedSystem);
    assert(hypergraph->isNormalGraph());

    // Solving constructed CHC system
    auto engine = EngineFactory(logic, options).getEngine(options.getOrDefault(Options::ENGINE, "spacer"));

    auto res = engine->solve(*hypergraph);

    switch (res.getAnswer()) {
        case VerificationAnswer::SAFE:
            return Answer::YES;
        case VerificationAnswer::UNKNOWN:
            return Answer::ERROR;
        case VerificationAnswer::UNSAFE:
            return Answer::UNKNOWN;
    }
    assert(false && "Unreachable!");
    return Answer::ERROR;
}

} // namespace golem::vmt
