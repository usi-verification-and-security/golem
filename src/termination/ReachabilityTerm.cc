/*
 * Copyright (c) 2025, Konstantin Britikov <konstantin.britikov@usi.ch>
 *
 * SPDX-License-Identifier: MIT
 */

#include "ReachabilityTerm.h"

#include "TermUtils.h"
#include "engine/EngineFactory.h"
#include "graph/ChcGraphBuilder.h"

namespace golem::termination {

ReachabilityTerm::Answer ReachabilityTerm::termination(TransitionSystem const & ts) {
    auto & logic = dynamic_cast<ArithLogic &>(ts.getLogic());
    auto vars = ts.getStateVars();

    // Adding a counter variable
    PTRef counter = logic.mkIntVar("counter");
    PTRef counter0 = TimeMachine(logic).getVarVersionZero(counter);
    PTRef counter1 = TimeMachine(logic).sendVarThroughTime(counter0, 1);
    // initial condition: counter > max(0, x_1, -x_1, x_2, -x_2, ..., x_n, -x_n)
    vec<PTRef> geqCheck;
    geqCheck.push(logic.mkGt(counter0, logic.getTerm_IntZero())); // Needed in case there are no int variables
    for (auto var : vars) {
        if (logic.isSortInt(logic.getSortRef(var))) {
            geqCheck.push(logic.mkGt(counter0, var));
            geqCheck.push(logic.mkGt(counter0, logic.mkNeg(var)));
        }
    }
    vars.push_back(counter0);
    PTRef max = logic.mkAnd(geqCheck);
    // init = init /\ counter > max(0, x_1, -x_1, x_2, -x_2, ..., x_n, -x_n)
    PTRef init = logic.mkAnd(ts.getInit(), max);
    // transition = transition /\ counter' = counter -1
    PTRef counterDec = logic.mkEq(counter1, logic.mkMinus(counter0, logic.getTerm_IntOne()));
    PTRef transition = logic.mkAnd(ts.getTransition(), counterDec);
    // query = counter < 0
    PTRef query = logic.mkLt(counter0, logic.getTerm_IntZero());

    ChcSystem chcs;
    // Adding an uninterpreted predicate P
    SymRef predicate = [&]() -> SymRef {
        vec<SRef> argSorts;
        for (PTRef var : vars) {
            argSorts.push(logic.getSortRef(var));
        }
        return logic.declareFun("P", logic.getSort_bool(), std::move(argSorts));
    }();
    chcs.addUninterpretedPredicate(predicate);

    // creating P(x_1, x_2, ..., x_n)
    auto pred = [&]() -> PTRef {
        vec<PTRef> args;
        for (PTRef var : vars) {
            args.push(var);
        }
        return logic.mkUninterpFun(predicate, std::move(args));
    }();
    // creating P(x_1', x_2', ..., x_n')
    auto pred_next = [&]() -> PTRef {
        vec<PTRef> args;
        TimeMachine tm(logic);
        for (PTRef var : vars) {
            args.push(tm.sendVarThroughTime(var, 1));
        }
        return logic.mkUninterpFun(predicate, std::move(args));
    }();
    chcs.addClause(ChcHead{UninterpretedPredicate{pred}}, ChcBody{InterpretedFla{init}, {}});
    chcs.addClause(ChcHead{UninterpretedPredicate{pred_next}},
                   ChcBody{InterpretedFla{transition}, {UninterpretedPredicate{pred}}});
    chcs.addClause(ChcHead{UninterpretedPredicate{logic.getTerm_false()}},
                   ChcBody{InterpretedFla{query}, {UninterpretedPredicate{pred}}});

    Normalizer normalizer(logic);
    auto normalizedSystem = normalizer.normalize(chcs);
    auto hypergraph = ChcGraphBuilder(logic).buildGraph(normalizedSystem);
    assert(hypergraph->isNormalGraph());

    // Solving constructed CHC system
    auto engine = EngineFactory(logic, options).getEngine(options.getOrDefault(Options::ENGINE, "spacer"));

    if (std::stoi(options.getOrDefault(Options::VERBOSE, "0")) > 0) {
        std::cout << "; Searching for nontermination!\n";
    }
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

} // namespace golem::termination
