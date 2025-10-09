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
    // Preprocessing of TS
    ArithLogic & logic = dynamic_cast<ArithLogic &>(ts.getLogic());
    auto vars = ts.getStateVars();
    vec<PTRef> eqCheck;
    vec<PTRef> geqCheck;

    if (ts.getTransition() == logic.getTerm_true() || ts.getInit() == logic.getTerm_false()) {
        return Answer::UNKNOWN;
    }
    // Adding a counter variable
    PTRef counter = logic.mkIntVar("counter");
    PTRef counter0 = TimeMachine(logic).getVarVersionZero(counter);
    PTRef counter1 = TimeMachine(logic).sendVarThroughTime(counter0, 1);
    for (auto var : vars) {
        if (logic.isSortInt(logic.getSortRef(var)) || logic.isSortReal(logic.getSortRef(var))) {
            eqCheck.push(logic.mkEq(var, counter0));
            eqCheck.push(logic.mkEq(logic.mkNeg(var), counter0));
            geqCheck.push(logic.mkGeq(counter0, var));
            geqCheck.push(logic.mkGeq(counter0, logic.mkNeg(var)));
        }
    }
    vars.push_back(counter0);
    // Creating a formula counter = max(x_1, -x_1, x_2, -x_2, ..., x_n, -x_n) - counter should be a positive max value
    // of a variable
    PTRef max = logic.mkAnd(logic.mkOr(eqCheck), logic.mkAnd(geqCheck));
    // This is a formula that decrements counter by one
    PTRef counterDec = logic.mkEq(counter1, logic.mkMinus(counter0, logic.getTerm_IntOne()));

    // init = init /\ counter = max(x_1, -x_1, x_2, -x_2, ..., x_n, -x_n)
    PTRef init = logic.mkAnd(ts.getInit(), max);
    // transition = transition /\ counter' = counter -1
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
    // adding clauses to CHC system
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
