/*
 * Copyright (c) 2025, Konstantin Britikov <konstantin.britikov@usi.ch>
 *
 * SPDX-License-Identifier: MIT
 */

#include "ReachabilityTerm.h"

#include "TermUtils.h"
#include "../ChcSystem.h"
#include "engine/EngineFactory.h"
#include "graph/ChcGraphBuilder.h"

namespace golem::termination {

ReachabilityTerm::Answer ReachabilityTerm::termination(TransitionSystem const & ts) {
    auto & logic = dynamic_cast<ArithLogic &>(ts.getLogic());
    auto vars = ts.getStateVars();
    uint multiplier = 1;
    // Adding a counter variable
    PTRef counter = logic.mkIntVar("counter");
    PTRef counter0 = TimeMachine(logic).getVarVersionZero(counter);
    PTRef counter1 = TimeMachine(logic).sendVarThroughTime(counter0, 1);
    // initial condition: counter > const * (|x_1| + |x_2| + ... + |x_n|)
    unsigned i = 0;
    PTRef sum = logic.getTerm_IntZero();
    vec<PTRef> sumCheck;
    sumCheck.push(logic.mkGt(counter0, logic.getTerm_IntZero())); // Needed in case there are no int variables
    for (auto var : vars) {
        if (logic.isSortInt(logic.getSortRef(var))) {
            PTRef temp = TimeMachine(logic).getVarVersionZero(logic.mkIntVar(("y" + std::to_string(i)).c_str()));
            // cond = y_i >=0 /\ (y_i = -1 * x_i \/ y_i = x_i)
            sumCheck.push(logic.mkAnd(logic.mkOr(logic.mkEq(temp, var), logic.mkEq(temp, logic.mkNeg(var))), logic.mkGeq(temp, logic.getTerm_IntZero())));
            // sum = sum + y_i
            sum = logic.mkPlus(sum, temp);
            i++;
        }
    }
    vars.push_back(counter0);
    while (true) {
        // counter = multiplier * (y_1 + ... + y_n)
        PTRef countEq = logic.mkEq(counter0, logic.mkTimes(logic.mkIntConst(Number(multiplier)), sum));
        // init = init /\ counter = y_1 + ... + y_n /\ (y_1 = |x_1| /\ ... /\ y_n = |x_n|)
        PTRef init = logic.mkAnd({ts.getInit(), countEq, logic.mkAnd(sumCheck)});
        // transition = transition /\ counter' = counter - 1
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
        multiplier = multiplier * 2;
        switch (res.getAnswer()) {
            case VerificationAnswer::SAFE:
                return Answer::YES;
            case VerificationAnswer::UNKNOWN:
                return Answer::ERROR;
            case VerificationAnswer::UNSAFE:
                continue;
        }
        assert(false && "Unreachable!");
        return Answer::ERROR;
    }
}

} // namespace golem::termination
