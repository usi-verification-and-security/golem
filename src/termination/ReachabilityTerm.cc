/*
 * Copyright (c) 2025, Konstantin Britikov <konstantin.britikov@usi.ch>
 *
 * SPDX-License-Identifier: MIT
 */

#include "ReachabilityTerm.h"

#include "ChcSystem.h"
#include "Normalizer.h"
#include "TermUtils.h"
#include "engine/EngineFactory.h"
#include "graph/ChcGraphBuilder.h"

namespace golem::termination {
ReachabilityTerm::Answer ReachabilityTerm::nontermination(ChcDirectedHyperGraph const & system) {
    ArithLogic & logic = dynamic_cast<ArithLogic &>(system.getLogic());
    // ChcSystem chcs;
    // // Creating predicate P(x) for TS
    // SymRef predicate = [&]() -> SymRef {
    //     vec<SRef> argSorts;
    //     for (PTRef var : system.getStateVars()) {
    //         argSorts.push(logic.getSortRef(var));
    //     }
    //     return logic.declareFun("L", logic.getSort_bool(), std::move(argSorts));
    // }();
    // chcs.addUninterpretedPredicate(predicate);
    //
    // // Add transition relation
    // {
    //     PTRef body = [&]() -> PTRef {
    //         vec<PTRef> args;
    //         for (PTRef var : system.getStateVars()) {
    //             args.push(var);
    //         }
    //         return logic.mkUninterpFun(predicate, std::move(args));
    //     }();
    //     PTRef head = [&]() -> PTRef {
    //         vec<PTRef> args;
    //         for (PTRef var : system.getNextStateVars()) {
    //             args.push(var);
    //         }
    //         return logic.mkUninterpFun(predicate, std::move(args));
    //     }();
    //     chcs.addClause(ChcHead{UninterpretedPredicate{head}},
    //                    ChcBody{InterpretedFla{system.getTransition()}, {UninterpretedPredicate{body}}});
    // }
    //
    // // Add query
    // {
    //     PTRef body = [&]() -> PTRef {
    //         vec<PTRef> args;
    //         for (PTRef var : system.getStateVars()) {
    //             args.push(var);
    //         }
    //         return logic.mkUninterpFun(predicate, std::move(args));
    //     }();
    //     chcs.addClause(ChcHead{logic.getTerm_false()},
    //                    ChcBody{InterpretedFla{logic.getTerm_true()}, {UninterpretedPredicate{body}}});
    // }
    //
    // // Add initial clause
    // {
    //     auto initial = [&]() -> PTRef {
    //         vec<PTRef> args;
    //         for (PTRef var : system.getStateVars()) {
    //             args.push(var);
    //         }
    //         return logic.mkUninterpFun(predicate, std::move(args));
    //     }();
    //     chcs.addClause(ChcHead{UninterpretedPredicate{initial}},
    //         ChcBody{InterpretedFla{system.getInit()}, {}});
    // }

    // Normalizer normalizer(logic);
    // auto normalizedSystem = normalizer.normalize(chcs);
    // auto hypergraph = ChcGraphBuilder(logic).buildGraph(normalizedSystem);
    // assert(hypergraph->isNormalGraph());
    // TODO: preprocessing
    auto engine = EngineFactory(logic, options).getEngine(options.getOrDefault(Options::ENGINE, "spacer"));
    if (std::stoi(options.getOrDefault(Options::VERBOSE, "0")) > 0) { std::cout << "; Searching for nontermination!\n"; }
    auto res = engine->solve(system);
    while(res.getAnswer() == VerificationAnswer::UNSAFE) {
        engine.
        auto witness = res.getInvalidityWitness();
        // auto format = opts.getOrDefault(Options::PROOF_FORMAT, "legacy");
        // result.printWitness(std::cout, logic, hypergraph, originalAssertions, normalizingEqualities, format);
        auto deriv = witness.getDerivation();
    }

    switch (res.getAnswer()) {
        case VerificationAnswer::SAFE:
            return Answer::NO;
        case VerificationAnswer::UNKNOWN:
            return Answer::UNKNOWN;
    }
    assert(false && "Unreachable!");
    return Answer::ERROR;
}

} // namespace golem::termination
