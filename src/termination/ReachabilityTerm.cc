/*
 * Copyright (c) 2025, Konstantin Britikov <konstantin.britikov@usi.ch>
 *
 * SPDX-License-Identifier: MIT
 */

#include "ReachabilityTerm.h"

#include "ChcSystem.h"
#include "TermUtils.h"
#include "engine/EngineFactory.h"
#include "engine/TPA.h"
#include "engine/Common.h"
#include "TransformationUtils.h"
#include "transformers/SingleLoopTransformation.h"
#include "ModelBasedProjection.h"
#include "QuantifierElimination.h"

namespace golem::termination {

    PTRef eliminateVars(PTRef fla, const vec<PTRef> & vars, Model & model, bool useQE, Logic logic) {
        if (useQE) {
            return QuantifierElimination(logic).eliminate(fla, vars);
        } else {
            return ModelBasedProjection(logic).project(fla, vars, model);
        }
    }

    // TODO: think what to do with negation
    PTRef dnfize(PTRef input, Logic & logic) {
        TermUtils utils {logic};
        if (logic.isAnd(input)) {
            auto juncts = utils.getTopLevelConjuncts(input);

            for (int i = 0; i < (int)juncts.size(); i++) {
                PTRef after_junct = dnfize(juncts[i], logic);
                if (logic.isOr(after_junct)) {
                    auto subjuncts = utils.getTopLevelDisjuncts(after_junct);
                    vec<PTRef> postprocessJuncts;
                    juncts[i] = juncts.last();
                    juncts.pop();
                    for (auto subjunct: subjuncts) {
                        postprocessJuncts.push(logic.mkAnd(logic.mkAnd(juncts), subjunct));
                    }
                    return dnfize(logic.mkOr(postprocessJuncts), logic);
                }
            }
        } else if (logic.isOr(input)) {
            auto juncts = utils.getTopLevelDisjuncts(input);
            vec<PTRef> postprocessJuncts;
            for (int i = 0; i < (int)juncts.size(); i++) {
                PTRef after_junct = dnfize(juncts[i], logic);
                if (logic.isOr(after_junct)) {
                    auto subjuncts = utils.getTopLevelDisjuncts(after_junct);
                    for (auto subjunct: subjuncts) {
                        postprocessJuncts.push(subjunct);
                    }
                } else {
                    postprocessJuncts.push(after_junct);
                }
            }
            return logic.mkOr(postprocessJuncts);
        } else if (logic.isNot(input)) {
            PTRef rev = logic.mkNot(input);
            if (logic.isAnd(rev)) {
                auto subjuncts = utils.getTopLevelConjuncts(rev);
                vec<PTRef> postprocessJuncts;
                for (int i = 0; i < (int)subjuncts.size(); i++) {
                    postprocessJuncts.push(logic.mkNot(subjuncts[i]));
                }
                return dnfize(logic.mkOr(postprocessJuncts), logic);
            } else if (logic.isOr(rev)) {
                auto subjuncts = utils.getTopLevelDisjuncts(input);
                vec<PTRef> postprocessJuncts;
                for (int i = 0; i < (int)subjuncts.size(); i++) {
                    postprocessJuncts.push(logic.mkNot(subjuncts[i]));
                }
                return dnfize(logic.mkAnd(postprocessJuncts), logic);
            }
        }
        return input;
    }


ReachabilityTerm::Answer ReachabilityTerm::nontermination(ChcDirectedGraph const & graph) {
    ArithLogic & logic = dynamic_cast<ArithLogic &>(graph.getLogic());
    TermUtils utils {logic};
    if (isTrivial(graph)) { return Answer::YES; }
    auto ts = [&]() -> std::unique_ptr<TransitionSystem> {
        if (isTransitionSystem(graph)) { return toTransitionSystem(graph, false); }
        auto [ts, bt] = SingleLoopTransformation{}.transform(graph);
        return std::move(ts);
    }();
    auto solver = std::make_unique<TPASplit>(logic, options);

    auto vars = ts->getStateVars();
    vec<PTRef> postprocVars1;
    vec<PTRef> postprocVars2;
    PTRef counter = logic.mkIntVar("counter");
    PTRef counter0 = TimeMachine(logic).getVarVersionZero(counter);
    PTRef counter1 = TimeMachine(logic).sendVarThroughTime(counter0,1);
    for (auto var: vars) {
        if (logic.isSortInt(logic.getSortRef(var)) || logic.isSortReal(logic.getSortRef(var))) {
            postprocVars1.push(logic.mkEq(var,counter0));
            postprocVars2.push(logic.mkGeq(counter0, var));
            postprocVars2.push(logic.mkGeq(counter0, logic.mkNeg(var)));
        }
    }
    vars.push_back(counter0);
    PTRef addInit = logic.mkAnd(logic.mkOr(postprocVars1), logic.mkAnd(postprocVars2));
    // std::cout<<"postProc1: " << logic.pp(logic.mkOr(postprocVars1)) << std::endl;
    // std::cout<<"postProc2: " << logic.pp(logic.mkAnd(postprocVars2)) << std::endl;
    // std::cout<<"addInit: " << logic.pp(addInit) << std::endl;
    PTRef init  = logic.mkAnd(ts->getInit(), addInit);
    PTRef counterDec = logic.mkEq(counter1, logic.mkMinus(counter0, logic.getTerm_IntOne()));
    PTRef transition = dnfize(logic.mkAnd(ts->getTransition(), counterDec),logic);
    PTRef query = logic.mkGeq(counter0, logic.getTerm_IntZero());
    solver->resetTransitionSystem(TransitionSystem(logic,
                    std::make_unique<SystemType>(vars, ts->getAuxiliaryVars(), logic),
                    init,
                        transition,
                        query));
    // std::cout<<"Init: " << logic.pp(init) << std::endl;
    // std::cout<<"Transition: " << logic.pp(transition) << std::endl;
    // std::cout<<"Query: " << logic.pp(query) << std::endl;

    if (std::stoi(options.getOrDefault(Options::VERBOSE, "0")) > 0) { std::cout << "; Searching for nontermination!\n"; }
    auto res = solver->solve();

    switch (res) {
        case VerificationAnswer::SAFE:
            return Answer::YES;
        case VerificationAnswer::UNKNOWN:
            return Answer::ERROR;
        case VerificationAnswer::UNSAFE:
            return Answer::UNKNOWN;
    }
}

} // namespace golem::termination
