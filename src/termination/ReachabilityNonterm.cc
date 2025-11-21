/*
 * Copyright (c) 2025, Konstantin Britikov <konstantin.britikov@usi.ch>
 *
 * SPDX-License-Identifier: MIT
 */

#include "ReachabilityNonterm.h"

#include "ChcSystem.h"
#include "ModelBasedProjection.h"
#include "QuantifierElimination.h"
#include "TermUtils.h"
#include "utils/SmtSolver.h"

#include "engine/EngineFactory.h"
#include "graph/ChcGraphBuilder.h"

namespace golem::termination {

std::unique_ptr<ChcDirectedHyperGraph> constructHyperGraph(PTRef const init, PTRef const transition, PTRef const query,
                                                           Logic & logic, std::vector<PTRef> vars) {
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
    return hypergraph;
}

ReachabilityNonterm::Answer ReachabilityNonterm::nontermination(TransitionSystem const & ts) {
    auto vars = ts.getStateVars();
    ArithLogic & logic = dynamic_cast<ArithLogic &>(ts.getLogic());
    PTRef init = ts.getInit();
    PTRef transition = ts.getTransition();
    // In this case query is a set of sink states - states from which transition is not possible.
    // sink /\ transition is UNSAT
    PTRef sink = logic.mkNot(QuantifierElimination(logic).keepOnly(transition, vars));

    // if sink is false, there are no sink states in the TS, therefore it is nonterminating
    if (sink == logic.getTerm_false()) { return Answer::NO; }

    // Witness computation is required, as we need to use both counterexample traces to limit terminating states
    // and inductive invariants to prove nontermination
    Options witnesses = options;
    witnesses.addOption(options.COMPUTE_WITNESS, "true");

    // Main nonterm-checking loop
    while (true) {
        // Constructing a graph based on the currently considered TS
        auto graph = constructHyperGraph(init, transition, sink, logic, vars);
        auto engine = EngineFactory(logic, witnesses).getEngine(witnesses.getOrDefault(Options::ENGINE, "spacer"));

        // Check if sink states are reachable within TS
        auto res = engine->solve(*graph);
        if (res.getAnswer() == VerificationAnswer::UNSAFE) {
            // When sink states are reachable, extract the number of transitions needed to reach the sink states
            uint num = res.getInvalidityWitness().getDerivation().size() - 3;

            // Construct the logical formula representing the trace:
            // Init(x) /\ Tr(x,x') /\ ... /\ Bad(x^(num))
            std::vector formulas{init, TimeMachine(logic).sendFlaThroughTime(sink, num)};
            for (uint j = 0; j < num; j++) {
                formulas.push_back(TimeMachine(logic).sendFlaThroughTime(transition, j));
            }
            PTRef transitions = logic.mkAnd(formulas);

            // Get the satisfying model of the trace.
            // It is needed to detect nondeterminism
            SMTSolver SMTsolver(logic, SMTSolver::WitnessProduction::ONLY_MODEL);
            SMTsolver.assertProp(transitions);
            if (SMTsolver.check() != SMTSolver::Answer::SAT) {
                assert(false);
                return Answer::ERROR;
            }
            auto model = SMTsolver.getModel();

            // Result is a formula, depicting all states reachable in j transitions, which can reach
            // termination in n-j transitions (if j = n it is Termination states)
            PTRef Result = TimeMachine(logic).sendFlaThroughTime(sink, num);

            bool detected = false;
            // Traversing trace from the Bad to Init, detecting the last transition where some variables
            // were assigned nondetermenistically
            for (int j = num; j > 0; j--) {
                vec<PTRef> prev_vars;
                // Constructing vectors of variables x^(j-1) and x^(j)
                for (auto var : vars) {
                    PTRef prev = TimeMachine(logic).sendVarThroughTime(var, j - 1);
                    prev_vars.push(prev);
                }
                // Base is a formula, depicting all states reachable in j-1 transitions, which can reach
                // termination in n-j+1 transitions
                PTRef Base = QuantifierElimination(logic).keepOnly(transitions, prev_vars);
                SMTsolver.resetSolver();
                // Checking if it is possible to reach states which would not lead to termination in n-j states
                // (if j = n) it checks if it is possible to reach nontermination states from trace
                SMTsolver.assertProp(
                    logic.mkAnd({Base, TimeMachine(logic).sendFlaThroughTime(transition, j - 1), logic.mkNot(Result)}));

                // It means that this transition was nondetermenistic, since
                // using transition from the states that guaranteed to reach termination in n-j+1 transitions
                // it is possible to reach states which are not guaranteed to reach termination in n-j transitions
                if (SMTsolver.check() == SMTSolver::Answer::SAT) {
                    // We restrict the nondeterminism that leads to the termination, removing the states
                    // which are guaranteed to terminate in n-j transitions
                    PTRef block = TimeMachine(logic).sendFlaThroughTime(Result, -j + 1);
                    assert(block != logic.getTerm_true());
                    transition = logic.mkAnd(transition, logic.mkNot(block));
                    detected = true;
                    break;
                } else {
                    Result = Base;
                }
            }
            if (!detected) {
                // If all transitions were determenistic, we block the initial states that lead to the termination
                init = logic.mkAnd(init, logic.mkNot(Result));
            }

        } else if (res.getAnswer() == VerificationAnswer::SAFE) {
            // In case if sink states are not reachable, we need to construct the inductive invariant and demonstrate
            // that it doesn't contain any sink states itself.
            // It is possible since we add constraints to the transition relation, which were not accounted for
            // initially.
            auto witness = res.getValidityWitness();
            assert(witness.getDefinitions().size() == 3);
            PTRef inv;
            std::vector<PTRef> repr;
            // First, we extract the invariant from the witness. It is interpretation of predicate P.
            for (auto wtn : witness.getDefinitions()) {
                if (wtn.first.x != 3 && wtn.first.x != 0) {
                    repr = graph->predicateRepresentation().getRepresentation(wtn.first);
                    inv = wtn.second;
                }
            }
            TermUtils::substitutions_map varSubstitutions;
            for (uint32_t i = 0u; i < vars.size(); ++i) {
                varSubstitutions.insert({repr[i], vars[i]});
            }
            // Then invariant is translated, so the variables correspond to the encoding of the CHC system,
            // pre-normalization
            inv = TermUtils(logic).varSubstitute(inv, varSubstitutions);

            SMTSolver SMTsolver(logic, SMTSolver::WitnessProduction::NONE);
            SMTsolver.assertProp(logic.mkAnd(init, transition));
            // We check if init state is blocked (it's impossible to make a transition from initial state)
            // When it is the case, TS is terminating
            if (SMTsolver.check() == SMTSolver::Answer::UNSAT) {
                return Answer::YES;
            } else {
                SMTsolver.resetSolver();
                SMTsolver.assertProp(
                    logic.mkAnd({inv, transition, logic.mkNot(TimeMachine(logic).sendFlaThroughTime(inv, 1))}));
                assert(SMTsolver.check() == SMTSolver::Answer::UNSAT);
                PTRef constr = logic.mkNot(QuantifierElimination(logic).keepOnly(transition, vars));
                SMTsolver.resetSolver();
                SMTsolver.assertProp(logic.mkAnd({inv, constr}));
                // We check if from any state satisfying the invariant it is possible to take a transition.
                // For this we check the reverse, if there exists a state satisfying Inv, from which it is impossible
                // to take a transition:
                // Exists x. Inv(x) /\ Does not (Exist x'.  Tr(x,x')) - right conjunct is QE-ed
                // Meaning there exists a state satisfying an invariant, such that there does not exist a SAT transition
                // from this state If it is the case, there exist a sink state in the invariant - otherwise, invariant
                // is a recurrent set
                if (SMTsolver.check() == SMTSolver::Answer::UNSAT) {
                    // std::cout<<"Final check:" << logic.pp(logic.mkAnd({inv, constr})) << "\n";
                    return Answer::NO;
                } else {
                    // We update the sink states by the detected sink states and rerun the verification
                    sink = constr;
                }
            }
        } else {
            assert(false && "Unreachable!");
            return Answer::ERROR;
        }
    }

    assert(false && "Unreachable!");
    return Answer::ERROR;
}

} // namespace golem::termination