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

// Function to eliminate negations, replacing "not (a = b)" with "a < b \/ a > b"
PTRef normalize(PTRef input, ArithLogic & logic, bool negated = false) {
    assert(logic.isNot(input) || logic.isAnd(input) || logic.isOr(input) || logic.isNumEq(input) || logic.isLeq(input));
    if (logic.isAnd(input) || logic.isOr(input)) {
        // Check every junct
        auto juncts = logic.isAnd(input) ? TermUtils(logic).getTopLevelConjuncts(input)
                                         : TermUtils(logic).getTopLevelDisjuncts(input);
        vec<PTRef> subjuncts;
        for (auto junct : juncts) {
            subjuncts.push(normalize(junct, logic, negated));
        }
        if (logic.isAnd(input)) return negated ? logic.mkOr(subjuncts) : logic.mkAnd(subjuncts);
        if (logic.isOr(input)) return negated ? logic.mkAnd(subjuncts) : logic.mkOr(subjuncts);
        assert(false);
    }

    auto it = logic.getPterm(input).begin();
    if (logic.isNot(input)) { return normalize(it[0], logic, !negated); }
    if (negated && logic.isNumEq(input)) {
        // x != y <=> x <= y-1 \/  y+1 <= x
        PTRef geq = logic.mkLeq(logic.mkPlus(it[1], logic.getTerm_IntOne()), it[0]);
        PTRef leq = logic.mkLeq(it[0], logic.mkPlus(it[1], logic.getTerm_IntMinusOne()));
        return logic.mkOr(geq, leq);
    }
    if (negated && logic.isLeq(input)) {
        // !(x <= y) <=> y+1 <= x
        return logic.mkLeq(logic.mkPlus(it[1], logic.getTerm_IntOne()), it[0]);
    }

    return negated ? logic.mkNot(input) : input;
}

// This function is needed to extract specific atoms from the arithmetic formula
void extractTerms(ArithLogic & logic, std::vector<PTRef> & terms, PTRef formula) {
    assert(logic.isVar(formula) || logic.isTimes(formula) || logic.isPlus(formula));
    if (logic.isPlus(formula)) {
        Pterm const & term = logic.getPterm(formula);
        terms.insert(terms.end(), term.begin(), term.end());
    } else {
        terms.push_back(formula);
    }
}

// Builds: for every column j, sum_i weights[i] * matrix[i][j] == 0
PTRef mkZeroDotProductEqs(ArithLogic & logic, vec<PTRef> const & weights,
                          std::vector<std::vector<PTRef>> const & matrix, int numCols) {
    vec<PTRef> eqs;
    for (int j = 0; j < numCols; ++j) {
        vec<PTRef> mults;
        for (int i = 0; i < weights.size(); ++i) {
            mults.push(logic.mkTimes(weights[i], matrix[i][j]));
        }
        eqs.push(logic.mkEq(logic.mkPlus(mults), logic.getTerm_IntZero()));
    }
    return logic.mkAnd(eqs);
}

bool checkWellFounded(PTRef const formula, ArithLogic & logic, vec<PTRef> const & vars) {
    assert(logic.isAnd(formula) || logic.isLeq(formula) || logic.isEquality(formula));
    vec<PTRef> conjuncts = TermUtils(logic).getTopLevelConjuncts(formula);

    vec<PTRef> int_vars;
    vec<PTRef> next_int_vars;
    // Extract integer variables from the inequalities
    for (auto var : vars) {
        if (logic.isNumVar(var)) {
            int_vars.push(var);
            next_int_vars.push(TimeMachine(logic).sendVarThroughTime(var, 1));
        }
    }

    // TODO: Think about boolean w-f
    vec<PTRef> leq_conjuncts;
    for (auto conj : conjuncts) {
        if (logic.isLeq(conj))
            leq_conjuncts.push(conj);
        else if (logic.isNumEq(conj)) {
            auto it = logic.getPterm(conj).begin();
            // x == y <=> y <= x /\ x <= y
            leq_conjuncts.push(logic.mkLeq(it[0], it[1]));
            leq_conjuncts.push(logic.mkLeq(it[1], it[0]));
        } else {
            assert(false);
        }
    }

    SMTSolver solver(logic, SMTSolver::WitnessProduction::NONE);

    // Equality check (x = x') - should be UNSAT for termination
    vec<PTRef> eq_vars;
    for (auto var : vars) {
        PTRef curr = TimeMachine(logic).sendVarThroughTime(var, 0);
        PTRef next = TimeMachine(logic).sendVarThroughTime(var, 1);
        eq_vars.push(logic.mkEq(curr, next));
    }
    solver.assertProp(logic.mkAnd(formula, logic.mkAnd(eq_vars)));
    if (solver.check() == SMTSolver::Answer::SAT) return false;

    // If two transitions in a row are UNSAT, formula is well-founded
    solver.resetSolver();
    solver.assertProp(logic.mkAnd(formula, TimeMachine(logic).sendFlaThroughTime(formula, 1)));
    if (solver.check() == SMTSolver::Answer::UNSAT) return true;

    std::vector<std::vector<PTRef>> A;
    std::vector<std::vector<PTRef>> A_p;
    std::vector<PTRef> b = std::vector<PTRef>(leq_conjuncts.size(), logic.getTerm_IntZero());
    // Computation of matrices A, A_p, and vector b based on the coefficients of vars and constants
    for (auto conjunct : leq_conjuncts) {
        A.push_back(std::vector(int_vars.size(), logic.getTerm_IntZero()));
        A_p.push_back(std::vector(int_vars.size(), logic.getTerm_IntZero()));
        std::vector<PTRef> terms;
        // Extracting coefficients of the variables from the inequality
        // Formula is expected to be of form c <= a_1 * x_1 + ... + a_n * x_n.
        assert(logic.isLeq(conjunct));
        auto it = logic.getPterm(conjunct).begin();
        assert(logic.getPterm(conjunct).size() == 2);
        assert(logic.isConstant(it[0]));
        b[A.size() - 1] = logic.mkNeg(it[0]);
        extractTerms(logic, terms, it[1]);

        // Connecting coefficients to specific variables
        // Since the formula is "c <= ....", the coefficients
        // on the variables need to be negated
        for (size_t i = 0; i < terms.size(); i++) {
            assert(logic.isVar(terms[i]) || logic.isTimes(terms[i]));
            PTRef constant, subatom;
            if (logic.isVar(terms[i])) {
                constant = logic.getTerm_IntMinusOne();
                subatom = terms[i];
            } else {
                auto it = logic.getPterm(terms[i]).begin();
                assert(logic.isTimes(terms[i]));
                if (logic.isConstant(it[0])) {
                    constant = logic.mkNeg(it[0]);
                    subatom = it[1];
                } else {
                    constant = logic.mkNeg(it[1]);
                    subatom = it[0];
                }
            }

            assert(logic.isConstant(constant));
            for (int j = 0; j < int_vars.size(); j++) {
                if (subatom == int_vars[j]) {
                    A[A.size() - 1][j] = constant;
                    break;
                }
                if (subatom == next_int_vars[j]) {
                    A_p[A_p.size() - 1][j] = constant;
                    break;
                }
            }
        }
    }

    // Well-foundness check by Podelski - by synthesizing the ranking function
    vec<PTRef> lambda_1, lambda_2;
    for (size_t i = 0; i < A.size(); i++) {
        lambda_1.push(logic.mkIntVar(("lambda_1" + std::to_string(i)).c_str()));
        lambda_2.push(logic.mkIntVar(("lambda_2" + std::to_string(i)).c_str()));
    }

    // 0. Constraint on lambdas:
    PTRef ZeroIneq;
    {
        vec<PTRef> ineqs;
        for (auto i = 0; i < lambda_1.size(); ++i) {
            ineqs.push(logic.mkGeq(lambda_1[i], logic.getTerm_IntZero()));
            ineqs.push(logic.mkGeq(lambda_2[i], logic.getTerm_IntZero()));
        }
        ZeroIneq = logic.mkAnd(ineqs);
    }

    // 1. lambda_1 * A_p = 0:
    PTRef firstEq = mkZeroDotProductEqs(logic, lambda_1, A_p, int_vars.size());

    // 2. (lambda_1 - lambda_2) * A = 0
    vec<PTRef> minuses(lambda_1.size());
    for (auto i = 0; i < lambda_1.size(); i++) {
        minuses[i] = logic.mkMinus(lambda_1[i], lambda_2[i]);
    }
    PTRef secondEq = mkZeroDotProductEqs(logic, minuses, A, int_vars.size());

    // 3. lambda_2 * (A + A_p) = 0
    std::vector<std::vector<PTRef>> sumM;
    for (size_t i = 0; i < A.size(); i++) {
        sumM.push_back(std::vector(int_vars.size(), logic.getTerm_IntZero()));
        for (int j = 0; j < int_vars.size(); j++) {
            sumM[i][j] = logic.mkPlus(A[i][j], A_p[i][j]);
        }
    }
    PTRef thirdEq = mkZeroDotProductEqs(logic, lambda_2, sumM, int_vars.size());

    // 4. lambda_2 * b < 0
    PTRef constCheck;
    {
        vec<PTRef> sums;
        for (auto j = 0; j < lambda_2.size(); j++) {
            PTRef mult = logic.mkTimes(lambda_2[j], b[j]);
            sums.push(mult);
        }

        constCheck = logic.mkLt(logic.mkPlus(sums), logic.getTerm_IntZero());
    }

    // Final check:
    PTRef finalCheck = logic.mkAnd({ZeroIneq, firstEq, secondEq, thirdEq, constCheck});
    solver.resetSolver();
    solver.assertProp(finalCheck);
    return solver.check() == SMTSolver::Answer::SAT;
}

// Function is needed to construct CHC system out of TS
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

// This function takes transition relation formula Tr(x,x') and shifts next Vars, making it Tr(x,x'')
PTRef shiftOnlyNextVars(PTRef formula, const std::vector<PTRef> & vars, Logic & logic) {
    TermUtils::substitutions_map varSubstitutions;
    for (auto var : vars) {
        varSubstitutions.insert(
            {TimeMachine(logic).sendVarThroughTime(var, 1), TimeMachine(logic).sendVarThroughTime(var, 2)});
    }
    return TermUtils(logic).varSubstitute(formula, varSubstitutions);
}

// This function takes a SAT formula, and based on the model of the formula it extracts
// literals that are assigned to T via given model.
void extractActiveLiterals(PTRef formula, Logic & logic, Model & model, vec<PTRef> & activeLiterals, SMTSolver & solver,
                           bool reverse = false) {
    PTRef value = model.evaluate(formula);
    if ((value == logic.getTerm_false() && reverse == false) || (value == logic.getTerm_true() && reverse == true)) {
        return;
    }

    if (logic.isAnd(formula) || logic.isOr(formula)) {
        // Check every conjunct
        Pterm const & terms = logic.getPterm(formula);
        for (int i = 0; i < terms.size(); i++) {
            extractActiveLiterals(terms[i], logic, model, activeLiterals, solver, reverse);
        }
    } else if (logic.isNot(formula)) {
        extractActiveLiterals(TermUtils(logic).simplifyMax(logic.mkNot(formula)), logic, model, activeLiterals, solver,
                              !reverse);
    } else {
        activeLiterals.push(reverse ? logic.mkNot(formula) : formula);
    }
}

// Converts formula into disjunctive normal form
// bound sets a maximal number of disjuncts in DNF if bound != 0
PTRef toDNF(PTRef formula, Logic & logic, int bound = 0) {
    vec<PTRef> DNF;
    bool unlimited = bound == 0;
    SMTSolver smt_solver(logic, SMTSolver::WitnessProduction::ONLY_MODEL);
    smt_solver.assertProp(formula);
    // Loop extracts single SAT assignment, blocks satisfied literals and reruns check
    while (smt_solver.check() == SMTSolver::Answer::SAT && (unlimited || bound > 0)) {
        vec<PTRef> activeLiterals;
        auto model = smt_solver.getModel();
        extractActiveLiterals(formula, logic, *model, activeLiterals, smt_solver);
        PTRef cube = logic.mkAnd(activeLiterals);
        DNF.push(cube);
        smt_solver.push();
        smt_solver.assertProp(logic.mkNot(cube));
        bound--;
    }
    return logic.mkOr(DNF);
}

// This function extracts well-founded disjuncts from the interpolant
vec<PTRef> extractWellFoundedCandidates(PTRef itp, PTRef sink, ArithLogic & logic, const std::vector<PTRef> & vars) {
    TermUtils utils(logic);
    SMTSolver smt_solver(logic, SMTSolver::WitnessProduction::NONE);

    auto sink_disjuncts =
        utils.getTopLevelDisjuncts(toDNF(utils.simplifyMax(normalize(logic.mkNot(sink), logic)), logic));
    auto candidates = utils.getTopLevelDisjuncts(toDNF(utils.simplifyMax(normalize(itp, logic)), logic, 500));
    vec<PTRef> strictCandidates;
    for (auto cand : candidates) {
        assert(cand != logic.getTerm_true());
        if (checkWellFounded(cand, logic, vars)) {
            strictCandidates.push(cand);
        } else {
            for (auto sink_cand : sink_disjuncts) {
                PTRef conjunction = utils.simplifyMax(logic.mkAnd(sink_cand, cand));
                smt_solver.resetSolver();
                smt_solver.assertProp(conjunction);
                if (smt_solver.check() == SMTSolver::Answer::SAT && checkWellFounded(conjunction, logic, vars)) {
                    strictCandidates.push(conjunction);
                }
            }
        }
    }
    return strictCandidates;
}

// Function evaluates if Tr(x,x') determenistic
bool determinismCheck(const PTRef & transition, Logic & logic, const std::vector<PTRef> & vars) {
    SMTSolver detChecker(logic, SMTSolver::WitnessProduction::NONE);
    TermUtils::substitutions_map detSubstitutions;
    vec<PTRef> neq;
    // Constructing x' != x''
    for (uint32_t i = 0u; i < vars.size(); ++i) {
        PTRef next = TimeMachine(logic).sendVarThroughTime(vars[i], 1);
        PTRef nextNext = TimeMachine(logic).sendVarThroughTime(vars[i], 2);
        detSubstitutions.insert({next, nextNext});
        neq.push(logic.mkNot(logic.mkEq(next, nextNext)));
    }
    PTRef newTransition = TermUtils(logic).varSubstitute(transition, detSubstitutions);
    // Tr(x,x') /\ Tr(x, x'') /\ ! x' = x''
    detChecker.assertProp(logic.mkAnd({transition, newTransition, logic.mkOr(neq)}));

    return detChecker.check() == SMTSolver::Answer::UNSAT;
}

// Function constructs Id relation, Id(x,x') = (x'=x)
PTRef getId(const std::vector<PTRef> & vars, Logic & logic) {
    // Start buiding the trace that reaches sink states
    vec<PTRef> eq_vars(vars.size());
    for (auto var : vars) {
        PTRef curr = TimeMachine(logic).sendVarThroughTime(var, 0);
        PTRef next = TimeMachine(logic).sendVarThroughTime(var, 1);
        eq_vars.push(logic.mkEq(curr, next));
    }
    return logic.mkAnd(eq_vars);
}

PTRef constructTransitionInvariantCandidates(PTRef init, PTRef transition, PTRef sink, int depth, Logic & logic,
                                             const std::vector<PTRef> & vars) {
    PTRef id = getId(vars, logic);
    PTRef transitionOrId = logic.mkOr(transition, id);
    std::vector deterministic_trace{transition};
    for (int k = 1; k < depth; k++) {
        // For every transition deterministic trace is updated, adding an Id or Tr
        // This is needed so that Interpolant overapproximates 1 <= n <= num transitions
        deterministic_trace.push_back(TimeMachine(logic).sendFlaThroughTime(transitionOrId, k));
    }
    PTRef trace = logic.mkAnd(deterministic_trace);

    // States guaranteed to reach termination: Sink at exactly `depth` steps, plus (if depth > 1)
    // states reachable from `init` within 1..depth-1 steps that already satisfy the trace.
    std::vector<PTRef> checked_states;
    if (depth > 1) {
        vec<PTRef> temp_vars;
        for (auto var : vars) {
            temp_vars.push(TimeMachine(logic).sendVarThroughTime(var, depth - 1));
        }
        checked_states.push_back(TimeMachine(logic).sendFlaThroughTime(
            QuantifierElimination(logic).keepOnly(logic.mkAnd(init, trace), temp_vars), 1));
    }
    checked_states.push_back(TimeMachine(logic).sendFlaThroughTime(sink, depth));
    // sink is updated, representing states that are guaranteed to reach termination
    PTRef terminating_states = logic.mkOr(checked_states);

    // Itp(Tr /\ ... /\ Tr, Init /\ not TerminatingStates) should be UNSAT: by construction,
    // `terminating_states` already covers everything reachable from `init` via the trace.
    SMTSolver smt_solver(logic, SMTSolver::WitnessProduction::ONLY_INTERPOLANTS);
    smt_solver.getConfig().setSimplifyInterpolant(4);
    smt_solver.assertProp(trace);
    smt_solver.push();
    smt_solver.assertProp(logic.mkAnd(init, logic.mkNot(terminating_states)));
    if (smt_solver.check() != SMTSolver::Answer::UNSAT) {
        assert(false);
        return logic.getTerm_false();
    }

    auto itpContext = smt_solver.getInterpolationContext();
    vec<PTRef> itps;
    ipartitions_t mask = 1;
    itpContext->getSingleInterpolant(itps, mask);
    assert(itps.size() == 1);
    // Extracting Itp(Tr /\ ... /\ Tr, Init /\ not Sink) - overapproximation of 1 <= n <= num
    // transitions
    PTRef itp = itps[0];

    TermUtils::substitutions_map varSubstitutions;
    for (uint32_t i = 0u; i < vars.size(); ++i) {
        varSubstitutions.insert(
            {TimeMachine(logic).sendVarThroughTime(vars[i], depth), TimeMachine(logic).sendVarThroughTime(vars[i], 1)});
    }
    // Then interpolant is translated, so it would correspond to transition relation Itp(x,x')
    return TermUtils(logic).varSubstitute(itp, varSubstitutions);
}

std::tuple<ReachabilityNonterm::Answer, PTRef> ReachabilityNonterm::analyzeTS(PTRef init, PTRef transition, PTRef sink,
                                                                              ArithLogic & logic) {
    vec<PTRef> strictCandidates;
    while (true) {
        // TODO:  graph based instead of TS
        auto graph = constructHyperGraph(init, transition, sink, logic, vars);
        auto engine = EngineFactory(logic, options).getEngine(options.getOrDefault(Options::ENGINE, "spacer"));
        // Check if sink states are reachable within TS
        auto res = engine->solve(*graph);
        if (res.getAnswer() == VerificationAnswer::UNSAFE) {
            // When sink states are reachable, extract the number of transitions needed to reach the sink states
            uint num = res.getInvalidityWitness().getDerivation().size() - 3;
            // Construct the logical formula representing the trace:
            // Init(x) /\ Tr(x,x') /\ ... /\ Bad(x^(num))
            std::vector<PTRef> formulas;
            for (uint j = 0; j < num; j++) {
                formulas.push_back(TimeMachine(logic).sendFlaThroughTime(transition, j));
            }
            PTRef trace = logic.mkAnd(formulas);
            PTRef originalTransition = transition;
            std::tie(init, transition) = blockDeterministicPrefix(init, transition, sink, trace, num, logic);

            SMTSolver SMTsolver(logic, SMTSolver::WitnessProduction::NONE);
            SMTsolver.assertProp(logic.mkAnd(init, transition));
            // We check if init states are blocked (it's impossible to make a transition from initial state)
            // When it is the case, TS is terminating
            if (SMTsolver.check() == SMTSolver::Answer::UNSAT) { return {Answer::YES, logic.mkOr(strictCandidates)}; }

            // This is an extension of the approach, constructing TrInv and attempting to prove termination
            // and non-termination using invariants
            if (num > 0) {
                if (!generateWellfoundedDisjuncts(originalTransition, sink, trace, num, logic, strictCandidates)) continue;
                auto [answer1, res2] = refineTransitionInvariant(init, transition, sink, logic, strictCandidates);
                if (answer1 != Answer::UNKNOWN) return {answer1, res2};
            }
        } else if (res.getAnswer() == VerificationAnswer::SAFE) {
            SMTSolver SMTsolver(logic, SMTSolver::WitnessProduction::NONE);
            SMTsolver.assertProp(logic.mkAnd(init, transition));
            // We check if init state is blocked (it's impossible to make a transition from initial state)
            // When it is the case, TS is terminating
            if (SMTsolver.check() == SMTSolver::Answer::UNSAT) { return {Answer::YES, logic.getTerm_false()}; }
            // In case if sink states are not reachable, we need to construct the inductive invariant and demonstrate
            // that it doesn't contain any sink states itself.
            // It is possible since we add constraints to the transition relation, which were not accounted for
            // initially.
            auto witness = res.getValidityWitness();
            assert(witness.getDefinitions().size() == 3);
            PTRef inv = logic.getTerm_true();
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
                return {Answer::NO, inv};
            } else {
                // We update the sink states by the detected sink states and rerun the verification
                sink = constr;
            }

        } else {
            assert(false && "Unreachable!");
            return {Answer::ERROR, logic.getTerm_false()};
        }
    }

    return {Answer::ERROR, logic.getTerm_false()};
}

ReachabilityNonterm::Answer ReachabilityNonterm::run(TransitionSystem const & ts) {
    vars = ts.getStateVars();
    auto aux_vars = ts.getAuxiliaryVars();
    ArithLogic & logic = dynamic_cast<ArithLogic &>(ts.getLogic());
    PTRef init = ts.getInit();
    PTRef transition = normalize(ts.getTransition(), logic);
    transition = toDNF(transition, logic);
    std::vector<PTRef> tmp_vars = vars;
    tmp_vars.insert(tmp_vars.end(), aux_vars.begin(), aux_vars.end());
    // Transition relation is well-founded
    if (!logic.isOr(transition) && checkWellFounded(transition, logic, tmp_vars)) { return Answer::YES; }

    // In this case query is a set of sink states - states from which transition is not possible.
    // sink /\ transition is UNSAT
    PTRef sink = logic.mkNot(QuantifierElimination(logic).keepOnly(transition, vars));

    // if sink is false, there are no sink states in the TS, therefore it is nonterminating
    if (sink == logic.getTerm_false()) { return Answer::NO; }

    // Witness computation is required, as we need to use both counterexample traces to limit terminating states
    // and inductive invariants to prove nontermination
    DETERMINISTIC_TRANSITION = determinismCheck(transition, logic, vars);
    covered = logic.getTerm_false();
    // Safety-Based Termination Analysis
    // TODO: Figure out why passing in transition is problematic
    auto [answer, trInvOrRecurringSet] = analyzeTS(init, transition, sink, logic);
    return answer;
}

// This function takes a counterexample of the length n, detects states that deterministically lead to termination
// and blocks them.
// Function returns updated blocked init
std::tuple<PTRef, PTRef> ReachabilityNonterm::blockDeterministicPrefix(PTRef init, PTRef transition, PTRef sink,
                                                                       PTRef trace, uint num, ArithLogic & logic) {
    PTRef sinkAtNum = TimeMachine(logic).sendFlaThroughTime(sink, num);
    PTRef transitions = logic.mkAnd({init, trace, sinkAtNum});

    SMTSolver SMTsolver(logic, SMTSolver::WitnessProduction::NONE);
    SMTsolver.assertProp(transitions);
    // Check that sink is reachable in num transitions
    assert(SMTsolver.check() == SMTSolver::Answer::SAT);

    SMTsolver.resetSolver();
    SMTsolver.assertProp(logic.mkAnd({init, trace, logic.mkNot(sinkAtNum)}));
    PTRef guaranteedTerminating = sinkAtNum;

    uint j = 0;
    bool nondet_trace = !DETERMINISTIC_TRANSITION && SMTsolver.check() == SMTSolver::Answer::SAT;
    // Traversing trace from the Bad to Init, detecting the last transition where some variables
    // were assigned nondetermenistically (Only if it is possible to reach some states other then sink in n trs)
    if (nondet_trace) {
        for (j = num; j > 0; j--) {
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
            SMTsolver.assertProp(logic.mkAnd(
                {Base, TimeMachine(logic).sendFlaThroughTime(transition, j - 1), logic.mkNot(guaranteedTerminating)}));

            // It means that this transition was nondetermenistic, since
            // using transition from the states that guaranteed to reach termination in n-j+1 transitions
            // it is possible to reach states which are not guaranteed to reach termination in n-j transitions
            if (SMTsolver.check() == SMTSolver::Answer::SAT) {
                break;
            } else {
                guaranteedTerminating = Base;
            }
        }
    }

    if (j == 0) {
        // If transitions were deterministic, initial states are blocked
        init =
            nondet_trace
                ? TermUtils(logic).simplifyMax(logic.mkAnd(init, logic.mkNot(guaranteedTerminating)))
                : TermUtils(logic).simplifyMax(logic.mkAnd(
                      init, logic.mkNot(QuantifierElimination(logic).keepOnly(logic.mkAnd({trace, sinkAtNum}), vars))));
    } else {
        // Otherwise, states leading to termination are blocked from transition
        PTRef block = TimeMachine(logic).sendFlaThroughTime(guaranteedTerminating, -j + 1);
        assert(block != logic.getTerm_true());
        transition = logic.mkAnd(transition, logic.mkNot(block));
    }

    return {init, transition};
}

// This function attempts to construct transition invariant. It constructs disjuncts of transition invariant
// candidate, by building interpolant. Interpolants are DNFized, and disjuncts are checked for well-foundness.
bool ReachabilityNonterm::generateWellfoundedDisjuncts(PTRef transition, PTRef sink, PTRef trace, uint num, ArithLogic & logic,
                                            vec<PTRef> & strictCandidates) {
    SMTSolver SMTsolver(logic, SMTSolver::WitnessProduction::NONE);
    // Calculate the states that are guaranteed to terminate within num transitions:
    // Tr^n(x,x') /\ not Sink(x') - is a formula, which can be satisfied by any x which can
    // reach "not Sink(x')" in n transitions:
    PTRef NT = QuantifierElimination(logic).keepOnly(
        logic.mkAnd(trace, logic.mkNot(TimeMachine(logic).sendFlaThroughTime(sink, num))), vars);
    // States that can not reach "not Sink(x')" in n transitions (therefore necesarily reach Sink(x')):
    PTRef T = logic.mkNot(NT);

    // The procedure to construct transition invariants is executed
    PTRef itp = constructTransitionInvariantCandidates(T, transition, sink, num, logic, vars);
    // Extract well-founded disjuncts from the transition invariant
    auto newCands = extractWellFoundedCandidates(itp, sink, logic, vars);

    uint addedCands = 0;
    for (auto cand : newCands) {
        SMTsolver.resetSolver();
        SMTsolver.assertProp(logic.mkAnd(cand, logic.mkNot(logic.mkOr(strictCandidates))));
        if (SMTsolver.check() == SMTSolver::Answer::SAT) {
            strictCandidates.push(cand);
            addedCands++;
        }
    }
    return addedCands == 0;

}

// This function uses transition invariants candidates, constructing states which are not covered by the current.
// These states are checked for reachability. If they are not reachable - TS is terminating.
// If they are reachable - TS checks the termination for these states.
std::tuple<ReachabilityNonterm::Answer, PTRef>
ReachabilityNonterm::refineTransitionInvariant(PTRef init, PTRef transition, PTRef & sink, ArithLogic & logic,
                                               vec<PTRef> & strictCandidates) {
    PTRef trInv = logic.mkOr(strictCandidates);
    PTRef id = getId(vars, logic);
    SMTSolver smt_checker(logic, SMTSolver::WitnessProduction::ONLY_MODEL);
    // We check if TrInv is a general transition invariant
    // (trInv \/ Id) /\ Tr => trInv
    smt_checker.assertProp(logic.mkAnd({logic.mkOr(trInv, id), TimeMachine(logic).sendFlaThroughTime(transition, 1),
                                      logic.mkNot(shiftOnlyNextVars(trInv, vars, logic))}));
    // Check if trInv is Transition Invariant
    if (smt_checker.check() == SMTSolver::Answer::UNSAT) {
        // If trInv is Transition invariant, then Tr leads to termination on the whole state-space
        return {Answer::YES, trInv};
    }

    PTRef noncoveredStates = QuantifierElimination(logic).keepOnly(
        logic.mkAnd({logic.mkOr(trInv, id), TimeMachine(logic).sendFlaThroughTime(transition, 1),
                     logic.mkNot(shiftOnlyNextVars(trInv, vars, logic))}),
        vars);
    covered = TermUtils(logic).simplifyMax(logic.mkOr(covered, logic.mkNot(noncoveredStates)));

    // We check if the states that are not covered by TrInv are reachable
    auto graph =
        constructHyperGraph(init, transition, logic.mkAnd({logic.mkNot(sink), logic.mkNot(covered)}), logic, vars);
    auto engine = EngineFactory(logic, options).getEngine(options.getOrDefault(Options::ENGINE, "spacer"));

    // If states not covered by TrInv are not reachable - then TrInv is transition invariant on all
    // reachable states, therefore it is well-founded transition invariant
    auto res = engine->solve(*graph);
    if (res.getAnswer() == VerificationAnswer::SAFE) { return {Answer::YES, trInv}; }
    // Otherwise, if states not covered by TrInv are reachable, then the following procedure should
    // take place:
    // 1. Detect the states outside of TrInv that are reachable
    // 2. Check if those states are terminating or not
    PTRef reached = logic.getTerm_false();

    // Construction of reached states
    {
        int num_non = res.getInvalidityWitness().getDerivation().size() - 3;
        assert(res.getAnswer() == VerificationAnswer::UNSAFE);
        assert(num_non >= 0);
        vec<PTRef> last_vars;
        // Extract integer variables from the inequalities
        for (auto var : vars) {
            last_vars.push(TimeMachine(logic).sendVarThroughTime(var, num_non));
        }
        // Construct the logical formula representing the trace:
        // Init(x) /\ Tr(x,x') /\ ... /\ Bad(x^(num))
        std::vector<PTRef> formulas(num_non);
        for (int k = 0; k < num_non; k++) {
            formulas[k] = TimeMachine(logic).sendFlaThroughTime(transition, k);
        }
        smt_checker.resetSolver();
        PTRef transitions = logic.mkAnd(
            {init, logic.mkAnd(formulas),
             TimeMachine(logic).sendFlaThroughTime(logic.mkAnd({logic.mkNot(sink), logic.mkNot(covered)}), num_non)});
        smt_checker.assertProp(transitions);
        if (smt_checker.check() != SMTSolver::Answer::SAT) assert(false);
        // We get some of the reachable states
        reached = TermUtils(logic).simplifyMax(TimeMachine(logic).sendFlaThroughTime(
            ModelBasedProjection(logic).keepOnly(transitions, last_vars, *smt_checker.getModel()), -num_non));
    }

    // TODO: Think what to do if init is "REACHED" (ideally I want init to be in covered by TrINV)
    //   SMTsolver.assertProp(logic.mkAnd(logic.mkNot(init), reached));

    assert(reached != logic.getTerm_false());
    // Algorithm checks if reachable states are terminating
    auto [answer, subinv] =
        analyzeTS(reached, transition, TermUtils(logic).simplifyMax(logic.mkNot(noncoveredStates)), logic);
    // TODO: It is possible to do check differently, analyzing <noncoveredStates, tr,
    //   not(noncoveredStates)>
    //   If this terminates, then the whole TS terminates, but if it nonterinates we need to prove
    //   reachability
    if (answer == Answer::YES) {
        // TODO: Need to change TrInv, adding found subinv in a better way
        strictCandidates.clear();
        strictCandidates.push(subinv);
        strictCandidates.push(trInv);

        // TODO: Think if maybe sink can be even more restricted...
        sink = TermUtils(logic).simplifyMax(logic.mkOr(sink, reached));
        smt_checker.resetSolver();
        // TODO: It should work for  subinv \/ TrInv, but it does not
        //    weaker TrInv seems to fail more often then stronger TrInv :(
        smt_checker.assertProp(
            logic.mkAnd({noncoveredStates, logic.mkOr(subinv, id), TimeMachine(logic).sendFlaThroughTime(transition, 1),
                         logic.mkNot(shiftOnlyNextVars(subinv, vars, logic))}));
        // Check if trInv is Transition Invariant on the whole state-space
        if (smt_checker.check() == SMTSolver::Answer::UNSAT) {
            // If trInv is Transition invariant, then Tr leads to termination on the whole state-space
            return {Answer::YES, subinv};
        }
    } else if (answer == Answer::NO)
        return {Answer::NO, subinv};

    return {Answer::UNKNOWN, logic.getTerm_false()};
}

} // namespace golem::termination