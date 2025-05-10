/*
 * Copyright (c) 2023-2025, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "SmtSolver.h"

namespace golem {
SMTSolver::SMTSolver(Logic & logic, WitnessProduction setup) {
    bool produceModel = setup == WitnessProduction::ONLY_MODEL || setup == WitnessProduction::MODEL_AND_INTERPOLANTS;
    bool produceInterpolants =
        setup == WitnessProduction::ONLY_INTERPOLANTS || setup == WitnessProduction::MODEL_AND_INTERPOLANTS;
    const char * msg = "ok";
    this->config.setOption(SMTConfig::o_produce_models, SMTOption(produceModel), msg);
    this->config.setOption(SMTConfig::o_produce_inter, SMTOption(produceInterpolants), msg);
    solver = std::make_unique<MainSolver>(logic, config, "");
}

void SMTSolver::resetSolver() {
    solver = std::make_unique<MainSolver>(solver->getLogic(), config, "");
}

void SMTSolver::assertProp(PTRef prop) {
    solver->insertFormula(prop);
}

SMTSolver::Answer SMTSolver::check() {
    auto res = solver->check();
    if (res == s_True) { return Answer::SAT; }
    if (res == s_False) { return Answer::UNSAT; }
    if (res == s_Error) { return Answer::ERROR; }
    return Answer::UNKNOWN;
}

void SMTSolver::push() {
    solver->push();
}

void SMTSolver::pop() {
    solver->pop();
}

namespace {
Formulas checkEntailmentOneByOne(SMTSolver & solver, Formulas candidates, Logic & logic) {
    Formulas implied;
    for (PTRef candidate : candidates) {
        solver.push();
        solver.assertProp(logic.mkNot(candidate));
        auto const res = solver.check();
        if (res == SMTSolver::Answer::UNSAT) { implied.push(candidate); }
        solver.pop();
    }
    return implied;
}

Formulas impliedBy(SMTSolver & solver, Formulas candidates, Logic & logic) {
    vec<PTRef> queries;
    queries.capacity(candidates.size());
    vec<PTRef> activationLiterals;
    activationLiterals.capacity(candidates.size());
    for (int counter = 0; counter < candidates.size(); ++counter) {
        std::string name = ".act" + std::to_string(counter);
        PTRef activationVariable = logic.mkBoolVar(name.c_str());
        activationLiterals.push(activationVariable);
        queries.push(logic.mkAnd(activationLiterals[counter], logic.mkNot(candidates[counter])));
    }

    solver.assertProp(logic.mkOr(queries));

    auto disabled = 0u;
    while (disabled < queries.size_()) {
        solver.push();
        solver.assertProp(logic.mkAnd(activationLiterals));
        auto res = solver.check();
        if (res == SMTSolver::Answer::UNSAT) { break; }
        if (res != SMTSolver::Answer::SAT) {
            assert(false);
            throw std::logic_error("Solver could not solve a problem while trying to push components!");
        }
        auto model = solver.getModel();
        for (auto i = 0; i < activationLiterals.size(); ++i) {
            if (logic.isNot(activationLiterals[i])) { continue; } // already disabled
            if (model->evaluate(queries[i]) == logic.getTerm_true()) {
                ++disabled;
                assert(not logic.isNot(activationLiterals[i]));
                activationLiterals[i] = logic.mkNot(activationLiterals[i]);
            }
        }
        solver.pop();
    }

    Formulas implied;
    for (auto i = 0; i < candidates.size(); ++i) {
        if (not logic.isNot(activationLiterals[i])) { implied.push(candidates[i]); }
    }
    return implied;
}
} // namespace

Formulas impliedBy(Formulas candidates, PTRef assertion, Logic & logic) {
    SMTSolver solver(logic, SMTSolver::WitnessProduction::ONLY_MODEL);
    solver.assertProp(assertion);
    return impliedBy(solver, std::move(candidates), logic);
}

Formulas impliedBy(Formulas candidates, vec<PTRef> const & assertions, Logic & logic) {
    SMTSolver solver(logic, SMTSolver::WitnessProduction::ONLY_MODEL);
    for (PTRef const assertion : assertions) {
        solver.assertProp(assertion);
    }
    return impliedBy(solver, std::move(candidates), logic);
}

Formulas checkEntailmentOneByOne(Formulas candidates, PTRef assertion, Logic & logic) {
    SMTSolver solver(logic, SMTSolver::WitnessProduction::NONE);
    solver.assertProp(assertion);
    return checkEntailmentOneByOne(solver, std::move(candidates), logic);
}

Formulas checkEntailmentOneByOne(Formulas candidates, vec<PTRef> const & assertions, Logic & logic) {
    SMTSolver solver(logic, SMTSolver::WitnessProduction::NONE);
    for (PTRef const assertion : assertions) {
        solver.assertProp(assertion);
    }
    return checkEntailmentOneByOne(solver, std::move(candidates), logic);
}
} // namespace golem
