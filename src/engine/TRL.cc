/*
 * Copyright (c) 2025, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "TRL.h"

#include "ModelBasedProjection.h"
#include "QuantifierElimination.h"
#include "utils/SmtSolver.h"
#include "utils/StdUtils.h"

#include <ranges>

namespace golem {

namespace {

class ConjunctiveVariableProjection {
public:
    explicit ConjunctiveVariableProjection(ArithLogic & logic) : logic(logic) {}
    PTRef projectTo(PTRef fla, std::vector<PTRef> const & vars, Model & model) const;

private:
    ArithLogic & logic;
};

struct Loop {
    std::size_t stepIndex;
    std::size_t length;
};

struct LoopValuation {
    TermUtils::substitutions_map evaluation;
};

struct BlockingClause {
    PTRef clause;
    std::size_t activationDepth;
};

class Context {
public:
    explicit Context(TransitionSystem const & system, bool computeWintess = false)
        : system(system), logic(dynamic_cast<ArithLogic &>(system.getLogic())), computeWitness(computeWintess) {
        indexVar = TimeMachine(logic).getVarVersionZero(logic.mkIntVar("trl_id"));
    }
    TransitionSystemVerificationResult run();

private:
    [[nodiscard]] ArithLogic & getLogic() const { return dynamic_cast<ArithLogic &>(system.getLogic()); }
    [[nodiscard]] std::optional<Loop> getLoop(std::vector<PTRef> trace) const;
    LoopValuation getLoopValuation(Loop loop, Model & model) const;
    [[nodiscard]] PTRef computeBlockingClause(Loop const & loop, PTRef relation, Model & model) const;
    [[nodiscard]] PTRef project(PTRef fla, Model & model, std::size_t shift = 0) const;
    [[nodiscard]] PTRef shiftTo(PTRef fla, std::size_t start, std::size_t end) const;
    [[nodiscard]] PTRef unshiftFrom(PTRef fla, std::size_t start, std::size_t end) const;
    [[nodiscard]] PTRef indexVarAt(std::size_t index) const;
    PTRef transitiveProjection(PTRef fla, Model & model, Loop loop);

    PTRef getFreshLoopCounter();
    [[nodiscard]] std::vector<PTRef> getSystemVars(std::size_t step) const;
    PTRef computeInductiveInvariant(std::vector<PTRef> const & relations, int diameter) const;

    TransitionSystem const & system;
    ArithLogic & logic;
    PTRef indexVar;
    std::size_t loopCounterIndex = 0;
    bool computeWitness = false;
};

TransitionSystemVerificationResult Context::run() {
    int currentUnrolling = 0;
    auto lp = dynamic_cast<ArithLogic *>(&system.getLogic());
    if (not lp) { return {VerificationAnswer::UNKNOWN}; }
    ArithLogic & logic = *lp;
    TimeMachine tm(logic);
    SMTSolver solver(logic, SMTSolver::WitnessProduction::ONLY_MODEL);
    std::vector<PTRef> relations{system.getTransition()};
    std::vector<BlockingClause> blockingClauses;

    solver.assertProp(system.getInit());
    while (true) {
        solver.push();
        PTRef versionedQuery = tm.sendFlaThroughTime(system.getQuery(), currentUnrolling);
        solver.assertProp(versionedQuery);
        auto res = solver.check();
        if (res == SMTSolver::Answer::SAT) { return {VerificationAnswer::UNKNOWN}; }
        if (res != SMTSolver::Answer::UNSAT) { return {VerificationAnswer::UNKNOWN}; }
        solver.pop();
        solver.push();
        PTRef currentIndexVar = tm.sendVarThroughTime(indexVar, currentUnrolling);
        // encode transitivity
        if (currentUnrolling > 0) {
            PTRef transitivityConstraint =
                logic.mkOr(logic.mkEq(currentIndexVar, logic.getTerm_IntZero()),
                           logic.mkNot(logic.mkEq(currentIndexVar, tm.sendVarThroughTime(currentIndexVar, -1))));
            solver.assertProp(transitivityConstraint);
        }
        // encode →τ and learned relations
        auto nextStep = [&]() -> PTRef {
            vec<PTRef> disjuncts;
            for (unsigned i = 0u; i < relations.size(); ++i) {
                disjuncts.push(logic.mkAnd(tm.sendFlaThroughTime(relations[i], currentUnrolling),
                                           logic.mkEq(currentIndexVar, logic.mkIntConst(i))));
            }
            return logic.mkOr(std::move(disjuncts));
        }();
        solver.assertProp(nextStep);
        // Add blocking clauses for current unrolling
        for (auto const & blockingClause : blockingClauses) {
            if (blockingClause.activationDepth == static_cast<std::size_t>(currentUnrolling)) {
                solver.assertProp(blockingClause.clause);
            }
        }
        // Check if the search space is exhausted
        res = solver.check();
        if (res == SMTSolver::Answer::UNSAT) {
            if (not computeWitness) { return {VerificationAnswer::SAFE}; }
            PTRef inductiveInvariant = computeInductiveInvariant(relations, currentUnrolling);
            return {VerificationAnswer::SAFE, inductiveInvariant};
        }
        if (res != SMTSolver::Answer::SAT) { return {VerificationAnswer::UNKNOWN}; }
        // check current trace for a loop
        auto model = solver.getModel();
        auto const relationsOnTrace = [&]() -> std::vector<std::size_t> {
            std::vector<std::size_t> relationIndices;
            for (int i = 0; i <= currentUnrolling; i++) {
                auto relationIndexTerm = model->evaluate(tm.sendVarThroughTime(indexVar, i));
                assert(relationIndexTerm != PTRef_Undef);
                auto relationIndexAsRational = logic.getNumConst(relationIndexTerm);
                assert(relationIndexAsRational.isInteger());
                auto [relationIndex, _] = relationIndexAsRational.tryGetNumDen().value();
                relationIndices.push_back(relationIndex);
            }
            return relationIndices;
        }();
        // FIXME: Use proper ranges syntax
        auto const trace = [&]() -> std::vector<PTRef> {
            std::vector<PTRef> steps;
            steps.reserve(relationsOnTrace.size());
            for (std::size_t index : relationsOnTrace) {
                assert(index < relations.size());
                PTRef const relation = relations[index];
                int const step = static_cast<int>(steps.size());
                PTRef const shifted = TimeMachine(logic).sendFlaThroughTime(relation, step);
                PTRef const projected = project(shifted, *model, step);
                steps.push_back(projected);
            }
            return steps;
        }();
        if (auto maybeLoop = getLoop(trace)) {
            auto loop = *maybeLoop;
            auto loopValuation = getLoopValuation(loop, *model);
            PTRef blockingRelation = [&]() {
                for (PTRef relation : relations | std::views::drop(1)) {
                    PTRef val = TermUtils(logic).varSubstitute(relation, loopValuation.evaluation);
                    if (val == logic.getTerm_false()) { continue; }
                    if (val == logic.getTerm_true()) return relation;
                    // Test consistency
                    SMTSolver auxSolver(logic, SMTSolver::WitnessProduction::ONLY_MODEL);
                    auxSolver.assertProp(val);
                    auto const res = auxSolver.check();
                    if (res == SMTSolver::Answer::SAT) { return relation; }
                }
                return PTRef_Undef;
            }();
            if (blockingRelation == PTRef_Undef) {
                PTRef loopFormula = [&]() -> PTRef {
                    vec<PTRef> loopsSteps;
                    for (PTRef step : trace | std::views::drop(loop.stepIndex) | std::views::take(loop.length)) {
                        loopsSteps.push(step);
                    }
                    return logic.mkAnd(std::move(loopsSteps));
                }();
                blockingRelation = transitiveProjection(loopFormula, *model, loop);
                blockingRelation = unshiftFrom(blockingRelation, 0, loop.length);
                relations.push_back(blockingRelation);
            }
            assert(blockingRelation != PTRef_Undef);
            // FIXME: This is cumbersome, we should not need an SMT check to get the proper model
            SMTSolver auxSolver(logic, SMTSolver::WitnessProduction::ONLY_MODEL);
            for (auto const & [var, val] : loopValuation.evaluation) {
                auxSolver.assertProp(logic.mkEq(var, val));
            }
            auxSolver.assertProp(blockingRelation);
            auto const res = auxSolver.check();
            assert(res == SMTSolver::Answer::SAT);
            if (res != SMTSolver::Answer::SAT) {
                throw std::logic_error("Blocking relation must be consistent with the loop");
            }
            model = auxSolver.getModel();
            PTRef blockingClause = computeBlockingClause(loop, blockingRelation, *model);
            blockingClauses.push_back({.clause = blockingClause, .activationDepth = loop.stepIndex + loop.length - 1});
            while (currentUnrolling >= static_cast<int>(loop.stepIndex)) {
                solver.pop();
                --currentUnrolling;
            }
        }
        ++currentUnrolling;
    }
    assert(false); // UNREACHABLE
    return {VerificationAnswer::UNKNOWN};
}

namespace {
void collectImplicant(Logic & logic, PTRef fla, Model & model, std::unordered_set<uint32_t> & processed,
                      std::vector<PTRef> & literals) {
    auto id = Idx(logic.getPterm(fla).getId());
    auto [_, inserted] = processed.insert(id);
    if (not inserted) { return; }
    PTRef const trueTerm = logic.getTerm_true();
    assert(model.evaluate(fla) == trueTerm);
    if (logic.isAtom(fla)) {
        literals.push_back(fla);
        return;
    }
    if (logic.isAnd(fla)) {
        // all children must be satisfied
        auto const size = logic.getPterm(fla).size();
        for (int i = 0; i < size; ++i) {
            PTRef child = logic.getPterm(fla)[i];
            assert(model.evaluate(child) == trueTerm);
            collectImplicant(logic, child, model, processed, literals);
        }
        return;
    }
    if (logic.isOr(fla)) {
        // at least one child must be satisfied
        auto const size = logic.getPterm(fla).size();
        for (int i = 0; i < size; ++i) {
            PTRef child = logic.getPterm(fla)[i];
            if (model.evaluate(child) == trueTerm) {
                collectImplicant(logic, child, model, processed, literals);
                return;
            }
        }
        assert(false);
        throw std::logic_error("Error in processing disjunction in collectImplicant!");
    }
    if (logic.isNot(fla)) {
        PTRef child = logic.getPterm(fla)[0];
        if (logic.isAtom(child)) {
            assert(model.evaluate(child) == logic.getTerm_false());
            literals.push_back(fla);
            return;
        }
        throw std::logic_error("Formula is not in NNF in collectImplicant!");
    }
    throw std::logic_error("Unexpected connective in formula in collectImplicant");
}
std::vector<PTRef> collectSatisfiedLiterals(PTRef nnf, Logic & logic, Model & model) {
    std::vector<PTRef> literals;
    std::unordered_set<uint32_t> processed;
    collectImplicant(logic, nnf, model, processed, literals);
    return literals;
}
} // namespace

PTRef ConjunctiveVariableProjection::projectTo(PTRef fla, std::vector<PTRef> const & vars, Model & model) const {
    PTRef const mbp = ModelBasedProjection(logic).keepOnly(fla, vars, model);
    PTRef const nnf = TermUtils(logic).toNNF(mbp);
    auto const sip = collectSatisfiedLiterals(nnf, logic, model);
    return logic.mkAnd(sip);
}

PTRef Context::transitiveProjection(PTRef fla, Model & model, Loop loop) {
    // Introduce diff variables
    auto loopBegVars = getSystemVars(loop.stepIndex);
    auto loopEndVars = getSystemVars(loop.stepIndex + loop.length);
    std::vector<std::pair<PTRef, PTRef>> diffVarVals;
    diffVarVals.reserve(loopBegVars.size());
    std::string const prefix = "trl::diff";
    auto isDiffVar = [&](PTRef term) {
        return logic.isVar(term) and strncmp(prefix.c_str(), logic.getSymName(term), strlen(prefix.c_str())) == 0;
    };
    vec<PTRef> diffEqualities;
    TermUtils::substitutions_map backSubstitution;
    for (auto i = 0u; i < loopBegVars.size(); ++i) {
        SRef type = logic.getSortRef(loopBegVars[i]);
        if (type != logic.getSort_int()) { continue; }
        std::string const name = prefix + std::to_string(i);
        PTRef const diffVar = logic.mkVar(type, name.c_str());
        PTRef const diff = logic.mkMinus(loopEndVars[i], loopBegVars[i]);
        diffEqualities.push(logic.mkEq(diffVar, diff));
        diffVarVals.emplace_back(diffVar, model.evaluate(diff));
        backSubstitution.insert({diffVar, diff});
    }
    // Compute projection
    PTRef extendedFla = logic.mkAnd(fla, logic.mkAnd(std::move(diffEqualities)));
    auto extendedModel = model.extend(diffVarVals);
    std::vector<PTRef> diffVars;
    std::ranges::copy(diffVarVals | std::views::transform(&std::pair<PTRef, PTRef>::first),
                      std::back_inserter(diffVars));
    PTRef projected = ConjunctiveVariableProjection(logic).projectTo(extendedFla, diffVars, *extendedModel);
    PTRef loopCounter = getFreshLoopCounter();
    TimeMachine tm(logic);
    loopCounter = tm.sendVarThroughTime(tm.getVarVersionZero(loopCounter), static_cast<int>(loop.stepIndex));
    std::vector<PTRef> recurrentLiterals = [&]() {
        std::vector<PTRef> res;
        vec<PTRef> conjuncts = TermUtils(logic).getTopLevelConjuncts(projected);
        for (PTRef conjunct : conjuncts) {
            bool isLit =
                logic.isAtom(conjunct) or (logic.isNot(conjunct) and logic.isAtom(logic.getPterm(conjunct)[0]));
            if (not isLit) { continue; }
            auto getFactorsFromTerm = [&](PTRef term) -> vec<PTRef> {
                assert(logic.isLinearTerm(term));
                if (logic.isLinearFactor(term)) { return {term}; }
                auto [_, factors] = logic.getConstantAndFactors(term);
                return std::move(factors);
            };
            auto isRecurrentFactor = [&](PTRef factor) {
                assert(logic.isLinearFactor(factor));
                auto [var, c] = logic.splitTermToVarAndConst(factor);
                return isDiffVar(var);
            };
            if (logic.isEquality(conjunct)) {
                // TODO: Improve
                PTRef lhs = logic.getPterm(conjunct)[0];
                PTRef rhs = logic.getPterm(conjunct)[1];
                if (logic.isConstant(lhs)) { std::swap(lhs, rhs); }
                if (logic.isConstant(rhs) and logic.isLinearTerm(lhs)) {
                    auto factors = getFactorsFromTerm(lhs);
                    bool isRecurrent = std::all_of(factors.begin(), factors.end(), isRecurrentFactor);
                    if (isRecurrent) {
                        PTRef backSubstituted = TermUtils(logic).varSubstitute(lhs, backSubstitution);
                        res.push_back(logic.mkEq(logic.mkTimes(rhs, loopCounter), backSubstituted));
                    }
                }
            } else if (logic.isLeq(conjunct)) {
                auto [constant, term] = logic.leqToConstantAndTerm(conjunct);
                assert(logic.isLinearTerm(term));
                assert(logic.isConstant(constant));
                auto factors = getFactorsFromTerm(term);
                bool isRecurrent = std::all_of(factors.begin(), factors.end(), isRecurrentFactor);
                if (isRecurrent) {
                    PTRef backSubstituted = TermUtils(logic).varSubstitute(term, backSubstitution);
                    res.push_back(logic.mkLeq(logic.mkTimes(constant, loopCounter), backSubstituted));
                }
            } else if (logic.isNot(conjunct)) {
                // TODO:!!!
            }
            // TODO: Handle divisibility predicates
        }
        return res;
    }();
    vec<PTRef> projectionComponents = {logic.mkLt(logic.getTerm_IntZero(), loopCounter), logic.mkAnd(recurrentLiterals),
                                       ConjunctiveVariableProjection(logic).projectTo(fla, loopBegVars, model),
                                       ConjunctiveVariableProjection(logic).projectTo(fla, loopEndVars, model)};
    return tm.sendFlaThroughTime(logic.mkAnd(std::move(projectionComponents)), -(static_cast<int>(loop.stepIndex)));
}

PTRef Context::project(PTRef fla, Model & model, std::size_t shift) const {
    auto varsToKeep = system.getStateVars() + system.getNextStateVars();
    if (shift != 0) {
        for (PTRef & var : varsToKeep) {
            var = TimeMachine(logic).sendVarThroughTime(var, static_cast<int>(shift));
        }
    }
    return ConjunctiveVariableProjection(getLogic()).projectTo(fla, varsToKeep, model);
}

PTRef Context::computeBlockingClause(Loop const & loop, PTRef relation, Model & model) const {
    auto & logic = getLogic();
    PTRef const projection = project(relation, model);
    PTRef const neg = logic.mkNot(projection);
    PTRef const shifted = shiftTo(neg, loop.stepIndex, loop.stepIndex + loop.length);
    return loop.length == 1 ? logic.mkOr(shifted, logic.mkGt(indexVarAt(loop.stepIndex), logic.getTerm_IntZero()))
                            : shifted;
}

PTRef Context::indexVarAt(std::size_t index) const {
    return TimeMachine(logic).sendVarThroughTime(indexVar, static_cast<int>(index));
}

PTRef Context::shiftTo(PTRef fla, std::size_t stepStart, std::size_t stepEnd) const {
    assert(stepEnd > stepStart);
    TermUtils utils(logic);
    TimeMachine tm(logic);
    TermUtils::substitutions_map substitutions;
    for (PTRef var : system.getStateVars()) {
        substitutions.insert({var, tm.sendVarThroughTime(var, static_cast<int>(stepStart))});
    }
    for (PTRef var : system.getNextStateVars()) {
        substitutions.insert({var, tm.sendVarThroughTime(var, static_cast<int>(stepEnd) - 1)});
    }
    return utils.varSubstitute(fla, substitutions);
}

PTRef Context::unshiftFrom(PTRef fla, std::size_t stepStart, std::size_t stepEnd) const {
    assert(stepEnd > stepStart);
    TermUtils utils(logic);
    TimeMachine tm(logic);
    TermUtils::substitutions_map substitutions;
    for (PTRef var : system.getStateVars()) {
        substitutions.insert({tm.sendVarThroughTime(var, static_cast<int>(stepStart)), var});
    }
    for (PTRef var : system.getNextStateVars()) {
        substitutions.insert({tm.sendVarThroughTime(var, static_cast<int>(stepEnd) - 1), var});
    }
    return utils.varSubstitute(fla, substitutions);
}

std::optional<Loop> Context::getLoop(std::vector<PTRef> trace) const {
    std::vector<PTRef> transitions;
    transitions.reserve(trace.size());
    for (std::size_t i = 0u; i < trace.size(); ++i) {
        PTRef const base = TimeMachine(logic).sendFlaThroughTime(trace[i], -static_cast<int>(i));
        transitions.push_back(base);
    }

    // find the shortest subsequence with same first and last index -> loop
    std::unordered_map<PTRef, std::size_t, PTRefHash> lastKnowIndex;
    std::size_t smallestLenght = std::numeric_limits<std::size_t>::max();
    std::optional<std::size_t> startingIndex = std::nullopt;
    for (std::size_t i = 0; i < transitions.size(); ++i) {
        PTRef current = transitions[i];
        auto it = lastKnowIndex.find(current);
        if (it != lastKnowIndex.end()) {
            auto const previous = it->second;
            auto const diff = i - previous;
            if (diff < smallestLenght) {
                startingIndex = previous;
                smallestLenght = diff;
            }
        }
        lastKnowIndex[current] = i;
    }
    if (not startingIndex.has_value()) return std::nullopt;
    return Loop{.stepIndex = startingIndex.value(), .length = smallestLenght};
}

LoopValuation Context::getLoopValuation(Loop loop, Model & model) const {
    LoopValuation values;
    TimeMachine tm(logic);
    int shift = static_cast<int>(loop.stepIndex);
    for (PTRef var : system.getStateVars()) {
        values.evaluation.insert({var, model.evaluate(tm.sendVarThroughTime(var, shift))});
    }
    shift = static_cast<int>(loop.stepIndex + loop.length - 1); // -1 because we shift from step 1
    for (PTRef var : system.getNextStateVars()) {
        values.evaluation.insert({var, model.evaluate(tm.sendVarThroughTime(var, shift))});
    }
    return values;
}

PTRef Context::getFreshLoopCounter() {
    std::string const name = "trl_lc" + std::to_string(loopCounterIndex++);
    return logic.mkIntVar(name.c_str());
}
std::vector<PTRef> Context::getSystemVars(std::size_t step) const {
    std::vector<PTRef> res;
    TimeMachine tm(logic);
    for (PTRef var : system.getStateVars()) {
        res.push_back(tm.sendVarThroughTime(var, static_cast<int>(step)));
    }
    return res;
}

PTRef Context::computeInductiveInvariant(std::vector<PTRef> const & relations, int diameter) const {
    PTRef const extendedTransition = logic.mkOr(relations);
    TimeMachine tm(logic);
    vec<PTRef> components;
    PTRef current = system.getInit();
    components.push(current);
    for (int i = 0; i < diameter; ++i) {
        current = logic.mkAnd(current, tm.sendFlaThroughTime(extendedTransition, i));
        current = QuantifierElimination(logic).keepOnly(current, getSystemVars(i + 1));
        components.push(tm.sendFlaThroughTime(current, -(i + 1)));
    }
    return logic.mkOr(std::move(components));
}
} // namespace

TransitionSystemVerificationResult TRL::solve(TransitionSystem const & system) {
    return Context(system, computeWitness).run();
}

} // namespace golem
