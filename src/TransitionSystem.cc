/*
 * Copyright (c) 2020-2025, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "TransitionSystem.h"

#include "QuantifierElimination.h"
#include "TermUtils.h"
#include "utils/SmtSolver.h"
#include "utils/Timer.h"

namespace golem {
bool TransitionSystem::isWellFormed() {
    // return systemType->isStateFormula(init) && systemType->isStateFormula(query) && systemType->isTransitionFormula(transition);
    bool ok = systemType->isStateFormula(init);
    if (not ok) {
        std::stringstream ss;
        TermUtils(logic).printTermWithLets(ss, init);
        std::cerr << "Problem in init:" << ss.str() << std::endl;
        return false;
    }
    ok = systemType->isStateFormula(query);
    if (not ok) {
        std::stringstream ss;
        TermUtils(logic).printTermWithLets(ss, query);
        std::cerr << "Problem in query: " << ss.str() << std::endl;
        return false;
    }
    ok = systemType->isTransitionFormula(transition);
    if (not ok) {
        std::stringstream ss;
        TermUtils(logic).printTermWithLets(ss, transition);
        std::cerr << "Problem in transition: " << ss.str() << std::endl;
        return false;
    }
    return true;
}

PTRef TransitionSystem::toNextStateVar(PTRef var) const {
    assert(logic.isVar(var));
    static std::string suffix = "#p";
    std::string originalName = logic.getSymName(var);
    std::string newName = originalName + suffix;
    return logic.mkVar(logic.getSortRef(var), newName.c_str());
}

SystemType::SystemType(std::vector<SRef> stateVarTypes, std::vector<SRef> auxiliaryVarTypes, Logic & logic)
    : logic(logic) {
    struct Helper {
        Helper(Logic & logic, std::string varNamePrefix) : logic(logic), varNamePrefix(std::move(varNamePrefix)) {}
        Logic & logic;
        std::string prefix = "ts::";
        std::string varNamePrefix;
        std::size_t counter = 0;

        PTRef operator()(SRef sref) {
            return logic.mkVar(sref, std::string(prefix + varNamePrefix + std::to_string(counter++)).c_str());
        }
    };
    TimeMachine tm(logic);
    Helper helper{logic, "x"};
    std::transform(stateVarTypes.begin(), stateVarTypes.end(), std::back_inserter(stateVars),
                   [&](SRef sref) { return tm.getVarVersionZero(helper(sref)); });
    std::transform(stateVars.begin(), stateVars.end(), std::back_inserter(nextStateVars),
                   [&](PTRef var) { return tm.sendVarThroughTime(var, 1); });
    helper.varNamePrefix = "aux";
    std::transform(auxiliaryVarTypes.begin(), auxiliaryVarTypes.end(), std::back_inserter(auxiliaryVars),
                   [&](SRef sref) { return tm.getVarVersionZero(helper(sref)); });
}

SystemType::SystemType(std::vector<PTRef> stateVars, std::vector<PTRef> auxiliaryVars, Logic & logic) : logic(logic) {
    std::transform(stateVars.begin(), stateVars.end(), std::back_inserter(nextStateVars),
                   [&logic](PTRef var) { return TimeMachine(logic).sendVarThroughTime(var, 1); });
    this->stateVars = std::move(stateVars);
    this->auxiliaryVars = std::move(auxiliaryVars);
}

SystemType::SystemType(vec<PTRef> const & stateVars, vec<PTRef> const & auxiliaryVars, Logic & logic) : logic(logic) {
    std::transform(stateVars.begin(), stateVars.end(), std::back_inserter(nextStateVars),
                   [&logic](PTRef var) { return TimeMachine(logic).sendVarThroughTime(var, 1); });
    std::copy(stateVars.begin(), stateVars.end(), std::back_inserter(this->stateVars));
    std::copy(auxiliaryVars.begin(), auxiliaryVars.end(), std::back_inserter(this->auxiliaryVars));
}

bool SystemType::isStateFormula(PTRef fla) const {
    auto const & currentStateVars = stateVars;
    vec<PTRef> vars = TermUtils(logic).getVars(fla);
    for (PTRef var : vars) {
        if (std::find(std::begin(currentStateVars), std::end(currentStateVars), var) == std::end(currentStateVars)) {
            return false;
        }
    }
    return true;
}

bool SystemType::isTransitionFormula(PTRef fla) const {
    std::vector<PTRef> allVars;
    allVars.reserve(stateVars.size() + nextStateVars.size() + auxiliaryVars.size());
    allVars.insert(allVars.end(), stateVars.begin(), stateVars.end());
    allVars.insert(allVars.end(), nextStateVars.begin(), nextStateVars.end());
    allVars.insert(allVars.end(), auxiliaryVars.begin(), auxiliaryVars.end());
    vec<PTRef> vars = TermUtils(logic).getVars(fla);
    return std::all_of(vars.begin(), vars.end(), [&allVars](PTRef var) {
        return std::find(std::begin(allVars), std::end(allVars), var) != std::end(allVars);
    });
}

PTRef TransitionSystem::getInit() const {
    return init;
}

PTRef TransitionSystem::getQuery() const {
    return query;
}

PTRef TransitionSystem::getTransition() const {
    return transition;
}

Logic & TransitionSystem::getLogic() const {
    return logic;
}

std::vector<PTRef> TransitionSystem::getStateVars() const {
    return this->systemType->getStateVars();
}

std::vector<PTRef> TransitionSystem::getNextStateVars() const {
    return this->systemType->getNextStateVars();
}

std::vector<PTRef> TransitionSystem::getAuxiliaryVars() const {
    return this->systemType->getAuxiliaryVars();
}

TransitionSystem TransitionSystem::reverse(TransitionSystem const & original) {
    PTRef reversedInitial = original.query;
    PTRef reversedQuery = original.init;
    PTRef reversedTransition = reverseTransitionRelation(original);
    auto type = std::make_unique<SystemType>(*original.systemType);
    return TransitionSystem(original.logic, std::move(type), reversedInitial, reversedTransition, reversedQuery);
}

PTRef TransitionSystem::reverseTransitionRelation(TransitionSystem const & transitionSystem) {
    PTRef transition = transitionSystem.transition;
    TimeMachine tm(transitionSystem.logic);
    auto const & stateVars = transitionSystem.getStateVars();
    auto const & nextStateVars = transitionSystem.getNextStateVars();
    std::vector<PTRef> helperVars;
    helperVars.reserve(stateVars.size());
    std::transform(stateVars.begin(), stateVars.end(), std::back_inserter(helperVars),
                   [&](PTRef var) { return tm.sendVarThroughTime(var, 2); });
    TermUtils utils(transitionSystem.logic);
    TermUtils::substitutions_map subst;
    std::size_t varCount = stateVars.size();
    for (auto i = 0u; i < varCount; ++i) {
        subst.insert({stateVars[i], helperVars[i]});
    }
    transition = utils.varSubstitute(transition, subst);

    subst.clear();
    for (auto i = 0u; i < varCount; ++i) {
        subst.insert({nextStateVars[i], stateVars[i]});
    }
    transition = utils.varSubstitute(transition, subst);

    subst.clear();
    for (auto i = 0u; i < varCount; ++i) {
        subst.insert({helperVars[i], nextStateVars[i]});
    }
    transition = utils.varSubstitute(transition, subst);

    return transition;
}

PTRef KTo1Inductive::kinductiveToInductive(PTRef invariant, unsigned k, TransitionSystem const & system) const {
    switch (mode) {
        case Mode::UNFOLD:
            return unfold(invariant, k, system);
        case Mode::QE:
            return qe(invariant, k, system);
        default:
            assert(false);
            throw std::logic_error("Unreachable!");
    }
}

/**
 * If P(x) is k-inductive invariant then the following formula is 1-inductive invariant:
 * P(x_0) \land \forall x_1,x_2,\ldots,x_{k-1}
 *  (P(x_0) \land Tr(x_0,x_1) \implies P(x_1))
 *  \land (P(x_0) \land Tr(x_0,x_1 \land P(x_1) \land Tr(x_1,x_2) \implies P(x_2))
 *  ...
 *  \land (P(x_0) \land Tr(x_0,x_1) \land p(x_1) \land \ldots \land P(x_{k-2}) \land Tr(x_{k-2},x_{k-1} \implies P(x_{k_1}))
 *
 * This is equivalent to
 * P(x_0) \land \neg \exists x_1,x_2,\ldots,x_{k-1}
 *  (P(x_0) \land Tr(x_0,x_1) \land \neg P(x_1))
 *  \lor (P(x_0) \land Tr(x_0,x_1 \land P(x_1) \land Tr(x_1,x_2) \land \neg P(x_2))
 *  ...
 *  \lor (P(x_0) \land Tr(x_0,x_1) \land p(x_1) \land \ldots \land P(x_{k-2}) \land Tr(x_{k-2},x_{k-1} \land \neg P(x_{k-1}))
 *
 * The quantifier-free core can be further rewritten using distributivity to
 * (P(x_0) \land Tr(x_0,x_1) \land (
 *  \neg P(x_1) \lor (P(x_1) \land Tr(x_1,x_2) \land (
 *   \neg P(x_2) \lor (P(x_2) \land Tr(x_2,x_3) \land (
 *    ...
 *      \neg P(x_{k-2}) \lor (P(x_{k-2}) \land Tr(x_{k-2},x_{k-1}) \land \neg P(x_{k-1})
 *   )...))
 *
 * @param invariant k-inductive invsariant for the transition system \p system
 * @param k
 * @param system
 * @return 1-inductive invariant for the same system that is logically stronger than the k-inductive one
 */
PTRef KTo1Inductive::qe(PTRef invariant, unsigned k, TransitionSystem const & system) {
    assert(k >= 2);
    Logic & logic = system.getLogic();
    PTRef transition = system.getTransition();
    auto stateVars = system.getStateVars();
    auto getNextVersion = [&logic](PTRef fla, int shift) { return TimeMachine(logic).sendFlaThroughTime(fla, shift); };
    PTRef acc = logic.getTerm_false();
    for (unsigned i = k - 1; i > 0; --i) {
        acc = logic.mkOr(acc, logic.mkNot(getNextVersion(invariant, i)));
        acc = logic.mkAnd({acc, getNextVersion(invariant, i - 1), getNextVersion(transition, i - 1)});
    }
    PTRef afterElimination = QuantifierElimination(logic).keepOnly(acc, stateVars);
    PTRef result = TermUtils(logic).toNNF(logic.mkNot(afterElimination));
    result = logic.mkAnd(result, invariant);
    return result;
}

namespace {

PTRef buildFormula(unsigned index, PTRef invariant, TransitionSystem const & system) {
    if (index == 0) { return system.getLogic().getTerm_true(); }
    Logic & logic = system.getLogic();
    TimeMachine timeMachine(logic);
    PTRef previous = buildFormula(index - 1, invariant, system);
    PTRef invariantShifted = timeMachine.sendFlaThroughTime(invariant, index - 1);
    PTRef stepShifted = timeMachine.sendFlaThroughTime(system.getTransition(), index - 1);
    PTRef initShifted = timeMachine.sendFlaThroughTime(system.getInit(), index);
    return logic.mkOr(initShifted, logic.mkAnd({previous, invariantShifted, stepShifted}));
}
} // namespace

/**
 * Computes 1-inductive invariant from a k-inductive one using only interpolation.
 * The idea is an application of the more general concept of reinforced unfold tranformation for CHCs from the paper
 * "Horn Clause Solvers for Program Verification", (https://link.springer.com/chapter/10.1007/978-3-319-23534-9_2).
 * Section 4.2 of the paper proves the correctness of the transformation and hints on use we implement here.
 * Here we use a variant that halves the \p k (rounded up) in every iteration.
 *
 * Consider the definition of 1-inductive invariant as a single Horn clause in NNF:
 * init(x^1) \lor (Inv(x^0) \land step(x^0,x^1)) \implies Inv(x^1)
 *
 * Unfolding this definition of $Inv$ k-1 times yields a formula equivalent to the definition of k-inductive invariant.
 * Following the approach described in the paper, we can split the formula in two parts and compute an interpolant.
 * Conjoining the interpolant to the original invariant yields k'-inductive invariant with k' < k.
 * Depending on how we split the formula, we can get to different k'. The smallest k' we can get to is k/2 (rounded up).
 *
 * @param invariant k-inductive invsariant for the transition system \p system
 * @param k
 * @param system
 * @return 1-inductive invariant for the same system that is logically stronger than the k-inductive one
 */
PTRef KTo1Inductive::unfold(PTRef invariant, unsigned k, TransitionSystem const & system) {
    Logic & logic = system.getLogic();
    TimeMachine tm(logic);
    while (k > 1) {
        // Split k into i + j such that i >= j
        unsigned j = k / 2;
        unsigned i = k - j;
        // Build the two formulas
        PTRef ipart = buildFormula(i, invariant, system);
        PTRef jpart = i == j ? ipart : buildFormula(j, invariant, system);
        PTRef shifted = tm.sendFlaThroughTime(jpart, i);
        PTRef negatedInvariant = logic.mkNot(tm.sendFlaThroughTime(invariant, k));
        SMTSolver solver(logic, SMTSolver::WitnessProduction::ONLY_INTERPOLANTS);
        solver.assertProp(ipart);
        solver.assertProp(logic.mkAnd(shifted, negatedInvariant));
        auto res = solver.check();
        if (res != SMTSolver::Answer::UNSAT) {
            throw std::logic_error("Error in reducing k-inductive invariant to 1-inductive: Query must be UNSAT!");
        }
        auto itpContext = solver.getInterpolationContext();
        vec<PTRef> itps;
        ipartitions_t partitions = 1;
        itpContext->getSingleInterpolant(itps, partitions);
        assert(itps.size() == 1);
        PTRef itp = tm.sendFlaThroughTime(itps[0], -static_cast<int>(i));
        invariant = TermUtils(logic).conjoin(invariant, itp);
        assert(i < k);
        k = i;
    }
    return invariant;
}

PTRef kinductiveToInductive(PTRef invariant, unsigned k, TransitionSystem const & system) {
    if (k == 1) { return invariant; }
    // std::cout << "Reducing k-inductive invariant with k=" << k << std::endl;
    // Timer timer;
    PTRef res = KTo1Inductive{KTo1Inductive::Mode::UNFOLD}.kinductiveToInductive(invariant, k, system);
    // std::cout << timer.elapsedMilliseconds() << " ms" << std::endl;
    return res;
}
} // namespace golem