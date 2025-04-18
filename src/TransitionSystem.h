/*
 * Copyright (c) 2020-2025, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef GOLEM_TRANSITIONSYSTEM_H
#define GOLEM_TRANSITIONSYSTEM_H

#include "osmt_terms.h"

#include <memory>
#include <vector>

namespace golem {
class SystemType {

    std::vector<PTRef> stateVars;
    std::vector<PTRef> nextStateVars;
    std::vector<PTRef> auxiliaryVars; // Allowed in the transition relation

    Logic & logic;

public:
    SystemType(std::vector<SRef> stateVarTypes, Logic & logic);
    SystemType(std::vector<SRef> stateVarTypes, std::vector<SRef> auxiliaryVarTypes, Logic & logic);
    SystemType(std::vector<PTRef> stateVars, std::vector<PTRef> auxiliaryVars, Logic & logic);
    SystemType(vec<PTRef> const & stateVars, vec<PTRef> const & auxiliaryVars, Logic & logic);

    [[nodiscard]] bool isStateFormula(PTRef fla) const;

    [[nodiscard]] bool isTransitionFormula(PTRef fla) const;

    [[nodiscard]] std::vector<PTRef> const & getStateVars() const { return stateVars; }
    [[nodiscard]] std::vector<PTRef> const & getNextStateVars() const { return nextStateVars; }
    [[nodiscard]] std::vector<PTRef> const & getAuxiliaryVars() const { return auxiliaryVars; }
};

class TransitionSystem {

    Logic & logic;

    std::unique_ptr<SystemType> systemType;

    PTRef init;
    PTRef transition;
    PTRef query;

public:
    TransitionSystem(Logic & logic, std::unique_ptr<SystemType> systemType, PTRef initialStates,
                     PTRef transitionRelation, PTRef badStates)
        : logic(logic),
          systemType(std::move(systemType)),
          init(initialStates),
          transition(transitionRelation),
          query(badStates) {
        if (not isWellFormed()) { throw std::logic_error("Transition system not created correctly"); }
    }

    [[nodiscard]] PTRef getInit() const;
    [[nodiscard]] PTRef getQuery() const;
    [[nodiscard]] PTRef getTransition() const;

    [[nodiscard]] Logic & getLogic() const;

    [[nodiscard]] std::vector<PTRef> getStateVars() const;
    [[nodiscard]] std::vector<PTRef> getNextStateVars() const;
    [[nodiscard]] std::vector<PTRef> getAuxiliaryVars() const;

    static TransitionSystem reverse(TransitionSystem const &);

    static PTRef reverseTransitionRelation(TransitionSystem const &);

private:
    [[nodiscard]] bool isWellFormed() const;

    [[nodiscard]] PTRef toNextStateVar(PTRef var) const;
};

struct KTo1Inductive {
    enum class Mode { UNFOLD, QE };
    explicit KTo1Inductive(Mode mode) : mode(mode) {}
    [[nodiscard]] PTRef kinductiveToInductive(PTRef invariant, unsigned k, TransitionSystem const & system) const;

private:
    Mode mode;

    [[nodiscard]] static PTRef qe(PTRef invariant, unsigned k, TransitionSystem const & system);
    [[nodiscard]] static PTRef unfold(PTRef invariant, unsigned k, TransitionSystem const & system);
};

PTRef kinductiveToInductive(PTRef invariant, unsigned k, TransitionSystem const & system);
} // namespace golem

#endif // GOLEM_TRANSITIONSYSTEM_H
