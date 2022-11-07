/*
 * Copyright (c) 2020-2022, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */


#include "TransitionSystem.h"
#include "TermUtils.h"

bool TransitionSystem::isWellFormed() {
//    return systemType->isStateFormula(init) && systemType->isStateFormula(query) && systemType->isTransitionFormula(transition);
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

SystemType::SystemType(std::vector<SRef> stateVarTypes, std::vector<SRef> auxiliaryVarTypes, Logic & logic) : logic(logic) {
    struct Helper {
        Helper(Logic & logic, std::string varNamePrefix) : logic(logic), varNamePrefix(std::move(varNamePrefix)) {}
        Logic & logic;
        std::string prefix = "ts::";
        std::string varNamePrefix;
        std::size_t counter = 0;

        PTRef operator()(SRef sref) { return logic.mkVar(sref, std::string(prefix + varNamePrefix + std::to_string(counter++)).c_str());}
    };
    TimeMachine tm(logic);
    Helper helper{logic, "x"};
    std::transform(stateVarTypes.begin(), stateVarTypes.end(), std::back_inserter(stateVars), [&](SRef sref) {
        return tm.getVarVersionZero(helper(sref));
    });
    std::transform(stateVars.begin(), stateVars.end(), std::back_inserter(nextStateVars), [&](PTRef var) {
        return tm.sendVarThroughTime(var,1);
    });
    helper.varNamePrefix = "aux";
    std::transform(auxiliaryVarTypes.begin(), auxiliaryVarTypes.end(), std::back_inserter(auxiliaryVars), [&](SRef sref) {
        return tm.getVarVersionZero(helper(sref));
    });
}

SystemType::SystemType(std::vector<PTRef> stateVars, std::vector<PTRef> auxiliaryVars, Logic & logic) : logic(logic) {
    std::transform(stateVars.begin(), stateVars.end(), std::back_inserter(nextStateVars), [&logic](PTRef var) {
        return TimeMachine(logic).sendVarThroughTime(var, 1);
    });
    this->stateVars = std::move(stateVars);
    this->auxiliaryVars = std::move(auxiliaryVars);
}

SystemType::SystemType(vec<PTRef> const & stateVars, vec<PTRef> const & auxiliaryVars, Logic & logic) : logic(logic) {
    std::transform(stateVars.begin(), stateVars.end(), std::back_inserter(nextStateVars), [&logic](PTRef var) {
        return TimeMachine(logic).sendVarThroughTime(var, 1);
    });
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
    return std::all_of(vars.begin(), vars.end(), [&allVars](PTRef var){
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
    std::transform(stateVars.begin(), stateVars.end(), std::back_inserter(helperVars), [&](PTRef var) {
        return tm.sendVarThroughTime(var,2);
    });
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