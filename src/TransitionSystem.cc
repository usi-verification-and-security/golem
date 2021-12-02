//
// Created by Martin Blicha on 21.07.20.
//

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


PTRef TransitionSystem::toNextStateVar(PTRef var, std::size_t steps) {
    assert(logic.isVar(var));
    static std::string suffix = "#p";
    std::string originalName = logic.getSymName(var);
    std::string newName = originalName + suffix;
    return logic.mkVar(logic.getSortRef(var), newName.c_str());
}

PTRef TransitionSystem::getPathFormula(std::size_t unrollingNumber) {
    vec<PTRef> components;
    components.push(helper->getFutureStateFormula(this->init, 0));
    for (std::size_t i = 0; i < unrollingNumber; ++i) {
        components.push(helper->getFutureTransitionFormula(this->transition, i));
    }
    components.push(helper->getFutureStateFormula(this->query, unrollingNumber));
    return logic.mkAnd(components);
}

void TransitionSystemHelper::ensureFrames(std::size_t k) {
    while(frames.size() <= k) {
        auto n = frames.size();
        frames.push_back(TransitionSystemHelper::Frame());
        auto & frame = frames.back();
        auto const & currentStateVars = systemType.getStateVars();
        std::transform(currentStateVars.begin(), currentStateVars.end(), std::back_inserter(frame.frameVars),
            [this, n](PTRef var) { return this->toFrameVar(var, n); });
    }
}

PTRef TransitionSystemHelper::getFutureStateFormula(PTRef fla, std::size_t k) {
    assert(systemType.isStateFormula(fla));
    ensureFrames(k);
    std::vector<PTRef> const& stateVars = systemType.getStateVars();
    auto const & frameVars = frames[k].frameVars;
    assert(stateVars.size() == frameVars.size());
    TermUtils::substitutions_map substMap;
    for (std::size_t i = 0; i < stateVars.size(); ++i) {
        substMap.insert({stateVars[i], frameVars[i]});
    }
    return TermUtils(logic).varSubstitute(fla, substMap);
}

PTRef TransitionSystemHelper::getFutureTransitionFormula(PTRef fla, std::size_t k) {
    assert(systemType.isTransitionFormula(fla));
    ensureFrames(k + 1);
    auto const & stateVars = systemType.getStateVars();
    auto const & nextStateVars = systemType.getNextStateVars();
    auto const & frameVars = frames[k].frameVars;
    assert(stateVars.size() == frameVars.size());
    TermUtils::substitutions_map substMap;
    for (std::size_t i = 0; i < stateVars.size(); ++i) {
        substMap.insert({stateVars[i], frameVars[i]});
    }
    auto const & nextFrameVars = frames[k + 1].frameVars;
    for (std::size_t i = 0; i < nextStateVars.size(); ++i) {
        substMap.insert({nextStateVars[i], nextFrameVars[i]});
    }
    return TermUtils(logic).varSubstitute(fla, substMap);
}

PTRef TransitionSystemHelper::toFrameVar(PTRef var, std::size_t frameNum) {
    assert(logic.isVar(var));
    SRef sort = logic.getSortRef(var);
    std::string numberFramePrefix = framePrefix + std::to_string(frameNum);
    std::string newVarName = numberFramePrefix + logic.getSymName(var);
    return logic.mkVar(sort, newVarName.c_str());
}

SystemType::SystemType(std::vector<SRef> stateVarTypes, std::vector<SRef> auxiliaryVarTypes, Logic & logic) : logic(logic) {
    struct Helper {
        Helper(Logic & logic, std::string varNamePrefix) : logic(logic), varNamePrefix(std::move(varNamePrefix)) {}
        std::string prefix = "ts::";
        std::string varNamePrefix;
        std::size_t counter = 0;
        Logic & logic;

        PTRef operator()(SRef sref) { return logic.mkVar(sref, std::string(prefix + varNamePrefix + std::to_string(counter++)).c_str());}
    };
    Helper helper{logic, "x"};
    std::transform(stateVarTypes.begin(), stateVarTypes.end(), std::back_inserter(stateVars), helper);
    helper.varNamePrefix = "xp";
    std::transform(stateVarTypes.begin(), stateVarTypes.end(), std::back_inserter(nextStateVars), helper);
    helper.varNamePrefix = "aux";
    std::transform(auxiliaryVarTypes.begin(), auxiliaryVarTypes.end(), std::back_inserter(auxiliaryVars), helper);
}

SystemType::SystemType(std::vector<PTRef> stateVars, std::vector<PTRef> auxiliaryVars, Logic & logic) : logic(logic) {
    std::transform(stateVars.begin(), stateVars.end(), std::back_inserter(nextStateVars), [&logic](PTRef var) {
        return TimeMachine(logic).sendVarThroughTime(var, 1);
    });
    this->stateVars = std::move(stateVars);
    this->auxiliaryVars = std::move(auxiliaryVars);
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

std::vector<PTRef> TransitionSystem::getStateVars() const {
    return this->systemType->getStateVars();
}

std::vector<PTRef> TransitionSystem::getNextStateVars() const {
    return this->systemType->getNextStateVars();
}

std::vector<PTRef> TransitionSystem::getAuxiliaryVars() const {
    return this->systemType->getAuxiliaryVars();
}
