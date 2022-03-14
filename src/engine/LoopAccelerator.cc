//
// Created by Martin Blicha on 25.08.20.
//

#include "LoopAccelerator.h"

#include <functional>
#include <sstream>

const std::string LoopAccelerator::PREFIX = "LoopAccDuplicate#";
const std::string LoopAccelerator::LOOP_COUNTER_PREFIX = "loop#";


ChcDirectedGraph LoopAccelerator::removeAcceleratedLoops(const ChcDirectedGraph & original,
                                                         std::map<EId, PTRef> const & acceleratedLoops) const {
    auto vertices = original.getVertexCopies();
    auto edges = original.getEdgeCopies();
    LinearCanonicalPredicateRepresentation predicateRepresentation = original.getPredicateRepresentation();
    auto entry = original.getEntryId();
    auto exit = original.getExitId();
    auto maxId = std::max_element(vertices.begin(), vertices.end(), [](Vertex const & first, Vertex const & second) {
        return first.id.id < second.id.id;
    })->id.id;
    auto nextId = maxId + 1;
    TimeMachine timeMachine(logic);
    // we need to split the vertex with self-loop into two and add an edge corresponding to the acceleration
    for (auto const & acceleration : acceleratedLoops) {
        // the current vertex will now represent the vertex AFTER acceleration
        // create another vertex then will represent the vertex before acceleration
        Vertex const & current = original.getVertex(original.getSource(acceleration.first));
        // duplicate the vertex with new symbol name
        SymRef currentSymbol = current.predicateSymbol;
        std::string duplicateName = LoopAccelerator::PREFIX + logic.getSymName(current.predicateSymbol);
        vec<SRef> domainSorts;
        for (unsigned int i = 0; i < logic.getSym(currentSymbol).nargs(); ++i) {
            domainSorts.push(logic.getSym(currentSymbol)[i]);
        }
        SymRef duplicateSymbol = logic.declareFun(duplicateName, logic.getSortRef(current.predicateSymbol), domainSorts);
        Vertex duplicate = Vertex{.predicateSymbol = duplicateSymbol, .id = {nextId++}};
        vertices.push_back(duplicate);
        // add the new symbol to canonical representation
        std::vector<PTRef> varargs; varargs.reserve(domainSorts.size_());
        for (SRef domainSort : domainSorts) {
            std::string varName = LoopAccelerator::PREFIX + "x#" + std::to_string(varCounter++);
            varargs.push_back(logic.mkVar(domainSort, varName.c_str()));
        }
        predicateRepresentation.addRepresentation(duplicateSymbol, varargs);
        // update edges and canonical predicate representation
        std::unordered_map<PTRef, PTRef, PTRefHash> varSubstNext;
        std::unordered_map<PTRef, PTRef, PTRefHash> varSubstCurrent;
        TermUtils utils(logic);
        auto originalVarsNext = utils.getVarsFromPredicateInOrder(predicateRepresentation.getTargetTermFor(currentSymbol));
        auto duplicateVarsNext = utils.getVarsFromPredicateInOrder(predicateRepresentation.getTargetTermFor(duplicateSymbol));
        auto originalVarsCurrent = utils.getVarsFromPredicateInOrder(predicateRepresentation.getSourceTermFor(currentSymbol));
        auto duplicateVarsCurrent = utils.getVarsFromPredicateInOrder(predicateRepresentation.getSourceTermFor(duplicateSymbol));
        for (std::size_t i = 0; i < originalVarsCurrent.size(); ++i) {
            varSubstCurrent.insert({originalVarsCurrent[i], duplicateVarsCurrent[i]});
            varSubstNext.insert({originalVarsNext[i], duplicateVarsNext[i]});
        }
        for (auto & edge : edges) {
            if (edge.to == current.id) {
                // update the edge representation
                if (edge.from == current.id) {
                    // the self-loop, change the edge label
                    PTRef acceleratedLabel = acceleration.second;
                    edge.fla = InterpretedFla{.fla = utils.varSubstitute(acceleratedLabel, varSubstCurrent)};
                    edge.from = duplicate.id;
                } else {
                    edge.to = duplicate.id;
                    edge.fla = InterpretedFla{.fla = utils.varSubstitute(edge.fla.fla, varSubstNext)};
                }
            }
        }
    }
    return ChcDirectedGraph(std::move(vertices), std::move(edges), std::move(predicateRepresentation), entry, exit);
}

std::map<EId, PTRef> LoopAccelerator::getAcceleratedLoops(std::vector<EId> selfLoops, ChcDirectedGraph const& graph) const {
    std::map<EId, PTRef> acceleratedDefs;
    std::vector<EId> accelerableLoops;
    TermUtils utils(logic);
    TimeMachine timeMachine(logic);
    for (auto const eid : selfLoops) {
        auto edge = graph.getEdge(eid);
        assert(edge.from == edge.to);
        PTRef label = edge.fla.fla;
        PTRef loopCounterVar = getLoopCounterVar();
        vec<PTRef> varDefs;
        bool success = false;
        auto conjuncts = utils.getTopLevelConjuncts(label);
        for (PTRef conjunct : conjuncts) {
            success = false;
            if (not logic.isEquality(conjunct)) { break; }
            auto vars = utils.getVars(conjunct);
            if (vars.size() != 2) { break; }
            auto versionNumber = timeMachine.getVersionNumber(vars[0]);
            if (versionNumber != 0 && versionNumber != 1) { break; }
            PTRef currentState = versionNumber == 0 ? vars[0] : timeMachine.sendVarThroughTime(vars[0], -1);
            PTRef nextState = timeMachine.sendVarThroughTime(currentState, 1);
            // the second var must match the first var, but it must represent the other state
            if (vars[1] != (versionNumber == 0 ? nextState : currentState)) { break; }
            // reformulate the equality as 'next = f(current)'
            PTRef lhs = logic.getPterm(conjunct)[0];
            PTRef rhs = logic.getPterm(conjunct)[1];
            if (not logic.isSortNum(logic.getSortRef(lhs))) { break; }
            PTRef zeroTerm = logic.mkMinus(lhs, rhs);
            PTRef nextStateDef = LATermUtils(logic).expressZeroTermFor(zeroTerm, nextState);
            // we can accelerate if 'f(current) = current + c' for some constant c
            PTRef acceleratedDefinition = PTRef_Undef;
            if (logic.isNumConst(nextStateDef) or logic.isNumVar(nextStateDef)) {
                // f(current) = c or f(current) = current => no change for any number of iterations
                acceleratedDefinition = nextStateDef;
            } else if (logic.isPlus(nextStateDef)) {
                auto size = logic.getPterm(nextStateDef).size();
                if (size == 2) { // with ITEs, there may be many arguments in the sum
                    PTRef var = logic.getPterm(nextStateDef)[0];
                    PTRef constant = logic.getPterm(nextStateDef)[1];
                    if (logic.isNumConst(var)) {
                        std::swap(var, constant);
                    }
                    assert(logic.isConstant(constant));
                    assert(logic.isVar(var) || logic.isTimes(var) || logic.isIte(var));
                    if (logic.isVar(var)) {
                        acceleratedDefinition = logic.mkPlus(var, logic.mkTimes(constant, loopCounterVar));
                    }
                }
            }
            if (acceleratedDefinition != PTRef_Undef) {
                // remember the accelerated definition
                varDefs.push(logic.mkEq(nextState, acceleratedDefinition));
                success = true;
            } else {
                break;
            }
        }
        if (success) {
            varDefs.push(logic.mkGeq(loopCounterVar, logic.getTerm_IntZero()));
            acceleratedDefs.insert({eid, logic.mkAnd(varDefs)});
        }
    }
    return acceleratedDefs;
}

GraphVerificationResult LoopAccelerator::solve(const ChcDirectedGraph & graph) {
//    graph.toDot(std::cout, logic);
    auto selfLoops = getSelfLoops(graph);
    auto acceleratedLoops = getAcceleratedLoops(std::move(selfLoops), graph);
    if (acceleratedLoops.empty()) {
        return delegate->solve(graph);
    }
    // create the new graph without the accelerated loops
    auto updatedGraph = removeAcceleratedLoops(graph, acceleratedLoops);
//    updatedGraph.toDot(std::cout, logic);
    auto res = delegate->solve(updatedGraph);
    if (res.getAnswer() == VerificationResult::SAFE) {
        // remove the duplicated predicates from list of definitions
        auto defs = res.getValidityWitness().getDefinitions();
        for (auto it = defs.begin(); it != defs.end(); /*increment in the body*/) {
            if (isAcceleratedPredicatedSymbol(it->first)) {
                it = defs.erase(it);
            } else {
                ++it;
            }
        }
        res = GraphVerificationResult(VerificationResult::SAFE, ValidityWitness(std::move(defs)));
    }
    if (res.getAnswer() == VerificationResult::UNSAFE) {
        // build the path formula and identify accelerated loops in the path
        auto const & errorPath = res.getInvalidityWitness().getErrorPath();
        InvalidityWitness witness;
        if (errorPath.isEmpty()) {
            // ERROR: empty error path received
            return GraphVerificationResult(VerificationResult::UNSAFE, std::move(witness));
        }
        vec<PTRef> pathSegmentFormulas;
        auto errorPathEdges = errorPath.getEdges();
        std::vector<std::size_t> acceleratedIndices;
        std::map<VId, VId> duplicateToOriginal;
        for (std::size_t i = 0; i < errorPathEdges.size(); ++i) {
            EId eid = errorPathEdges[i];
            auto const & edge = updatedGraph.getEdge(eid);
            pathSegmentFormulas.push(TimeMachine(logic).sendFlaThroughTime(edge.fla.fla, i));
            if (isAcceleratedPredicatedSymbol(updatedGraph.getVertex(edge.from).predicateSymbol)) {
                acceleratedIndices.push_back(i);
                duplicateToOriginal.insert({edge.from, edge.to});
            }
        }
        if (not acceleratedIndices.empty()) {
            // Get the unrolling number from the satisfying assignment of the path
            SMTConfig config;
            MainSolver solver(logic, config, "loop unroller");
            solver.insertFormula(logic.mkAnd(pathSegmentFormulas));
            auto queryRes = solver.check();
            if (queryRes != s_True) {
                // ERROR: satisfying assignment could not be extracted
                return GraphVerificationResult(VerificationResult::UNSAFE, InvalidityWitness());
            }
            auto model = solver.getModel();
            std::map<std::size_t, long long> loopIndexToUnrollingNumber;
            for (std::size_t i = 0; i < acceleratedIndices.size(); ++i) {
                EId eid = errorPathEdges[acceleratedIndices[i]];
                auto const & edge = updatedGraph.getEdge(eid);
                PTRef var = extractLoopCountVar(edge.fla.fla);
                PTRef properlyIndexedVar = TimeMachine(logic).sendVarThroughTime(var, acceleratedIndices[i]);
                PTRef val = model->evaluate(properlyIndexedVar);
                if (not logic.isNumConst(val) || not logic.getNumConst(val).isInteger()) {
                    // ERROR: integer number could not be extracted for the loop counter
                    return GraphVerificationResult(VerificationResult::UNSAFE, InvalidityWitness());
                }
                auto numVal = logic.getNumConst(val);
                std::stringstream ss;
                ss << numVal;
                auto stringVal = ss.str();
                long long loopNumber = std::atoll(stringVal.c_str());
                loopIndexToUnrollingNumber.insert({acceleratedIndices[i], loopNumber});
            }
            // compute the new path replacing the accelerated edge with correspoding number of unrolled edges
            std::vector<EId> newErrorPathEdges;
            TermUtils utils(logic);
            for (std::size_t i = 0; i < errorPathEdges.size(); ++i) {
                EId eid = errorPathEdges[i];
                auto edge = updatedGraph.getEdge(eid);
                if (loopIndexToUnrollingNumber.count(i) > 0) {
                    // unroll
                    auto unrollingNumber = loopIndexToUnrollingNumber[i];
                    // turn the edge into self loop
                    assert(duplicateToOriginal.count(edge.from) > 0 and duplicateToOriginal[edge.from] == edge.to);
                    for (decltype(unrollingNumber) n = 0; n < unrollingNumber; ++n) {
                        newErrorPathEdges.push_back(eid);
                    }
                } else {
                    newErrorPathEdges.push_back(eid);
                }
            }
            InvalidityWitness::ErrorPath newPath;
            newPath.setPath(std::move(newErrorPathEdges));
            witness.setErrorPath(newPath);
            res = GraphVerificationResult(VerificationResult::UNSAFE, std::move(witness));
        }
    }
    return res;
}

bool LoopAccelerator::isLoopCounterVar(PTRef var) const {
    std::string name = logic.getSymName(var);
    return name.rfind(LoopAccelerator::LOOP_COUNTER_PREFIX, 0) == 0;
}

bool LoopAccelerator::isAcceleratedPredicatedSymbol(SymRef sym) const {
    std::string name = logic.getSymName(sym);
    return name.rfind(LoopAccelerator::PREFIX, 0) == 0;
}

PTRef LoopAccelerator::extractLoopCountVar(PTRef fla) const {
    TermUtils utils(logic);
    auto vars = utils.getVars(fla);
    auto it = std::find_if(vars.begin(), vars.end(), [this](PTRef var){
       return isLoopCounterVar(var);
    });
    if (it == vars.end()) {
        throw std::logic_error("Error in extracting invalidity witness in loop acceleration");
    }
    return *it;
}
