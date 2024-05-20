/*
 * Copyright (c) 2024, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "ArgBasedEngine.h"

#include "utils/SmtSolver.h"

#include <memory>

class PredicateAbstractionManager {
public:
    explicit PredicateAbstractionManager(Logic & logic) : logic(logic) {}
    using Predicates = std::set<PTRef>;
    void initialize(std::vector<SymRef> const & symbols) {
        for (SymRef symbol : symbols) {
            symbolsToPredicates.emplace(symbol, Predicates{});
        }
    }

    Logic & getLogic() { return logic; }

    [[nodiscard]] auto const & predicatesFor(SymRef symbol) const {
        auto it = symbolsToPredicates.find(symbol);
        assert(it != symbolsToPredicates.end());
        return it->second;
    }

    void addPredicate(SymRef symbol, PTRef predicate) { symbolsToPredicates.at(symbol).insert(predicate); }
private:
    Logic & logic;
    std::unordered_map<SymRef, Predicates, SymRefHash> symbolsToPredicates;
};

class OverApproximatedStates {};

class CartesianPredicateAbstractionStates : public OverApproximatedStates {
    PredicateAbstractionManager & manager;
    PredicateAbstractionManager::Predicates satisfiedPredicates;
public:
    CartesianPredicateAbstractionStates(
        PredicateAbstractionManager & manager, PredicateAbstractionManager::Predicates && predicates)
        : manager(manager), satisfiedPredicates(std::move(predicates)) {}

    [[nodiscard]] PTRef asSingleFormula() const {
        Logic & logic = manager.getLogic();
        vec<PTRef> args;
        args.capacity(satisfiedPredicates.size());
        for (PTRef predicate : satisfiedPredicates) {
            args.push(predicate);
        }
        return logic.mkAnd(std::move(args));
    }

    bool operator==(CartesianPredicateAbstractionStates const & other) {
        assert(&other.manager == &this->manager);
        auto const & myPredicates = this->satisfiedPredicates;
        auto const & otherPredicates = other.satisfiedPredicates;
        return myPredicates.size() == otherPredicates.size() and std::equal(myPredicates.begin(), myPredicates.end(), otherPredicates.begin());
    }
};

struct ARGNode {
    SymRef predicateSymbol;
    std::unique_ptr<CartesianPredicateAbstractionStates> reachedStates;
    [[nodiscard]] PTRef getReachedStates() const {
        return reachedStates->asSingleFormula();
    };
};

inline bool operator==(ARGNode n1, ARGNode n2) { return n1.reachedStates == n2.reachedStates and n1.predicateSymbol.x == n2.predicateSymbol.x; }

class ARG {
public:
    using NodeId = std::size_t;

    struct Edge {
        std::vector<NodeId> sources;
        NodeId target;
        EId clauseId;
    };
private:
    ChcDirectedHyperGraph const & clauses;
    PredicateAbstractionManager predicateManager;
    std::vector<ARGNode> nodes;
    std::unordered_map<SymRef, std::vector<NodeId>, SymRefHash> instances;
    std::unordered_map<NodeId, std::vector<Edge>> incomingEdges;

public:
    constexpr static NodeId ENTRY = 0;
    explicit ARG(ChcDirectedHyperGraph const & clauses) : clauses(clauses), predicateManager(clauses.getLogic()) {
        auto symbols = clauses.getVertices();
        for (auto predicateSymbol : symbols) {
            instances.emplace(predicateSymbol, std::vector<NodeId>{});
        }
        predicateManager.initialize(symbols);
    }

    [[nodiscard]] PTRef getReachedStates(NodeId id) const {
        return nodes[id].getReachedStates();
    }

    [[nodiscard]] SymRef getPredicateSymbol(NodeId id) const {
        return nodes[id].predicateSymbol;
    }

    [[nodiscard]] PTRef getClauseConstraint(EId eid) const {
        return clauses.getEdgeLabel(eid);
    }

    /// Returns the ID of the new node with the given symbol and predicates and bool flag indicating if this new node
    /// is covered (subsumed) by an existing node in ARG
    /// NOTE: Currently we check exact match, this can be improved with subsumption
    std::pair<NodeId, bool> tryInsertNode(SymRef symbol, PredicateAbstractionManager::Predicates && predicates) {
        ARGNode node{symbol, std::make_unique<CartesianPredicateAbstractionStates>(predicateManager, std::move(predicates))};
        auto const & existingInstances = instances.at(symbol);
        bool subsumed = std::find_if(existingInstances.begin(), existingInstances.end(), [&](NodeId id) {
            return *nodes[id].reachedStates == *node.reachedStates;
        }) != existingInstances.end();

        auto id = nodes.size();
        nodes.push_back(std::move(node));
        instances.at(symbol).push_back(id);
        return {id, subsumed};
    }

    void addEdge(Edge edge) {
        auto target = edge.target;
        incomingEdges[target].push_back(std::move(edge));
    }

    [[nodiscard]] Edge const & getIncomingEdge(NodeId target) const {
        assert(incomingEdges.count(target));
        assert(not incomingEdges.at(target).empty());
        return incomingEdges.at(target).front();
    }

    [[nodiscard]] auto const & getInstancesFor(SymRef symbol) const {
        auto it = instances.find(symbol);
        assert(it != instances.end());
        return it->second;
    }

    [[nodiscard]] auto const & getPredicatesFor(SymRef symbol) const {
        return predicateManager.predicatesFor(symbol);
    }

    [[nodiscard]] auto const & getClauses() const { return clauses; }

    void refine(std::unordered_map<SymRef, std::vector<PTRef>, SymRefHash> const & refinementInfo);
};

struct UnprocessedEdge {
    EId eid;
    std::vector<ARG::NodeId> sources;
};

class InterpolationTree {
public:
    using NodeId = std::size_t;
    static constexpr std::size_t NO_ID = static_cast<std::size_t>(-1);
    static InterpolationTree make(ARG const & arg, UnprocessedEdge const & queryEdge);
    [[nodiscard]] PTRef getInstanceFor(NodeId id) const {
        assert(nodeToSymbolInstance.count(id) > 0);
        return nodeToSymbolInstance.at(id);
    }
private:
    struct Node {
        NodeId id;
        NodeId parent;
        std::vector<NodeId> children;
        PTRef label;
        // For CEX generation
        EId clauseId;
    };

    std::vector<Node> nodes;
    std::map<NodeId, PTRef> nodeToSymbolInstance;
    NodeId rootId {0};

    explicit InterpolationTree() {}

    NodeId createNode(NodeId parent, EId clauseId) {
        Node node{.id = nodes.size(), .parent = parent, .clauseId = clauseId};
        nodes.push_back(node);
        return nodes.back().id;
    }

    void addChild(NodeId parent, NodeId child) {
        assert(parent < nodes.size());
        nodes[parent].children.push_back(child);
    }

    void setLabel(NodeId node, PTRef label) {
        assert(node < nodes.size());
        nodes[node].label = label;
    }

    void computeLabels(ARG const & arg);

public:
    struct Result {
        std::unique_ptr<Model> model = nullptr;
        std::unordered_map<InterpolationTree::NodeId, PTRef> interpolant;

        [[nodiscard]] bool isFeasible() const { return model != nullptr; }
    };

    Result solve(Logic & logic) const;

    [[nodiscard]] std::vector<Node> getNodes() const { return nodes; }
};

class EdgeQueue {
public:
    void addEdge(UnprocessedEdge e);
    UnprocessedEdge pop();
    [[nodiscard]] bool isEmpty() const;
    void clear();
private:
    std::deque<UnprocessedEdge> queue;
};

class Algorithm {
    ChcDirectedHyperGraph const & clauses;
    bool computeWitness;
    AdjacencyListsGraphRepresentation representation;
    EdgeQueue queue;
    ARG arg;
    std::unordered_map<SymRef, std::vector<PTRef>, SymRefHash> lastRefinementInfo;
    InvalidityWitness witness;

public:
    explicit Algorithm(ChcDirectedHyperGraph const & clauses, bool computeWitness = false)
        : clauses(clauses),
          computeWitness(computeWitness),
          representation{AdjacencyListsGraphRepresentation::from(clauses)},
          arg{clauses}
    {
        auto [nodeId, covered] = arg.tryInsertNode(clauses.getEntry(), PredicateAbstractionManager::Predicates{});
        assert(not covered);
        assert(nodeId == ARG::ENTRY);
        auto facts = representation.getOutgoingEdgesFor(clauses.getEntry());
        for (EId fact : facts) {
            queue.addEdge({.eid = fact, .sources = {nodeId} });
        }
    }

    VerificationResult run();

private:
    void computeNewUnprocessedEdges(ARG::NodeId);
    std::pair<ARG::NodeId, bool> computeTarget(UnprocessedEdge const & edge);
    bool isRealProof(UnprocessedEdge const & edge);
    void refine();
    void computeInvalidityWitness(InterpolationTree const & itpTree, Model & model);
};

namespace{
void increment(std::vector<std::size_t> & indices, std::vector<std::vector<ARG::NodeId>> const & allInstances) {
    assert(not indices.empty());
    for (int i = indices.size() - 1; ; --i) {
        ++indices[i];
        if (indices[i] == allInstances[i].size() and i > 0) { indices[i] = 0; }
        else { break; }
    }
}
}

void Algorithm::computeNewUnprocessedEdges(ARG::NodeId nodeId) {
    struct Checker {
        PTRef edgeConstraint;
        Logic & logic;
        SMTSolver solver;
        ARG const & arg;

        Checker(PTRef edgeConstraint, Logic & logic, ARG const & arg)
            : edgeConstraint(edgeConstraint),
              logic(logic),
              solver(logic, SMTSolver::WitnessProduction::NONE),
              arg(arg)
        {
            solver.getCoreSolver().insertFormula(edgeConstraint);
        }

        bool isFeasible(std::vector<ARG::NodeId> const & sources) {
            solver.getCoreSolver().push();
            std::unordered_map<SymRef, int, SymRefHash> sourceCounts;
            VersionManager versionManager{logic};
            for (auto sourceId : sources) {
                PTRef reachedStates = arg.getReachedStates(sourceId);
                PTRef versionedStates = versionManager.baseFormulaToSource(reachedStates, sourceCounts[arg.getPredicateSymbol(sourceId)]++);
                solver.getCoreSolver().insertFormula(versionedStates);
            }
            auto res = solver.getCoreSolver().check();
            bool infeasible = res == s_False;
            solver.getCoreSolver().pop();
            return not infeasible;
        }
    };

    auto const & candidateClauses = representation.getOutgoingEdgesFor(arg.getPredicateSymbol(nodeId));
    // TODO: We may get the same edge multiple times if the predicate symbol appears multiple times in the body
    for (EId edge : candidateClauses) {
        // find all instances of edge sources in ARG and check feasibility
        auto sources = clauses.getSources(edge);
        std::vector<std::vector<ARG::NodeId>> allInstances;
        // TODO: one of the sources (corresponding to the new ARGnode) should be fixed!
        // TODO: What if we have a clause with multiple occurences of the same predicate?
        std::transform(std::begin(sources), std::end(sources), std::back_inserter(allInstances), [&](auto symbol) { return arg.getInstancesFor(symbol);});
        if (std::any_of(allInstances.begin(), allInstances.end(), [](auto const & nodeInstances){ return nodeInstances.empty(); })) {
            continue;
        }
        std::vector<std::size_t> indices(sources.size(), 0u);
        Checker checker(clauses.getEdgeLabel(edge), clauses.getLogic(), arg);
        for (; indices[0] != allInstances[0].size(); increment(indices, allInstances)) {
            std::vector<ARG::NodeId> argSources;
            for (std::size_t i = 0; i < indices.size(); ++i) {
                argSources.push_back(allInstances[i][indices[i]]);
            }
            if (checker.isFeasible(argSources)) {
                queue.addEdge({.eid = edge, .sources = std::move(argSources)});
            }
        }
    }
}

std::pair<ARG::NodeId, bool> Algorithm::computeTarget(const UnprocessedEdge & edge) {
    Logic & logic = clauses.getLogic();
    VersionManager versionManager{logic};
    std::unordered_map<SymRef, int, SymRefHash> sourcesCount;
    SMTSolver solver(logic,SMTSolver::WitnessProduction::NONE);
    solver.getCoreSolver().insertFormula(clauses.getEdgeLabel(edge.eid));
    for (auto sourceId : edge.sources) {
        PTRef reachedStates = arg.getReachedStates(sourceId);
        PTRef versioned = versionManager.baseFormulaToSource(reachedStates, sourcesCount[arg.getPredicateSymbol(sourceId)]++);
        solver.getCoreSolver().insertFormula(versioned);
    }
    auto target = clauses.getEdge(edge.eid).to;
    std::set<PTRef> impliedPredicates;
    for (PTRef predicate : arg.getPredicatesFor(target)) {
        solver.getCoreSolver().push();
        PTRef versionedPredicate = versionManager.baseFormulaToTarget(predicate);
        solver.getCoreSolver().insertFormula(logic.mkNot(versionedPredicate));
        auto res = solver.getCoreSolver().check();
        if (res == s_False) { impliedPredicates.insert(predicate); }
        solver.getCoreSolver().pop();
    }
    return arg.tryInsertNode(target, std::move(impliedPredicates));
}

bool Algorithm::isRealProof(UnprocessedEdge const & query) {
    assert(clauses.getEdge(query.eid).to == clauses.getExit());
    // build the formula/interpolation tree (DAG?)
    auto interpolationTree = InterpolationTree::make(arg, query);
    auto itpResult = interpolationTree.solve(clauses.getLogic());
    lastRefinementInfo.clear();
    if (itpResult.isFeasible()) {
        if (computeWitness) { computeInvalidityWitness(interpolationTree, *itpResult.model); }
    } else {
        TimeMachine timeMachine(clauses.getLogic());
        for (auto const & node : interpolationTree.getNodes()) {
            if (node.parent == InterpolationTree::NO_ID) { continue; }
            assert(itpResult.interpolant.count(node.id) > 0);
            PTRef interpolant = itpResult.interpolant.at(node.id);
            PTRef clearedInterpolant = timeMachine.versionedFormulaToUnversioned(interpolant);
            auto symbol = clauses.getTarget(node.clauseId);
            lastRefinementInfo[symbol].push_back(clearedInterpolant);
        }
    }
    return itpResult.isFeasible();
}

VerificationResult Algorithm::run() {
    while (not queue.isEmpty()) {
        auto nextEdge = queue.pop();
        EId originalEdge = nextEdge.eid;
        if (clauses.getEdge(originalEdge).to == clauses.getExit()) {
            if (isRealProof(nextEdge)) {
                return VerificationResult{VerificationAnswer::UNSAFE, witness};
            }
            refine();
            continue;
        }
        auto [id, isCovered] = computeTarget(nextEdge);
        if (not isCovered) {
            computeNewUnprocessedEdges(id);
        }
        arg.addEdge(ARG::Edge{.sources = std::move(nextEdge.sources), .target = id, .clauseId = nextEdge.eid});
    }
    if (not computeWitness) { return VerificationResult{VerificationAnswer::SAFE}; }
    // compute invariants
    ValidityWitness::definitions_t definitions;
    Logic & logic = clauses.getLogic();
    for (SymRef symbol : clauses.getVertices()) {
        if (symbol == logic.getSym_true()) {
            definitions.emplace(logic.getTerm_true(), logic.getTerm_true());
            continue;
        }
        if (symbol == logic.getSym_false()) {
            definitions.emplace(logic.getTerm_false(), logic.getTerm_false());
            continue;
        }
        auto const & argNodeIds = arg.getInstancesFor(symbol);
        vec<PTRef> reachedStates;
        for (ARG::NodeId nodeId : argNodeIds) {
            reachedStates.push(arg.getReachedStates(nodeId));
        }
        PTRef definition = logic.mkOr(std::move(reachedStates));
        PTRef sourcePredicate = clauses.getStateVersion(symbol);
        PTRef predicate = logic.getPterm(sourcePredicate).size() > 0 ? VersionManager(logic).sourceFormulaToBase(sourcePredicate) : sourcePredicate;
        definitions.emplace(predicate, definition);
    }
    return VerificationResult{VerificationAnswer::SAFE, ValidityWitness(std::move(definitions))};
}

namespace {
    bool computeWitness(Options const & options) {
        return options.hasOption(Options::COMPUTE_WITNESS) and options.getOption(Options::COMPUTE_WITNESS) == "true";
    }
}

VerificationResult ARGBasedEngine::solve(const ChcDirectedHyperGraph & graph) {
    return Algorithm(graph, computeWitness(options)).run();
}

bool EdgeQueue::isEmpty() const {
    return queue.empty();
}

void EdgeQueue::addEdge(UnprocessedEdge e) {
    queue.push_back(std::move(e));
}

UnprocessedEdge EdgeQueue::pop() {
    assert(not queue.empty());
    auto res = std::move(queue.front());
    queue.pop_front();
    return res;
}

void EdgeQueue::clear() {
    queue.clear();
}

InterpolationTree::Result InterpolationTree::solve(Logic & logic) const {
    SMTSolver solver(logic, SMTSolver::WitnessProduction::MODEL_AND_INTERPOLANTS);
    for (auto const & node : nodes) {
        assert(node.parent == InterpolationTree::NO_ID or node.id > node.parent);
        solver.getCoreSolver().insertFormula(node.label);
    }
    auto res = solver.getCoreSolver().check();
    if (res == s_True) { return InterpolationTree::Result{.model = solver.getCoreSolver().getModel(), .interpolant = {}}; }

    if (res != s_False) { throw std::logic_error("Solver could not return answer!"); }
    auto itpContext = solver.getCoreSolver().getInterpolationContext();
    std::vector<opensmt::ipartitions_t> partitions;
    partitions.resize(nodes.size(), 0);
    for (auto rit = nodes.rbegin(); rit != nodes.rend(); ++rit) {
        auto myId = rit->id;
        opensmt::setbit(partitions[myId], myId);
        auto parentId = rit->parent;
        if (parentId != NO_ID) { opensmt::orbit(partitions[parentId], partitions[parentId], partitions[myId]); }
    }
    InterpolationTree::Result result;
    std::vector<PTRef> interpolants;
    interpolants.reserve(nodes.size());
    for (std::size_t i = 0; i < nodes.size(); ++i) {
        itpContext->getSingleInterpolant(interpolants, partitions[i]);
        assert(interpolants.size() == i + 1);
        result.interpolant.emplace(nodes[i].id, interpolants.back());
    }
    return result;
}

void Algorithm::refine() {
    arg.refine(lastRefinementInfo);
    queue.clear();
    auto facts = representation.getOutgoingEdgesFor(clauses.getEntry());
    for (EId fact : facts) {
        queue.addEdge({.eid = fact, .sources = {ARG::ENTRY} });
    }
}

void InterpolationTree::computeLabels(ARG const & arg) {
    assert(nodeToSymbolInstance.empty());
    std::unordered_map<SymRef, std::size_t, SymRefHash> symbolEncountered;
    auto const & clauses = arg.getClauses();
    auto & logic = clauses.getLogic();
    nodeToSymbolInstance.emplace(rootId, logic.getTerm_false());
    TermUtils utils{logic};
    VersionManager manager{logic};
    TimeMachine timeMachine{logic};
    assert(not nodes.empty());
    NodeId root = 0;
    std::vector<NodeId> stack {root};
    while (not stack.empty()) {
        NodeId current = stack.back();
        stack.pop_back();
        assert(current < nodes.size());
        auto const & node = nodes[current];
//        if (node.children.empty()) { continue; }
        TermUtils::substitutions_map substitutions;
        auto const & edge = clauses.getEdge(node.clauseId);
        assert((edge.from.size() == 1 and edge.from[0] == clauses.getEntry()) or edge.from.size() == node.children.size());
        if (auto target = edge.to; target != clauses.getExit()) {
            assert(nodeToSymbolInstance.count(current) > 0);
            PTRef predicateInstance = clauses.getNextStateVersion(target);
            PTRef nodeInstance = nodeToSymbolInstance.at(current);
            utils.mapFromPredicate(predicateInstance, nodeInstance, substitutions);
        }
        std::unordered_map<SymRef, int, SymRefHash> sourcesCounter;
        for (std::size_t i = 0; i < node.children.size(); ++i) {
            SymRef sourceSymbol = edge.from[i];
            if (sourceSymbol == clauses.getEntry()) { assert(false); continue; } // TODO: check if this is needed
            PTRef predicateInstance = clauses.getStateVersion(sourceSymbol, sourcesCounter[sourceSymbol]++);
            auto symbolVersion = symbolEncountered[sourceSymbol]++;
            auto vars = utils.predicateArgsInOrder(predicateInstance);
            for (PTRef var : vars) {
                PTRef versionedVar = timeMachine.sendFlaThroughTime(
                    timeMachine.getVarVersionZero(manager.toBase(var)), static_cast<int>(symbolVersion));
                auto[_, inserted] = substitutions.emplace(var, versionedVar);
                assert(inserted); (void)inserted;
                // TODO: Check how auxiliary vars look like
            }
            PTRef nodePredicate = utils.varSubstitute(predicateInstance, substitutions);
            auto [_, inserted] = nodeToSymbolInstance.emplace(node.children[i], nodePredicate);
            assert(inserted); (void)inserted;
        }
        PTRef defaultConstraint = edge.fla.fla;
        PTRef versionedConstraint = utils.varSubstitute(defaultConstraint, substitutions);
        setLabel(current, versionedConstraint);
        for (NodeId childId : node.children) {
            stack.push_back(childId);
        }
    }
}

void ARG::refine(std::unordered_map<SymRef, std::vector<PTRef>, SymRefHash> const & refinementInfo) {
    for (auto && [predicateSymbol, newPredicates] : refinementInfo) {
        for (PTRef newPredicate : newPredicates) {
            predicateManager.addPredicate(predicateSymbol, newPredicate);
        }
    }
    // Regenerate ARG
    // For now, we clear it completely
    this->incomingEdges.clear();
    this->nodes.clear();
    for (auto && [_, symbolInstances] : instances) {
        symbolInstances.clear();
    }
    tryInsertNode(clauses.getEntry(), {});
}

InterpolationTree InterpolationTree::make(ARG const & arg, UnprocessedEdge const & queryEdge) {
    InterpolationTree tree;
    tree.rootId = tree.createNode(InterpolationTree::NO_ID, queryEdge.eid);

    struct Entry {
        ARG::NodeId argId;
        InterpolationTree::NodeId parentId;
    };
    std::vector<Entry> stack;
    auto addSources = [&](auto begin, auto end, InterpolationTree::NodeId parentId) {
        for (auto it = begin; it != end; ++it) {
            stack.push_back({.argId = *it, .parentId = parentId});
        }
    };
    addSources(queryEdge.sources.rbegin(), queryEdge.sources.rend(), tree.rootId);
    while (not stack.empty()) {
        auto [current, parent] = stack.back();
        stack.pop_back();
        if (current == ARG::ENTRY) { continue; }
        auto const & edge = arg.getIncomingEdge(current);
        auto currentId = tree.createNode(parent, edge.clauseId);
        tree.addChild(parent, currentId);
        addSources(edge.sources.rbegin(), edge.sources.rend(), currentId);
    }
    tree.computeLabels(arg);
    return tree;
}

void Algorithm::computeInvalidityWitness(InterpolationTree const & itpTree, Model & model) {
    Logic & logic = clauses.getLogic();
    TermUtils utils(logic);
    std::unordered_map<InterpolationTree::NodeId, std::vector<std::size_t>> premiseMap;
    InvalidityWitness::Derivation derivation;
    using DerivationStep = InvalidityWitness::Derivation::DerivationStep;
    std::size_t stepIndex = 0;
    // First step is just true
    derivation.addDerivationStep({.index = stepIndex++, .premises = {}, .derivedFact = logic.getTerm_true(), .clauseId = {static_cast<id_t>(-1)}});

    auto const & nodes = itpTree.getNodes();
    for (auto it = nodes.rbegin(); it != nodes.rend(); ++it) {
        auto const & node = *it;
        PTRef nodeInstance = itpTree.getInstanceFor(node.id);
        auto vars = utils.predicateArgsInOrder(nodeInstance);
        vec<PTRef> varValues(vars.size(), PTRef_Undef);
        std::transform(vars.begin(), vars.end(), varValues.begin(), [&](PTRef var) { return model.evaluate(var); });
        DerivationStep step;
        step.derivedFact = logic.insertTerm(logic.getSymRef(nodeInstance), std::move(varValues));
        step.index = stepIndex++;
        step.clauseId = node.clauseId;
        auto premisesIt = premiseMap.find(node.id);
        step.premises = premisesIt == premiseMap.end() ? std::vector<std::size_t>{0} : premisesIt->second;
        if (node.parent != InterpolationTree::NO_ID) {
            auto & parentPremises = premiseMap[node.parent];
            parentPremises.insert(parentPremises.begin(), step.index);
        }
        derivation.addDerivationStep(std::move(step));

    }
    witness.setDerivation(std::move(derivation));
}