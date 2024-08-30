/*
 * Copyright (c) 2024, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "ArgBasedEngine.h"

#include "transformers/Transformer.h"
#include "utils/SmtSolver.h"
#include "utils/StdUtils.h"

#include <memory>

#define TRACE_LEVEL 0

#define TRACE(l, m)                                                                                                    \
    if (TRACE_LEVEL >= l) { std::cout << m << std::endl; }

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
    CartesianPredicateAbstractionStates(PredicateAbstractionManager & manager,
                                        PredicateAbstractionManager::Predicates && predicates)
        : manager(manager), satisfiedPredicates(std::move(predicates)) {}

    [[nodiscard]] PTRef asSingleFormula() const {
        Logic & logic = manager.getLogic();
        vec<PTRef> args;
        args.capacity(static_cast<int>(satisfiedPredicates.size()));
        for (PTRef predicate : satisfiedPredicates) {
            args.push(predicate);
        }
        return logic.mkAnd(std::move(args));
    }

    bool operator==(CartesianPredicateAbstractionStates const & other) {
        assert(&other.manager == &this->manager);
        return this->satisfiedPredicates == other.satisfiedPredicates;
    }

    bool operator!=(CartesianPredicateAbstractionStates const & other) { return not(*this == other); }

private:
    friend class ARG;
    void refine(PredicateAbstractionManager::Predicates const & newPredicates) {
        satisfiedPredicates.insert(newPredicates.begin(), newPredicates.end());
    }
};

struct ARGNode {
    SymRef predicateSymbol;
    std::unique_ptr<CartesianPredicateAbstractionStates> reachedStates;
    [[nodiscard]] PTRef getReachedStates() const { return reachedStates->asSingleFormula(); };
};

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
    std::unordered_map<NodeId, NodeId> coveredNodes; // coveree -> coverer

public:
    constexpr static NodeId ENTRY = 0;

    explicit ARG(ChcDirectedHyperGraph const & clauses) : clauses(clauses), predicateManager(clauses.getLogic()) {
        auto symbols = clauses.getVertices();
        for (auto predicateSymbol : symbols) {
            instances.emplace(predicateSymbol, std::vector<NodeId>{});
        }
        predicateManager.initialize(symbols);
    }

    [[nodiscard]] PTRef getReachedStates(NodeId id) const { return nodes[id].getReachedStates(); }

    [[nodiscard]] SymRef getPredicateSymbol(NodeId id) const { return nodes[id].predicateSymbol; }

    [[nodiscard]] PTRef getClauseConstraint(EId eid) const { return clauses.getEdgeLabel(eid); }

    /// Returns the ID of the new node with the given symbol and predicates and bool flag indicating if this new node
    /// is covered (subsumed) by an existing node in ARG
    /// NOTE: Currently we check exact match, this can be improved with subsumption
    std::pair<NodeId, bool> tryInsertNode(SymRef symbol, PredicateAbstractionManager::Predicates && predicates) {
        ARGNode node{symbol,
                     std::make_unique<CartesianPredicateAbstractionStates>(predicateManager, std::move(predicates))};
        auto & existingInstances = instances.at(symbol);
        auto it = std::find_if(existingInstances.begin(), existingInstances.end(),
                               [&](NodeId id) { return *nodes[id].reachedStates == *node.reachedStates; });
        bool covered = it != existingInstances.end();
        auto id = nodes.size();
        nodes.push_back(std::move(node));
        TRACE(1, "Creating new node " + std::to_string(id) + " for symbol " + clauses.getLogic().printSym(symbol))
        if (covered) { coveredNodes.emplace(id, *it); }
        existingInstances.push_back(id);
        return {id, covered};
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

    [[nodiscard]] std::vector<Edge> const & getIncomingEdges(NodeId target) const {
        assert(incomingEdges.count(target));
        return incomingEdges.at(target);
    }

    [[nodiscard]] auto const & getInstancesFor(SymRef symbol) const {
        auto it = instances.find(symbol);
        assert(it != instances.end());
        return it->second;
    }

    [[nodiscard]] auto const & getPredicatesFor(SymRef symbol) const { return predicateManager.predicatesFor(symbol); }

    [[nodiscard]] auto const & getClauses() const { return clauses; }

    void refine(std::unordered_map<SymRef, std::vector<PTRef>, SymRefHash> const & refinementInfo);

    std::vector<NodeId> recheckCoveredNodes();

    bool isCovered(NodeId nodeId) const { return coveredNodes.count(nodeId) > 0; }
};

struct UnprocessedEdge {
    EId eid;
    std::vector<ARG::NodeId> sources;
};

bool operator==(UnprocessedEdge const & first, UnprocessedEdge const & second) {
    return first.eid == second.eid and first.sources == second.sources;
}

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
    NodeId rootId{0};

    explicit InterpolationTree() {}

    NodeId createNode(NodeId parent, EId clauseId) {
        Node node{.id = nodes.size(), .parent = parent, .children = {}, .label = PTRef_Undef, .clauseId = clauseId};
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
    explicit EdgeQueue(ChcDirectedHyperGraph const & clauses);
    void addEdge(UnprocessedEdge e);
    UnprocessedEdge pop();
    [[nodiscard]] bool isEmpty() const;
    void clear();
    [[nodiscard]] std::size_t size() const { return queue.size(); }

    [[nodiscard]] bool has(UnprocessedEdge const & edge) const; // TODO: Should not be needed!

private:
    ChcDirectedHyperGraph const & clauses;
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
        : clauses(clauses), computeWitness(computeWitness),
          representation(AdjacencyListsGraphRepresentation::from(clauses)), queue(clauses), arg{clauses} {
        auto [nodeId, covered] = arg.tryInsertNode(clauses.getEntry(), PredicateAbstractionManager::Predicates{});
        assert(not covered);
        assert(nodeId == ARG::ENTRY);
        auto facts = representation.getOutgoingEdgesFor(clauses.getEntry());
        for (EId fact : facts) {
            queue.addEdge({.eid = fact, .sources = {nodeId}});
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

namespace {
void increment(std::vector<std::size_t> & indices, std::vector<std::vector<ARG::NodeId>> const & allInstances) {
    assert(not indices.empty());
    for (int i = static_cast<int>(indices.size()) - 1; /* stopping condition in the body*/; --i) {
        ++indices[i];
        if (indices[i] == allInstances[i].size() and i > 0) {
            indices[i] = 0;
        } else {
            break;
        }
    }
}
} // namespace

/*********** MAIN algorithm ****************/

VerificationResult Algorithm::run() {
    while (not queue.isEmpty()) {
        auto nextEdge = queue.pop();
        EId originalEdge = nextEdge.eid;
        if (clauses.getEdge(originalEdge).to == clauses.getExit()) {
            if (isRealProof(nextEdge)) { return VerificationResult{VerificationAnswer::UNSAFE, witness}; }
            refine();
            continue;
        }
        auto [id, isCovered] = computeTarget(nextEdge);
        auto before = queue.size();
        if (not isCovered) { computeNewUnprocessedEdges(id); }
        auto after = queue.size();
        TRACE(1, "Added " + std::to_string(after - before) + " new edges to process")
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
        PTRef predicate = logic.getPterm(sourcePredicate).size() > 0
                              ? VersionManager(logic).sourceFormulaToBase(sourcePredicate)
                              : sourcePredicate;
        definitions.emplace(predicate, definition);
    }
    return VerificationResult{VerificationAnswer::SAFE, ValidityWitness(std::move(definitions))};
}

void Algorithm::computeNewUnprocessedEdges(ARG::NodeId nodeId) {
    struct Checker {
        Logic & logic;
        SMTSolver solver;
        ARG const & arg;

        Checker(PTRef edgeConstraint, Logic & logic, ARG const & arg)
            : logic(logic), solver(logic, SMTSolver::WitnessProduction::NONE), arg(arg) {
            solver.assertProp(edgeConstraint);
        }

        bool isFeasible(std::vector<ARG::NodeId> const & sources) {
            solver.push();
            std::unordered_map<SymRef, int, SymRefHash> sourceCounts;
            VersionManager versionManager{logic};
            for (auto sourceId : sources) {
                PTRef reachedStates = arg.getReachedStates(sourceId);
                PTRef versionedStates =
                    versionManager.baseFormulaToSource(reachedStates, sourceCounts[arg.getPredicateSymbol(sourceId)]++);
                solver.assertProp(versionedStates);
            }
            auto res = solver.check();
            bool infeasible = res == SMTSolver::Answer::UNSAT;
            solver.pop();
            return not infeasible;
        }
    };

    auto const & candidateClauses = representation.getOutgoingEdgesFor(arg.getPredicateSymbol(nodeId));
    // TODO: We may get the same edge multiple times if the predicate symbol appears multiple times in the body
    for (EId edge : candidateClauses) {
        // find all instances of edge sources in ARG and check feasibility
        auto sources = clauses.getSources(edge);
        std::vector<std::vector<ARG::NodeId>> allInstances;
        std::transform(std::begin(sources), std::end(sources), std::back_inserter(allInstances),
                       [&](auto symbol) { return arg.getInstancesFor(symbol); });
        if (std::any_of(allInstances.begin(), allInstances.end(),
                        [](auto const & nodeInstances) { return nodeInstances.empty(); })) {
            continue;
        }
        std::vector<std::size_t> indices(sources.size(), 0u);
        Checker checker(clauses.getEdgeLabel(edge), clauses.getLogic(), arg);
        for (; indices[0] != allInstances[0].size(); increment(indices, allInstances)) {
            std::vector<ARG::NodeId> argSources;
            for (std::size_t i = 0; i < indices.size(); ++i) {
                argSources.push_back(allInstances[i][indices[i]]);
            }
            if (std::find(argSources.begin(), argSources.end(), nodeId) == argSources.end()) { continue; }
            if (std::any_of(argSources.begin(), argSources.end(), [&](auto nodeId) { return arg.isCovered(nodeId); })) {
                continue;
            }
            UnprocessedEdge newEdge{.eid = edge, .sources = std::move(argSources)};
            if (not queue.has(newEdge) and checker.isFeasible(argSources)) { queue.addEdge(std::move(newEdge)); }
        }
    }
}

std::pair<ARG::NodeId, bool> Algorithm::computeTarget(const UnprocessedEdge & edge) {
    Logic & logic = clauses.getLogic();
    VersionManager versionManager{logic};
    std::unordered_map<SymRef, int, SymRefHash> sourcesCount;
    SMTSolver solver(logic, SMTSolver::WitnessProduction::NONE);
    solver.assertProp(clauses.getEdgeLabel(edge.eid));
    for (auto sourceId : edge.sources) {
        PTRef reachedStates = arg.getReachedStates(sourceId);
        PTRef versioned =
            versionManager.baseFormulaToSource(reachedStates, sourcesCount[arg.getPredicateSymbol(sourceId)]++);
        solver.assertProp(versioned);
    }
    auto target = clauses.getEdge(edge.eid).to;
    std::set<PTRef> impliedPredicates;
    for (PTRef predicate : arg.getPredicatesFor(target)) {
        solver.push();
        PTRef versionedPredicate = versionManager.baseFormulaToTarget(predicate);
        solver.assertProp(logic.mkNot(versionedPredicate));
        auto res = solver.check();
        if (res == SMTSolver::Answer::UNSAT) { impliedPredicates.insert(predicate); }
        solver.pop();
    }
    return arg.tryInsertNode(target, std::move(impliedPredicates));
}

bool Algorithm::isRealProof(UnprocessedEdge const & edge) {
    assert(clauses.getEdge(edge.eid).to == clauses.getExit());
    // build the formula/interpolation tree (DAG?)
    auto interpolationTree = InterpolationTree::make(arg, edge);
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

void Algorithm::refine() {
    TRACE(1, "Refining")
    arg.refine(lastRefinementInfo);
    // Nodes that were previously subsumed/covered might no longer be covered
    auto uncoveredNodes = arg.recheckCoveredNodes();
    for (auto nodeId : uncoveredNodes) {
        computeNewUnprocessedEdges(nodeId);
    }
}

void Algorithm::computeInvalidityWitness(InterpolationTree const & itpTree, Model & model) {
    Logic & logic = clauses.getLogic();
    std::unordered_map<InterpolationTree::NodeId, std::vector<std::size_t>> premiseMap;
    InvalidityWitness::Derivation derivation;
    using DerivationStep = InvalidityWitness::Derivation::DerivationStep;
    std::size_t stepIndex = 0;
    // First step is just true
    derivation.addDerivationStep({.index = stepIndex++,
                                  .premises = {},
                                  .derivedFact = logic.getTerm_true(),
                                  .clauseId = {static_cast<id_t>(-1)}});

    auto const & nodes = itpTree.getNodes();
    for (auto it = nodes.rbegin(); it != nodes.rend(); ++it) {
        auto const & node = *it;
        DerivationStep step;
        step.derivedFact = [&]() {
            PTRef nodeInstance = itpTree.getInstanceFor(node.id);
            auto vars = TermUtils(logic).predicateArgsInOrder(nodeInstance);
            vec<PTRef> varValues(static_cast<int>(vars.size()), PTRef_Undef);
            std::transform(vars.begin(), vars.end(), varValues.begin(), [&](PTRef var) { return model.evaluate(var); });
            return logic.insertTerm(logic.getSymRef(nodeInstance), std::move(varValues));
        }();
        step.index = stepIndex++;
        step.clauseId = node.clauseId;
        step.premises = tryGetValue(premiseMap, node.id).value_or(std::vector<std::size_t>{0});
        if (node.parent != InterpolationTree::NO_ID) {
            auto & parentPremises = premiseMap[node.parent];
            parentPremises.insert(parentPremises.begin(), step.index);
        }
        derivation.addDerivationStep(std::move(step));
    }
    witness.setDerivation(std::move(derivation));
}

/*********** END of MAIN algorithm ****************/

/*********** Interpolation tree *******************/

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
    std::vector<NodeId> stack{root};
    while (not stack.empty()) {
        NodeId current = stack.back();
        stack.pop_back();
        assert(current < nodes.size());
        auto const & node = nodes[current];
        TermUtils::substitutions_map substitutions;
        auto const & edge = clauses.getEdge(node.clauseId);
        assert((edge.from.size() == 1 and edge.from[0] == clauses.getEntry()) or
               edge.from.size() == node.children.size());
        if (auto target = edge.to; target != clauses.getExit()) {
            assert(nodeToSymbolInstance.count(current) > 0);
            PTRef predicateInstance = clauses.getNextStateVersion(target);
            PTRef nodeInstance = nodeToSymbolInstance.at(current);
            utils.mapFromPredicate(predicateInstance, nodeInstance, substitutions);
        }
        std::unordered_map<SymRef, int, SymRefHash> sourcesCounter;
        for (std::size_t i = 0; i < node.children.size(); ++i) {
            SymRef sourceSymbol = edge.from[i];
            assert(sourceSymbol != clauses.getEntry());
            PTRef predicateInstance = clauses.getStateVersion(sourceSymbol, sourcesCounter[sourceSymbol]++);
            auto symbolVersion = symbolEncountered[sourceSymbol]++;
            auto vars = utils.predicateArgsInOrder(predicateInstance);
            for (PTRef var : vars) {
                PTRef versionedVar = timeMachine.sendFlaThroughTime(timeMachine.getVarVersionZero(manager.toBase(var)),
                                                                    static_cast<int>(symbolVersion));
                auto [_, inserted] = substitutions.emplace(var, versionedVar);
                assert(inserted);
                (void)inserted;
            }
            PTRef nodePredicate = utils.varSubstitute(predicateInstance, substitutions);
            auto [_, inserted] = nodeToSymbolInstance.emplace(node.children[i], nodePredicate);
            assert(inserted);
            (void)inserted;
        }
        PTRef defaultConstraint = edge.fla.fla;
        // Deal with auxiliary variables which need to be versioned, because same constraint can be present multiple
        // times in the ITP tree
        auto auxVars = matchingSubTerms(logic, defaultConstraint, [&](PTRef term) {
            return logic.isVar(term) and substitutions.find(term) == substitutions.end();
        });
        if (auxVars.size() > 0) {
            for (PTRef var : auxVars) {
                assert(not timeMachine.isVersioned(var));
                PTRef versionZero = timeMachine.getVarVersionZero(var);
                substitutions.insert({var, timeMachine.sendVarThroughTime(versionZero, static_cast<int>(current))});
            }
        }
        PTRef versionedConstraint = utils.varSubstitute(defaultConstraint, substitutions);
        setLabel(current, versionedConstraint);
        for (NodeId childId : node.children) {
            stack.push_back(childId);
        }
    }
}

InterpolationTree::Result InterpolationTree::solve(Logic & logic) const {
    SMTSolver solver(logic, SMTSolver::WitnessProduction::MODEL_AND_INTERPOLANTS);
    for (auto const & node : nodes) {
        assert(node.parent == InterpolationTree::NO_ID or node.id > node.parent);
        solver.assertProp(node.label);
    }
    auto res = solver.check();
    if (res == SMTSolver::Answer::SAT) {
        return InterpolationTree::Result{.model = solver.getModel(), .interpolant = {}};
    }

    if (res != SMTSolver::Answer::UNSAT) { throw std::logic_error("Solver could not return answer!"); }
    auto itpContext = solver.getInterpolationContext();
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

/*********** END of Interpolation tree ************/

namespace {
bool computeWitness(Options const & options) {
    return options.hasOption(Options::COMPUTE_WITNESS) and options.getOption(Options::COMPUTE_WITNESS) == "true";
}

class AuxCleanupPass : public Transformer {
public:
    struct BackTranslator : public WitnessBackTranslator {
        InvalidityWitness translate(InvalidityWitness witness) override { return witness; }
        ValidityWitness translate(ValidityWitness witness) override { return witness; }
    };

    TransformationResult transform(std::unique_ptr<ChcDirectedHyperGraph> graph) override {
        Logic & logic = graph->getLogic();
        TermUtils utils(logic);
        std::size_t auxVarCounter = 0;
        graph->forEachEdge([&](auto & edge) {
            PTRef & constraint = edge.fla.fla;
            vec<PTRef> predicateVars;
            // vars from head
            {
                auto headVars = utils.predicateArgsInOrder(graph->getNextStateVersion(edge.to));
                for (PTRef var : headVars) {
                    assert(logic.isVar(var));
                    predicateVars.push(var);
                }
            }
            // TODO: Implement a helper to iterate over source vertices together with instantiation counter
            std::unordered_map<SymRef, std::size_t, SymRefHash> instanceCounter;
            for (auto source : edge.from) {
                PTRef sourcePredicate = graph->getStateVersion(source, instanceCounter[source]++);
                for (PTRef var : utils.predicateArgsInOrder(sourcePredicate)) {
                    assert(logic.isVar(var));
                    predicateVars.push(var);
                }
            }
            constraint = TrivialQuantifierElimination(logic).tryEliminateVarsExcept(predicateVars, constraint);
            auto isVarToNormalize = [&](PTRef var) {
                return logic.isVar(var) and
                       std::find(predicateVars.begin(), predicateVars.end(), var) == predicateVars.end();
            };
            auto localVars = matchingSubTerms(logic, constraint, isVarToNormalize);
            if (localVars.size() > 0) {
                TermUtils::substitutions_map subst;
                for (PTRef localVar : localVars) {
                    SRef sort = logic.getSortRef(localVar);
                    std::string uniq_name = "paux#" + std::to_string(auxVarCounter++);
                    PTRef renamed = logic.mkVar(sort, uniq_name.c_str());
                    subst.insert({localVar, renamed});
                }
                constraint = utils.varSubstitute(constraint, subst);
            }
        });

        return {std::move(graph), std::make_unique<BackTranslator>()};
    }
};
} // namespace

VerificationResult ARGBasedEngine::solve(const ChcDirectedHyperGraph & graph) {
    auto graphCopy = std::make_unique<ChcDirectedHyperGraph>(graph);
    AuxCleanupPass pass;
    auto cleanedGraph = pass.transform(std::move(graphCopy));
    return Algorithm(*cleanedGraph.first, computeWitness(options)).run();
}

EdgeQueue::EdgeQueue(const ChcDirectedHyperGraph & clauses) : clauses(clauses) {}

bool EdgeQueue::isEmpty() const {
    return queue.empty();
}

void EdgeQueue::addEdge(UnprocessedEdge e) {
    TRACE(1, "Adding new edge to queue, with clause ID " + std::to_string(e.eid.id))
    if (clauses.getExit() == clauses.getTarget(e.eid)) {
        queue.push_front(std::move(e));
    } else {
        queue.push_back(std::move(e));
    }
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

bool EdgeQueue::has(const UnprocessedEdge & edge) const {
    return std::find(queue.begin(), queue.end(), edge) != queue.end();
}

void ARG::refine(std::unordered_map<SymRef, std::vector<PTRef>, SymRefHash> const & refinementInfo) {
    for (auto && [predicateSymbol, newPredicates] : refinementInfo) {
        for (PTRef newPredicate : newPredicates) {
            predicateManager.addPredicate(predicateSymbol, newPredicate);
        }
    }
    // Regenerate ARG
    // We check the nodes in order such that all predecessors are checked before the successor.
    // Since we add nodes as they are created, this condition is guaranteed in ARG::nodes
    for (NodeId nid = 0; nid != nodes.size(); ++nid) {
        auto const & node = nodes[nid];
        if (refinementInfo.count(node.predicateSymbol) == 0) { continue; }
        auto const & edges = getIncomingEdges(nid);
        if (edges.size() != 1) { throw std::logic_error{"This approach works only for single incoming edge!"}; }
        // TODO: Unify with ARG::computeTarget
        auto const & edge = edges[0];
        Logic & logic = clauses.getLogic();
        VersionManager versionManager{logic};
        std::unordered_map<SymRef, int, SymRefHash> sourcesCount;
        SMTSolver solver(logic, SMTSolver::WitnessProduction::NONE);
        solver.assertProp(clauses.getEdgeLabel(edge.clauseId));
        for (auto sourceId : edge.sources) {
            PTRef reachedStates = getReachedStates(sourceId);
            PTRef versioned =
                versionManager.baseFormulaToSource(reachedStates, sourcesCount[getPredicateSymbol(sourceId)]++);
            solver.assertProp(versioned);
        }
        auto target = clauses.getEdge(edge.clauseId).to;
        assert(target == node.predicateSymbol);
        std::set<PTRef> impliedPredicates;
        for (PTRef predicate : refinementInfo.at(target)) {
            solver.push();
            PTRef versionedPredicate = versionManager.baseFormulaToTarget(predicate);
            solver.assertProp(logic.mkNot(versionedPredicate));
            auto res = solver.check();
            if (res == SMTSolver::Answer::UNSAT) { impliedPredicates.insert(predicate); }
            solver.pop();
        }
        node.reachedStates->refine(impliedPredicates);
    }
}

std::vector<ARG::NodeId> ARG::recheckCoveredNodes() {
    std::vector<ARG::NodeId> uncoveredNodes;
    for (auto & nodePair : coveredNodes) {
        auto & coveree = nodePair.first;
        auto & coverer = nodePair.second;
        if (*nodes[coveree].reachedStates == *nodes[coverer].reachedStates) { continue; }
        auto const & symbolInstances = instances.at(nodes[coveree].predicateSymbol);
        auto it = std::find_if(symbolInstances.begin(), symbolInstances.end(), [&](NodeId other) {
            return other != coveree and coveredNodes.count(other) == 0 and
                   *nodes[other].reachedStates == *nodes[coveree].reachedStates;
        });
        if (it != symbolInstances.end()) {
            TRACE(1, "Found other coverer")
            coverer = *it;
            continue;
        }
        uncoveredNodes.push_back(coveree);
    }
    for (auto nodeId : uncoveredNodes) {
        coveredNodes.erase(nodeId);
    }
    return uncoveredNodes;
}