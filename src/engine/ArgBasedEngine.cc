/*
 * Copyright (c) 2024, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "ArgBasedEngine.h"

#include "utils/SmtSolver.h"

struct ARGNode {
    Vertex vertex;
    PTRef reachedStates;
};

inline bool operator==(ARGNode n1, ARGNode n2) { return n1.reachedStates == n2.reachedStates and n1.vertex.id == n2.vertex.id; }

struct ARGNodeHasher {
    std::size_t operator()(ARGNode const & node) const {
        std::hash<std::size_t> hasher;
        std::size_t res = 0;
        res ^= hasher(node.vertex.predicateSymbol.x) + 0x9e3779b9 + (res<<6) + (res>>2);
        res ^= hasher(node.reachedStates.x) + 0x9e3779b9 + (res<<6) + (res>>2);
        return res;
    }
};

struct ARGEdge {
    std::vector<ARGNode> sources;
    ARGNode target;
    EId clauseId;
};

struct ARG {
    std::unordered_set<ARGNode, ARGNodeHasher> nodes;
    std::unordered_map<SymRef, std::vector<ARGNode>, SymRefHash> instances;

    bool hasNode(ARGNode node) { return nodes.find(node) != nodes.end(); }
    void addNode(ARGNode node) {
        auto [_, inserted] = nodes.insert(node); assert(inserted); (void)inserted;
        auto predicate = node.vertex.predicateSymbol;
        auto it = instances.find(predicate);
        if (it == instances.end()) { auto res = instances.emplace(predicate, std::vector<ARGNode>{}); it = res.first; }
        it->second.push_back(node);
    }

    void addEdge(ARGEdge edge);

    std::vector<ARGNode> getNodesFor(SymRef predicate) {
        auto it = instances.find(predicate);
        assert(it != instances.end());
        return it->second;
    }
};

struct UnprocessedEdge {
    EId eid;
    std::vector<ARGNode> sources;
};

struct EdgeQueue {
    void addEdge(UnprocessedEdge e);
    UnprocessedEdge pop();
    bool isEmpty() const;
};

class Algorithm {
    ChcDirectedHyperGraph const & clauses;
    AdjacencyListsGraphRepresentation representation;
    EdgeQueue queue;
    ARG arg;

public:
    explicit Algorithm(ChcDirectedHyperGraph const & clauses) : clauses(clauses), representation{AdjacencyListsGraphRepresentation::from(clauses)} {
        auto facts = representation.getOutgoingEdgesFor(clauses.getEntry());
        for (EId fact : facts) {
            queue.addEdge({.eid = fact, .sources = {} });
        }
    }

    VerificationResult run();

private:
    void computeNewUnprocessedEdges(ARGNode node);
    ARGNode computeNewNode(UnprocessedEdge const & edge);
};

namespace{
void increment(std::vector<std::size_t> & indices, std::vector<std::vector<ARGNode>> const & allInstances) {
    assert(not indices.empty());
    for (int i = indices.size() - 1; ; --i) {
        ++indices[i];
        if (indices[i] == allInstances[i].size() and i > 0) { indices[i] = 0; }
        else {break;}
    }
}
}

void Algorithm::computeNewUnprocessedEdges(ARGNode node) {
    struct Checker {
        PTRef edgeConstraint;
        Logic & logic;
        SMTSolver solver;

        explicit Checker(PTRef edgeConstraint, Logic & logic)
            : edgeConstraint(edgeConstraint),
              logic(logic),
              solver(logic, SMTSolver::WitnessProduction::NONE) {
            solver.getCoreSolver().insertFormula(edgeConstraint);
        }

        bool isFeasible(std::vector<ARGNode> const & sources) {
            solver.getCoreSolver().push();
            for (auto const & source : sources) {
                // FIXME: Versioning!
                solver.getCoreSolver().insertFormula(source.reachedStates);
            }
            auto res = solver.getCoreSolver().check();
            bool infeasible = res == s_False;
            solver.getCoreSolver().pop();
            return not infeasible;
        }
    };

    auto const & candidateEdges = representation.getOutgoingEdgesFor(node.vertex.predicateSymbol);
    for (EId edge : candidateEdges) {
        // find all instances of edge sources in ARG and check feasibility
        auto sources = clauses.getSources(edge);
        std::vector<std::vector<ARGNode>> allInstances;
        std::transform(std::begin(sources), std::end(sources), std::back_inserter(allInstances), [&](auto node) { return arg.getNodesFor(node);});
        std::vector<std::size_t> indices;
        std::transform(std::begin(allInstances), std::end(allInstances), std::back_inserter(indices), [](auto const &) { return 0u;});
        Checker checker(clauses.getEdgeLabel(edge), clauses.getLogic());
        for (; indices[0] != allInstances[0].size(); increment(indices, allInstances)) {
            std::vector<ARGNode> argSources;
            for (std::size_t i = 0; i < indices.size(); ++i) {
                argSources.push_back(allInstances[i][indices[i]]);
            }
            if (checker.isFeasible(argSources)) {
                queue.addEdge({.eid = edge, .sources = std::move(argSources)});
            }
        }
    }
}

ARGNode Algorithm::computeNewNode(const UnprocessedEdge & edge) {
    throw std::logic_error("Not implemented yet!");
}

VerificationResult Algorithm::run() {
    while (not queue.isEmpty()) {
        auto nextEdge = queue.pop();
        EId originalEdge = nextEdge.eid;
        if (clauses.getEdge(originalEdge).to == clauses.getExit()) {
            if (isRealProof(nextEdge)) {
                return VerificationResult{VerificationAnswer::UNSAFE};
            }
            refine();
            continue;
        }
        ARGNode newNode = computeNewNode(nextEdge);
        if (not arg.hasNode(newNode)) {
            arg.addNode(newNode);
            computeNewUnprocessedEdges(newNode);
        }
        arg.addEdge(ARGEdge{.sources = std::move(nextEdge.sources), .target = newNode, .clauseId = nextEdge.eid});
    }

    return VerificationResult{VerificationAnswer::SAFE};
}

VerificationResult ARGBasedEngine::solve(const ChcDirectedHyperGraph & graph) {
    return Algorithm(graph).run();
}