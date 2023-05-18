/*
 * Copyright (c) 2020-2022, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "Lawi.h"

#include <functional>
#include <optional>

namespace{

class ArtPath {
    struct PathSegment {
        EId edge;
        PTRef fla;
    };
    std::vector<PathSegment> segments;
public:
    vec<PTRef> getEdgeFormulas() const {
        vec<PTRef> edgeFlas;
        for (auto const & segment : segments) {
            edgeFlas.push(segment.fla);
        }
        return edgeFlas;
    }

    std::vector<EId> getEdges() const {
        std::vector<EId> edges;
        for (auto const & segment : segments) {
            edges.push_back(segment.edge);
        }
        return edges;
    }

    void addPathSegment(EId eid, PTRef fla) {
        segments.push_back(PathSegment{eid, fla});
    }

    std::size_t size() const {
        return segments.size();
    }
};

class AbstractReachabilityTree {
private:
	struct Edge {
		VId from;
		VId to;
	};
    ChcDirectedGraph const & graph;
    AdjacencyListsGraphRepresentation graphRepresentation;

    VId root;
    std::map<VId, SymRef> toOriginalLoc;
    std::map<EId, EId> toOriginalEdge;
    std::size_t vertexCount = 0;
    VId getNewVertex() { return VId{vertexCount++}; }

	std::vector<Edge> edges;
    std::map<VId, std::vector<EId>> childrenOf;
    std::map<VId, EId> parentOf;


public:
    AbstractReachabilityTree(ChcDirectedGraph const& graph)
        : graph(graph), graphRepresentation(AdjacencyListsGraphRepresentation::from(graph)) {
        root = getNewVertex();
        toOriginalLoc.insert({root, graph.getEntry()});
    }

    bool isErrorLocation(VId vertex) const { return getOriginalLocation(vertex) == getOriginalErrorLocation(); }
    bool sameLocation(VId v1, VId v2) const { return getOriginalLocation(v1) == getOriginalLocation(v2); }

    bool isAncestor(VId ancestor, VId descendant) const;

    void fillDescendantsRecusively(VId vertex, std::vector<VId> & descendants) const;
    std::vector<VId> getDescendantsOfIncluding(VId vertex) const;
    std::vector<VId> getAncestorsOfIncluding(VId vertex) const;
    std::vector<VId> getAncestorsOfUntil(VId vertex, VId stop) const;
    std::vector<VId> getAncestorsOfExcluding(VId vertex) const;
	std::vector<EId> getAncestorPathUntil(VId vertex, VId stop) const;
    std::vector<VId> getChildrenOf(VId vertex) const;
	std::vector<EId> getOutEdgesOf(VId vertex) const;
    std::vector<VId> getEarlierForSameLocationAs(VId vertex) const;
    std::vector<VId> getEarlierForSameLocationAs(VId vertex, size_t limit) const;
    bool isLeaf(VId vertex) const { return getChildrenOf(vertex).empty(); }

    std::vector<VId> expand(VId vertex);

    // Path goes in the direction from root to leaves
    ArtPath getPathFromInit(VId vertex, Logic & logic) const;
    ArtPath getPath(VId descendant, VId ancestor , Logic & logic) const;
    std::vector<VId> getPathVertices(ArtPath const & path) const;
	std::vector<VId> getPathVertices(std::vector<EId> const & path) const;

    VId getRoot() const { return root; }

    SymRef getOriginalLocation(VId vertex) const { assert(toOriginalLoc.count(vertex) != 0); return toOriginalLoc.at(vertex); }
	EId getOriginalEdge(EId eid) const { assert(toOriginalEdge.count(eid) != 0); return toOriginalEdge.at(eid); }

    void traverse(std::function<void(VId)> fun) const;

    VId nearestCommonAncestor(VId id, VId id1) const;

	PTRef getLabel(EId eid) const;
	VId getSource(EId eid) const;
	VId getTarget(EId eid) const;

private:
    // helpers
    void connect(VId from, VId to, EId originalEdge) {
        EId eid{edges.size()};
        edges.push_back(Edge{from, to});
        toOriginalEdge.insert({eid, originalEdge});
        auto it = childrenOf.find(from);
        if (it == childrenOf.end()) {
            childrenOf.insert({from, std::vector<EId>{eid}});
        } else {
            it->second.push_back(eid);
        }
        parentOf.insert({to, eid});
    }

    SymRef getOriginalErrorLocation() const { return graph.getExit(); };

    VId newVertexFor(SymRef originalLocation) {
        VId nv = getNewVertex();
        toOriginalLoc.insert({nv, originalLocation});
        return nv;
    }

};

class CoveringRelation {
public:
    struct RelElement{
        VId coveree;
        VId coverer;

        bool operator==(CoveringRelation::RelElement const & other) const {
            return this->coverer == other.coverer && this->coveree == other.coveree;
        }
    };
private:
    using rel_t = std::vector<RelElement>;
    // (v,w) \in inner <=> "v is covered by w (directly)" (Lab(v) \implies Lab(w))
    rel_t elements;

    AbstractReachabilityTree const & art;

    std::vector<VId> getDescendantsInclusive(VId vertex) const { return art.getDescendantsOfIncluding(vertex); }
    std::vector<VId> getAncestorsInclusive(VId vertex) const { return art.getAncestorsOfIncluding(vertex); }

public:
    CoveringRelation(AbstractReachabilityTree const & art) : art(art) {}

    bool isCovered(VId vertex) const;

    void updateWith(RelElement nElem);

    void vertexStrengthened(VId vertex);

private:
};

class LabelingFunction {
    std::map<VId, PTRef> labels;
public:
    PTRef getLabel(VId vertex) const {
        assert(labels.count(vertex) != 0);
        return labels.at(vertex);
    }

    void addLabel(VId vertex, PTRef label) {
        assert(labels.count(vertex) == 0);
        labels.insert({vertex, label});
    }

    void replaceLabel(VId vertex, PTRef label) {
        auto it = labels.find(vertex);
        assert(it != labels.end());
        it->second = label;

    }
};


class ImplicationChecker {
public:
    enum class QueryResult {VALID, INVALID, ERROR, UNKNOWN};

    ImplicationChecker(Logic & logic) : logic(logic) {}
    QueryResult checkImplication(PTRef antecedent, PTRef consequent) {
        if (antecedent == consequent || antecedent == logic.getTerm_false() || consequent == logic.getTerm_true()) {
            return QueryResult::VALID;
        }
        if (antecedent == logic.getTerm_true() || consequent == logic.getTerm_false()) {
            return QueryResult::INVALID;
        }
        auto pair = std::make_pair(antecedent, consequent);
        auto it = cache.find(pair);
        if (it != cache.end()) {
            return it->second;
        }
        SMTConfig config;
        MainSolver solver(logic, config, "implication_checker");
        PTRef negImpl = logic.mkAnd(antecedent, logic.mkNot(consequent)); // not(A->B) iff A and (not B)
//        std::cout << logic.printTerm(negImpl) << std::endl;
        solver.insertFormula(negImpl);
        auto res = solver.check();
        if (res == s_True) {
            cache.insert({pair, QueryResult::INVALID});
            return QueryResult::INVALID;
        }
        if (res == s_False) {
            cache.insert({pair, QueryResult::VALID});
            return QueryResult::VALID;
        }
        if (res == s_Undef) {
            return QueryResult::UNKNOWN;
        }
        if (res == s_Error) {
            return QueryResult::ERROR;
        }
        assert(false);
        throw std::logic_error("Unreachable code!");
    }

    QueryResult checkImplicationWithHints(PTRef antecedent, PTRef consequent, std::vector<std::unique_ptr<Model>>& antecedentModels) {
        if (antecedent == consequent || antecedent == logic.getTerm_false() || consequent == logic.getTerm_true()) {
            return QueryResult::VALID;
        }
        if (antecedent == logic.getTerm_true() || consequent == logic.getTerm_false()) {
            return QueryResult::INVALID;
        }
        auto pair = std::make_pair(antecedent, consequent);
        auto it = cache.find(pair);
        if (it != cache.end()) {
            return it->second;
        }
        for (auto const& model : antecedentModels) {
            assert(model->evaluate(antecedent) == logic.getTerm_true());
            if (model->evaluate(consequent) == logic.getTerm_false()) {
                cache.insert({pair, QueryResult::INVALID});
                return QueryResult::INVALID;
            }
        }
        SMTConfig config;
        MainSolver solver(logic, config, "implication_checker");
        PTRef negImpl = logic.mkAnd(antecedent, logic.mkNot(consequent)); // not(A->B) iff A and (not B)
//        std::cout << logic.printTerm(negImpl) << std::endl;
        solver.insertFormula(negImpl);
        auto res = solver.check();
        if (res == s_True) {
            cache.insert({pair, QueryResult::INVALID});
            antecedentModels.push_back(solver.getModel());
            return QueryResult::INVALID;
        }
        if (res == s_False) {
            cache.insert({pair, QueryResult::VALID});
            return QueryResult::VALID;
        }
        if (res == s_Undef) {
            return QueryResult::UNKNOWN;
        }
        if (res == s_Error) {
            return QueryResult::ERROR;
        }
        assert(false);
        throw std::logic_error("Unreachable code!");
    }

private:
    Logic & logic;
    std::unordered_map<std::pair<PTRef, PTRef>, QueryResult, PTRefPairHash> cache;
};

class LawiContext{
    Logic & logic;
    ChcDirectedGraph const & graph;
    Options const & options;

    AbstractReachabilityTree art;
    LabelingFunction labels;
    CoveringRelation coveringRelation;
    ImplicationChecker implicationChecker;

    std::vector<VId> leavesToCheck;

    bool usingForcedCovering;
    std::size_t forceCoveringLimit = 1;

    ErrorPath errorPath;

    void removeLeaf(VId leaf) {
        leavesToCheck.erase(std::remove(leavesToCheck.begin(), leavesToCheck.end(), leaf), leavesToCheck.end());
    }

    std::vector<VId> getAncestorsOf(VId vertex) const { return art.getAncestorsOfExcluding(vertex); }
    std::vector<VId> getEarlierForSameLocationAs(VId vertex) const { return art.getEarlierForSameLocationAs(vertex); }
    void closeAllAncestors(VId vertex) {
        for (VId ancestor : getAncestorsOf(vertex)) {
            close(ancestor);
        }
    }

    using ImplicationCheckResult = ImplicationChecker::QueryResult;

    // Returns true if the implication holds, false otherwise
    ImplicationCheckResult checkImplication(PTRef antecedent, PTRef consequent) {
        return implicationChecker.checkImplication(antecedent, consequent);
    }

    ImplicationCheckResult checkImplicationWithHints(PTRef antecedent, PTRef consequent, std::vector<std::unique_ptr<Model>>& antecedentModels) {
        return implicationChecker.checkImplicationWithHints(antecedent, consequent, antecedentModels);
    }

    void expand(VId vertex);

    struct RefinementResult {
        VerificationAnswer verificationAnswer;
        std::vector<VId> refinedVertices;
    };

    RefinementResult refine(VId vertex);

    [[maybe_unused]]
    void cover(VId v, VId w);

    bool coverWithHints(VId v, VId w, std::vector<std::unique_ptr<Model>>& vModels);

    void close(VId vertex);

    VerificationAnswer DFS(VId vertex);

    std::optional<VId> getUncoveredLeaf();

    std::unique_ptr<SMTConfig> createInterpolatingConfig() const {
        SMTConfig * config = new SMTConfig();
        const char* msg = "ok";
//        config->setOption(SMTConfig::o_sat_pure_lookahead, SMTOption(true), msg);
        bool set = config->setOption(SMTConfig::o_sat_picky, SMTOption(true), msg);
//        config->setOption(SMTConfig::o_sat_picky_w, 1, msg);

//        config->setOption(SMTConfig::o_random_seed, SMTOption(526899046), msg);
        set = config->setOption(SMTConfig::o_produce_inter, SMTOption(true), msg);
        assert(set); (void)set;
        config->setSimplifyInterpolant(4);
        if (options.hasOption(Options::LRA_ITP_ALG)) {
            int algNumber = std::atoi(options.getOption(Options::LRA_ITP_ALG).c_str());
            config->setLRAInterpolationAlgorithm(ItpAlgorithm{algNumber});
        }
        return std::unique_ptr<SMTConfig>(config);
    }

    vec<PTRef> normalizeInterpolants(vec<PTRef> const & itps) const;

    std::vector<VId> strengthenLabelsAlongPath(const ArtPath & path, vec<PTRef> const & itps);

    bool useForcedCovering() const { return usingForcedCovering; }

    ErrorPath buildGraphPathFromTreePath(ArtPath const & path) const;
public:
    LawiContext(Logic & logic, ChcDirectedGraph const& graph, Options const & options)
        : logic(logic), graph(graph), options(options), art(graph), coveringRelation(art), implicationChecker(logic) {
        labels.addLabel(art.getRoot(), logic.getTerm_true());
        leavesToCheck.push_back(art.getRoot());
        usingForcedCovering = options.hasOption(Options::FORCED_COVERING);
    }

    VerificationResult unwind();

    vec<PTRef> getPathInterpolants(MainSolver & solver, ArtPath const &) const;

    void applyForcedCovering(VId vertex);
};

//
//  Implementation of the main methods
//

void LawiContext::close(VId vertex) {
    auto before = getEarlierForSameLocationAs(vertex);
    std::vector<std::unique_ptr<Model>> vertexModels;
    for (VId earlier : before) {
        if (not coveringRelation.isCovered(earlier)) {
            bool covered = coverWithHints(vertex, earlier, vertexModels);
            if (covered) { return; }
        }
    }
}


// Main method
VerificationResult LawiContext::unwind() {
    bool computeWitness = options.hasOption(Options::COMPUTE_WITNESS);
    auto optionalVertex = getUncoveredLeaf();
    while (optionalVertex.has_value()) {
        auto uncoveredVertex = optionalVertex.value();
        closeAllAncestors(uncoveredVertex);
        auto res = DFS(uncoveredVertex);
        if (res == VerificationAnswer::UNSAFE) {
            if (computeWitness) {
                return VerificationResult(VerificationAnswer::UNSAFE, InvalidityWitness::fromErrorPath(errorPath, graph));
            } else {
                return VerificationResult(VerificationAnswer::UNSAFE);
            }
        }
        optionalVertex = getUncoveredLeaf();
    }
    if (not computeWitness) { return VerificationResult(VerificationAnswer::SAFE); }
    // Solution found!
    // Map original locations to disjunction of labels of not covered vertices
    std::unordered_map<SymRef, std::vector<PTRef>, SymRefHash> finalLabels;
    art.traverse([&](VId vertex) {
        if (not coveringRelation.isCovered(vertex)) {
            auto originalLocation = art.getOriginalLocation(vertex);
            PTRef label = labels.getLabel(vertex);
            finalLabels[originalLocation].push_back(label);
        }
    });
    // computed interpretations
    std::unordered_map<PTRef, PTRef, PTRefHash> solution;
    for (auto vid : graph.getVertices()) {
        PTRef predicate = graph.getStateVersion(vid);
        if (logic.isTrue(predicate) || logic.isFalse(predicate)) { continue; }
        auto it = finalLabels.find(vid);
        const PTRef definition = [&]() {
            if (it == finalLabels.end()) {
               return logic.getTerm_false();
            }
            PTRef definition = logic.mkOr(it->second);
            if (logic.isOr(definition) or logic.isAnd(definition)) {
                definition = simplifyUnderAssignment_Aggressive(definition, logic);
            }
            return definition;
        }();
        auto insertRes = solution.insert(std::make_pair(predicate, definition));
        assert(insertRes.second);
        if (not insertRes.second) {
            throw std::logic_error("Duplicate definition for a predicate encountered!");
        }
    }
    return VerificationResult(VerificationAnswer::SAFE, ValidityWitness(std::move(solution)));
}

// Processing of a single leaf
VerificationAnswer LawiContext::DFS(VId vertex) {
    close(vertex);
    if (coveringRelation.isCovered(vertex)) {
        // this vertex is covered, no need to process
        return VerificationAnswer::UNKNOWN;
    }
    // if it is an error location, we need to check the path
    if (art.isErrorLocation(vertex)) {
        auto res = refine(vertex);
        if (res.verificationAnswer == VerificationAnswer::UNSAFE) { return VerificationAnswer::UNSAFE; }
        for (VId strengthened : res.refinedVertices) {
            close(strengthened);
        }
    }
    else {
        expand(vertex);
        auto children = art.getChildrenOf(vertex);
        // ensure the children are properly initialized
        for (VId child : children) {
            labels.addLabel(child, logic.getTerm_true());
            if (useForcedCovering()) {
                applyForcedCovering(child);
            }
        }
        // run on children in DFS manner
        for (VId child : children) {
            auto res = DFS(child);
            if (res == VerificationAnswer::UNSAFE) { return VerificationAnswer::UNSAFE; }
        }
    }
    return VerificationAnswer::UNKNOWN;
}

void LawiContext::applyForcedCovering(VId vertex) {
    auto earlierSameLocation = art.getEarlierForSameLocationAs(vertex, forceCoveringLimit);
    for (VId candidate : earlierSameLocation) {
        if (coveringRelation.isCovered(candidate)) {
            continue;
        }
        VId nca = art.nearestCommonAncestor(candidate, vertex);
        // check label of nca and path to child implies label of candidate
        auto path = art.getPath(nca, vertex, logic);
        auto edgeFormulas = path.getEdgeFormulas();
        auto config = createInterpolatingConfig();
        MainSolver solver(logic, *config, "forcedCoveringChecker");
        solver.insertFormula(labels.getLabel(nca));
//        std::cout << logic.printTerm(labels.getLabel(nca)) << std::endl;
        for (PTRef edge : edgeFormulas) {
            solver.insertFormula(edge);
//            std::cout << logic.printTerm(edge) << std::endl;
        }
        PTRef labelToTest = TimeMachine(logic).sendFlaThroughTime(labels.getLabel(candidate), edgeFormulas.size());
//        std::cout << logic.printTerm(labelToTest) << std::endl;
        solver.insertFormula(logic.mkNot(labelToTest));
//        PTRef fla = logic.mkAnd({labels.getLabel(nca), logic.mkAnd(edgeFormulas), logic.mkNot(labelToTest)});
//        std::cout << logic.printTerm(fla) << std::endl;
        auto res = solver.check();
        if (res == s_False) {
            // this vertex is covered by the candidate
            // compute interpolants, strenthen the labels
            auto edges = path.getEdges();
            assert(not edges.empty() && art.getSource(edges.front()) == nca && art.getTarget(edges.back()) == vertex);
            // Interpolation
            vec<PTRef> pathInterpolants = getPathInterpolants(solver, path);
            vec<PTRef> normalizedInterpolants = normalizeInterpolants(pathInterpolants);
            strengthenLabelsAlongPath(path, normalizedInterpolants);
            // Don't forget to update the label of the last vertex in the path
            assert(labels.getLabel(vertex) == logic.getTerm_true());
            labels.replaceLabel(vertex, labels.getLabel(candidate));
            break; // label has been propagated
        }
        // else, this label cannot be propagated, continue with other candidates
    }
}

void LawiContext::expand(VId vertex) {
    assert(art.isLeaf(vertex) && not coveringRelation.isCovered(vertex));
    auto children = art.expand(vertex);
    for (auto child : children) {
        leavesToCheck.push_back(child);
    }
    removeLeaf(vertex);
}

LawiContext::RefinementResult LawiContext::refine(VId errVertex) {
    assert(art.isErrorLocation(errVertex));
    ArtPath path = art.getPathFromInit(errVertex, logic);
    auto edgeFormulas = path.getEdgeFormulas();
    /*
     * 1. check satisfiability
     * 2. if SAT -> return UNSAFE
     * 3. INTERPOLATE
     * 4. normalize to current state formulas
     * 5. if not implied by current label -> strengthen label and potentially uncover vertices
     */
//    std::cout << "\nChecking path: " << logic.printTerm(logic.mkAnd(edgeFormulas)) << std::endl;
//    std::cout << "\nChecking path of length " << edgeFormulas.size() << std::endl;
    auto config = createInterpolatingConfig();
    MainSolver solver(logic, *config, "checker");
    for (PTRef segment : edgeFormulas) {
//    	std::cout << logic.printTerm(segment) << std::endl;
        solver.insertFormula(segment);
    }
    auto res = solver.check();
    if (res == s_True) {
        errorPath = buildGraphPathFromTreePath(path);
        return RefinementResult{VerificationAnswer::UNSAFE, {}};
    } else if (res == s_False) {
		auto edges = path.getEdges();
		assert(not edges.empty() and art.getSource(edges.front()) == this->art.getRoot()
			and art.isErrorLocation(art.getTarget(edges.back())));
        // Interpolation
        vec<PTRef> pathInterpolants = getPathInterpolants(solver, path);
        vec<PTRef> normalizedInterpolants = normalizeInterpolants(pathInterpolants);
        auto strengthened = strengthenLabelsAlongPath(path, normalizedInterpolants);
        // this vertex does not have to be considered anymore
        removeLeaf(errVertex);
        return RefinementResult{VerificationAnswer::UNKNOWN, std::move(strengthened)};
    } else {
        throw std::logic_error("Error in the SMT solver");
    }
}

vec<PTRef> LawiContext::getPathInterpolants(MainSolver & solver, ArtPath const & path) const {
    auto itpContext = solver.getInterpolationContext();
    vec<PTRef> pathInterpolants;
    auto pathSize = path.size();
    // Create the partitions manually, TODO: fix the OpenSMT interface so that calling just getPathInterpolants would work correctly
    ipartitions_t mask = 0;
    for (std::size_t i = 0; i < pathSize - 1; ++i) {
        opensmt::setbit(mask, i);
        itpContext->getSingleInterpolant(pathInterpolants, mask);
    }
    // MB: Last interpolant must be always false
    pathInterpolants.push(logic.getTerm_false());
    assert(pathInterpolants.size_() == pathSize);
    return pathInterpolants;
}

// 'coveree' can be covered by 'coverer'
void LawiContext::cover(VId coveree, VId coverer) {
    if (coveringRelation.isCovered(coveree) || not art.sameLocation(coveree, coverer)
        || art.isAncestor(coveree, coverer)) {
        return;
    }
    auto res = checkImplication(labels.getLabel(coveree), labels.getLabel(coverer));
    if (res == decltype(res)::VALID) {
        coveringRelation.updateWith({.coveree = coveree, .coverer = coverer});
        // if coveree was covering something, this must be removed
    }
}

bool LawiContext::coverWithHints(VId coveree, VId coverer, std::vector<std::unique_ptr<Model>>& covereeModels) {
    if (coveringRelation.isCovered(coveree)) { return true; }
    if (not art.sameLocation(coveree, coverer) || art.isAncestor(coveree, coverer)) { return false; }
    auto res = checkImplicationWithHints(labels.getLabel(coveree), labels.getLabel(coverer), covereeModels);
    if (res == decltype(res)::VALID) {
        coveringRelation.updateWith({.coveree = coveree, .coverer = coverer});
        return true;
    }
    return false;
}

void CoveringRelation::updateWith(CoveringRelation::RelElement nElem) {
    assert(std::find(elements.begin(), elements.end(), nElem) == elements.end());
    // descendants of covered vertex cannot cover anything anymore
    auto descendants = this->getDescendantsInclusive(nElem.coveree);
    elements.erase(std::remove_if(elements.begin(), elements.end(),
                                  [&descendants](CoveringRelation::RelElement const & elem) {
        return std::find(descendants.begin(), descendants.end(), elem.coverer) != descendants.end();
    }), elements.end());
    // add the new element of the relation
    elements.push_back(nElem);
}

bool CoveringRelation::isCovered(VId vertex) const {
    auto ancestors = this->getAncestorsInclusive(vertex);
    return std::any_of(ancestors.begin(), ancestors.end(), [this](VId ancestor) {
        return std::any_of(elements.begin(), elements.end(), [ancestor](const CoveringRelation::RelElement & elem) {
           return elem.coveree == ancestor;
        });
    });
}

void CoveringRelation::vertexStrengthened(VId vertex) {
    elements.erase(std::remove_if(elements.begin(), elements.end(), [vertex](CoveringRelation::RelElement const & elem) {
        return elem.coverer == vertex;
    }), elements.end());
}

std::vector<VId> AbstractReachabilityTree::expand(VId vertex) {
    assert(isLeaf(vertex));
    std::vector<VId> children;
    auto originalLocation = getOriginalLocation(vertex);
    // get all outgoing edges and create corresponding vertices in this ART
    auto outEdges = graphRepresentation.getOutgoingEdgesFor(originalLocation);
    std::partition(outEdges.begin(), outEdges.end(), [this](EId outEdge) {
        return graph.getTarget(outEdge) == getOriginalErrorLocation();
    });
    for (EId eid : outEdges) {
        auto successor = graph.getTarget(eid);
        VId nVertex = newVertexFor(successor);
        children.push_back(nVertex);
        connect(vertex, nVertex, eid);
    }
    return children;
}

bool AbstractReachabilityTree::isAncestor(VId ancestor, VId descendant) const {
    VId current = descendant;
    while (current != ancestor && current != root) {
        assert(parentOf.count(current) != 0);
        current = getSource(parentOf.at(current));
    }
    assert(current == ancestor || current == root);
    return current == ancestor;
}

void AbstractReachabilityTree::fillDescendantsRecusively(VId vertex, std::vector<VId> & descendants) const {
    descendants.push_back(vertex);
    auto children = getChildrenOf(vertex);
    for (VId child : children) {
        fillDescendantsRecusively(child, descendants);
    }
}

std::vector<VId> AbstractReachabilityTree::getDescendantsOfIncluding(VId vertex) const {
    std::vector<VId> res;
    fillDescendantsRecusively(vertex, res);
    return res;
}

std::vector<EId> AbstractReachabilityTree::getAncestorPathUntil(VId vertex, VId stop) const {
	std::vector<EId> path;
	VId current = vertex;
	while (current != stop) {
		assert(parentOf.count(current) != 0);
		EId eid = parentOf.at(current);
		path.push_back(eid);
		current = getSource(eid);
	}
	std::reverse(path.begin(), path.end());
	return path;
}

std::vector<VId> AbstractReachabilityTree::getAncestorsOfUntil(VId vertex, VId stop) const {
    std::vector<VId> ancestors = {vertex}; // Here we are including 'vertex'
    auto path = getAncestorPathUntil(vertex, stop);
    std::transform(path.begin(), path.end(), std::back_inserter(ancestors), [this](EId eid) { return getSource(eid); });
    return ancestors;
}

std::vector<VId> AbstractReachabilityTree::getAncestorsOfIncluding(VId vertex) const {
    return getAncestorsOfUntil(vertex, root);
}

std::vector<VId> AbstractReachabilityTree::getAncestorsOfExcluding(VId vertex) const {
    auto ancestorsIncluding = getAncestorsOfIncluding(vertex);
    ancestorsIncluding.erase(ancestorsIncluding.begin());
    return ancestorsIncluding;
}

std::vector<EId> AbstractReachabilityTree::getOutEdgesOf(VId vertex) const {
	auto it = childrenOf.find(vertex);
	if (it == childrenOf.end()) { return {}; }
	return childrenOf.at(vertex);
}

std::vector<VId> AbstractReachabilityTree::getChildrenOf(VId vertex) const {
    auto outEdges = getOutEdgesOf(vertex);
    std::vector<VId> children;
    std::transform(outEdges.begin(), outEdges.end(), std::back_inserter(children), [this](EId outEdge) { return this->edges[outEdge.id].to; });
    return children;
}

std::vector<VId> AbstractReachabilityTree::getEarlierForSameLocationAs(VId vertex, size_t limit) const {
    std::vector<VId> res;
    if (vertex.id == 0) { return res; }
    for (std::size_t id = vertex.id - 1; id > 0 && res.size() < limit; --id) {
        VId other{id};
        if (sameLocation(vertex, other)) {
            res.push_back(other);
        }
    }
    return res;
}

std::vector<VId> AbstractReachabilityTree::getEarlierForSameLocationAs(VId vertex) const {
    return getEarlierForSameLocationAs(vertex, std::numeric_limits<std::size_t>::max());
}

std::vector<VId> AbstractReachabilityTree::getPathVertices(const ArtPath & path) const {
	return getPathVertices(path.getEdges());
}

std::vector<VId> AbstractReachabilityTree::getPathVertices(const std::vector<EId> & eids) const {
	std::vector<VId> vertices;
	std::transform(eids.begin(), eids.end(), std::back_inserter(vertices), [this](EId eid) { return getSource(eid); });
	vertices.push_back(getTarget(eids.back()));
	return vertices;
}

ArtPath AbstractReachabilityTree::getPathFromInit(VId vertex, Logic & logic) const {
    return getPath(root, vertex, logic);
}

ArtPath AbstractReachabilityTree::getPath(VId predecessor, VId successor, Logic & logic) const {
    ArtPath artPath;
    std::vector<EId> path = getAncestorPathUntil(successor, predecessor);
    TimeMachine timeMachine(logic);
    for (std::size_t i = 0; i < path.size(); ++i) {
        EId eid = path[i];
        PTRef fla = getLabel(eid);
        fla = timeMachine.sendFlaThroughTime(fla, i);
        artPath.addPathSegment(eid, fla);
    }
    return artPath;
}

PTRef AbstractReachabilityTree::getLabel(EId eid) const {
    EId originalEdge = getOriginalEdge(eid);
    PTRef fla = graph.getEdgeLabel(originalEdge);
    return fla;
}

VId AbstractReachabilityTree::getSource(EId eid) const {
	return edges[eid.id].from;
}

VId AbstractReachabilityTree::getTarget(EId eid) const {
	return edges[eid.id].to;
}

void AbstractReachabilityTree::traverse(std::function<void(VId)> fun) const {
    auto all = getDescendantsOfIncluding(getRoot());
    for (VId vertex : all) {
        fun(vertex);
    }
}

VId AbstractReachabilityTree::nearestCommonAncestor(VId v1, VId v2) const {
    auto predecessors1 = getAncestorsOfIncluding(v1);
    VId nca = v2;
    auto isPredOfV1 = [&predecessors1](VId v) {
        return std::find(predecessors1.begin(), predecessors1.end(), v) != predecessors1.end();
    };
    while (nca != root) {
        if (isPredOfV1(nca)) { return nca; }
        nca = getSource(parentOf.at(nca));
    }
    assert(nca == root);
    return nca;

}

std::optional<VId> LawiContext::getUncoveredLeaf() {
    for (auto it = leavesToCheck.rbegin(); it != leavesToCheck.rend(); ++it) {
        VId vid = *it;
        assert(art.isLeaf(vid));
        if (not coveringRelation.isCovered(vid)) {
            return vid;
        }
    }
    return std::nullopt;
}

vec<PTRef> LawiContext::normalizeInterpolants(const vec<PTRef> & itps) const {
    vec<PTRef> normalized;
    TimeMachine timeMachine(logic);
    for (int i = 0; i < itps.size(); ++i) {
        normalized.push(timeMachine.sendFlaThroughTime(itps[i], -(i+1)));
    }
    return normalized;
}

std::vector<VId> LawiContext::strengthenLabelsAlongPath(const ArtPath & path, const vec<PTRef> & itps) {
    auto vertices = art.getPathVertices(path);
    assert(vertices.size() == itps.size_() + 1);
    std::vector<VId> refinedVertices;
    for (int i = 0; i < itps.size(); ++i) {
        VId vertex = vertices[i + 1];
        PTRef itp = itps[i];
        PTRef currentLabel = labels.getLabel(vertex);
//        std::cout << "Old label of " << vertex.id << " is " << logic.printTerm(currentLabel) << std::endl;
        auto implCheckRes = checkImplication(currentLabel, itp);
        if (implCheckRes != decltype(implCheckRes)::VALID) {
            refinedVertices.push_back(vertex);
            labels.replaceLabel(vertex, logic.mkAnd(itp, currentLabel));
            // label of 'vertex' has been strengthened, it might not cover other vertices anymore
            coveringRelation.vertexStrengthened(vertex);
        }
//        std::cout << "New label of " << vertex.id << " is " << logic.printTerm(labels.getLabel(vertex)) << std::endl;
    }
    return refinedVertices;
}

ErrorPath LawiContext::buildGraphPathFromTreePath(const ArtPath & path) const {
    auto edges = path.getEdges();
	std::vector<EId> originalEdges;
    std::transform(edges.begin(), edges.end(), std::back_inserter(originalEdges),
				   [this](EId eid) { return art.getOriginalEdge(eid); });
    return ErrorPath(std::move(originalEdges));
}

}

//
// LAWI methods
//

VerificationResult Lawi::solve(ChcDirectedHyperGraph const & graph) {
    if (graph.isNormalGraph()) {
        auto normalGraph = graph.toNormalGraph();
        return solve(*normalGraph);
    }
    return VerificationResult(VerificationAnswer::UNKNOWN);
}


VerificationResult Lawi::solve(ChcDirectedGraph const & graph) {
    LawiContext ctx(logic, graph, options);
    return ctx.unwind();
}
