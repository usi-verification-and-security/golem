#include "Common.h"

VerificationResult solveTrivial(ChcDirectedGraph const & graph, Logic & logic) {
    // All edges should be between entry and exit, check if any of them has a satisfiable label
    auto edgeIds = graph.getEdges();
    assert(edgeIds.size() <= 1); // Current preprocessing in TPA ensures that multiedges are replaced by single edge
    for (EId eid : edgeIds) {
        assert(graph.getSource(eid) == graph.getEntry());
        assert(graph.getTarget(eid) == graph.getExit());
        PTRef label = graph.getEdgeLabel(eid);
        if (label == logic.getTerm_false()) { continue; }
        SMTConfig config;
        MainSolver solver(logic, config, "solver");
        solver.insertFormula(label);
        auto res = solver.check();
        if (res == s_False) {
            continue;
        } else if (res == s_True) {
            InvalidityWitness::Derivation derivation;
            derivation.addDerivationStep(
                {.index = 0, .premises = {}, .derivedFact = logic.getTerm_true(), .clauseId = {static_cast<id_t>(-1)}});
            derivation.addDerivationStep(
                {.index = 1, .premises = {0}, .derivedFact = logic.getTerm_false(), .clauseId = eid});
            InvalidityWitness witness;
            witness.setDerivation(std::move(derivation));
            return VerificationResult(VerificationAnswer::UNSAFE, std::move(witness));
        } else {
            // Unexpected solver result;
            return VerificationResult(VerificationAnswer::UNKNOWN);
        }
    }
    // Here we know that no edge is satisfiable
    return VerificationResult(VerificationAnswer::SAFE);
}
