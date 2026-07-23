#ifndef GOLEM_INDUCTIVE_ITP_H
#define GOLEM_INDUCTIVE_ITP_H

#include "ModelBasedProjection.h"
#include "TermUtils.h"
#include "SmtSolver.h"
#include "pterms/PTRef.h"
#include <string>

namespace golem {

// Helper for assertions
inline
bool is_clause(Logic& logic, PTRef fla) {
    if (logic.isConstant(fla) or logic.isAtom(fla)) { return true; }
    if (not (logic.isNot(fla) or logic.isOr(fla))) { return false; }
    for (PTRef term : logic.getPterm(fla)) {
        if (not is_clause(logic, term)) { return false; }
    }
    return true;
}

inline
bool implies(PTRef antecedent, PTRef consequent, Logic & logic) {
    SMTSolver solver(logic);
    solver.assertProp(antecedent);
    solver.assertProp(logic.mkNot(consequent));
    return solver.check() == SMTSolver::Answer::UNSAT;
}

inline
bool equivalent(PTRef a, PTRef b, Logic & logic) {
    return implies(a, b, logic) and implies(b, a, logic);
}

/* Given A(x, x'), B(x') such that
   - A(x, x') & B(x') is unsatisfiable
   Return a formula P(x) such that
   - A(x, x') & (guardVariable -> P(x)) -> P(x')
   - P(x) & B(x) is unsatisfiable
*/
template <typename Func>
PTRef inductiveConflict(Logic& logic,
                        PTRef T, PTRef A, PTRef B,
                        PTRef guardVariable,
                        Func toBase
                        ) {
    TermUtils termUtils(logic);

    ModelBasedProjection mbp_solver(logic);

    SMTSolver cti_solver(logic, SMTSolver::WitnessProduction::ONLY_MODEL);
    cti_solver.assertProp(A);
    cti_solver.assertProp(T);

    TermUtils::substitutions_map prime2base;
    vec<PTRef> xsPrime = termUtils.getVars(B);
    for (PTRef xPrime : xsPrime) {
        prime2base.emplace(xPrime, toBase(xPrime));
    }

    auto allVars = TermUtils(logic).getVars(A);
    vec<PTRef> xs;
    for (PTRef var : allVars) {
        // TODO: subtitute with isTarget()
        if (std::find(xsPrime.begin(), xsPrime.end(), var) == xsPrime.end()) {
            xs.push(var);
        }
    }

    // Assertion helper
    auto unsatCheck = [&cti_solver, &B](){
        cti_solver.push();
        cti_solver.assertProp(B);
        bool isUnsat = (cti_solver.check() == SMTSolver::Answer::UNSAT);
        cti_solver.pop();
        return isUnsat;
    };
    assert(unsatCheck());
    // std::cerr << "****************" << std::endl;
    // std::cerr << "A: " << logic.printTerm(A) << std::endl;
    // std::cerr << "B: " << logic.printTerm(B) << std::endl;
    auto varsA = termUtils.getVars(A);
    assert(std::find(varsA.begin(), varsA.end(), guardVariable) != varsA.end());
    // end check input

    // TODO: incrementality
    auto get_local_unsatcore = [&](PTRef mbp) -> std::pair<PTRef, PTRef> {
        SMTSolver itp_solver(logic, SMTSolver::WitnessProduction::ONLY_UNSAT_CORE);
        itp_solver.assertProp(B);
        int counter = 0;
        for (auto conj : termUtils.getTopLevelConjuncts(mbp)) {
            itp_solver.tryAssertNamedProp(conj, std::to_string(counter++));
        }
        // itp_solver.push();
        // std::cerr << "ITP(mbp, B) with mbp := " << logic.printTerm(mbp) << std::endl;
        auto res = itp_solver.check();
        if (res != SMTSolver::Answer::UNSAT) {
            throw std::logic_error("Error in UCORE: result is not unsatisfiable.");
        }
        auto core = itp_solver.getUnsatCore();
        const auto& terms = core->getTerms();
        // vec<PTRef> negatedTerms;
        // negatedTerms.capacity(terms.size());
        // for (PTRef term : terms) { negatedTerms.push(logic.mkNot(term)); }
        // auto interpolantPrime = logic.mkOr(negatedTerms);
        auto interpolantPrime = logic.mkAnd(terms);
        auto interpolant = termUtils.varSubstitute(interpolantPrime, prime2base);
        auto ok = is_clause(logic, interpolant);

        // assert(is_clause(is_clause, interpolant));
        // itp_solver.pop();
        return {interpolant, interpolantPrime};
    };

    // TODO: incrementality
    auto get_local_itp = [&](PTRef mbp) -> std::pair<PTRef, PTRef> {
        SMTSolver itp_solver(logic, SMTSolver::WitnessProduction::ONLY_INTERPOLANTS);
        itp_solver.getConfig().setSimplifyInterpolant(4);
        itp_solver.assertProp(mbp);
        itp_solver.assertProp(B);
        // itp_solver.push();
        // std::cerr << "ITP(mbp, B) with mbp := " << logic.printTerm(mbp) << std::endl;
        auto res = itp_solver.check();
        if (res != SMTSolver::Answer::UNSAT) {
            throw std::logic_error("Error in ITP: result is not unsatisfiable.");
        }
        auto itpCtx = itp_solver.getInterpolationContext();
        std::vector<PTRef> itps;
        ipartitions_t mask = 1;
        itpCtx->getSingleInterpolant(itps, mask);
        PTRef interpolantPrime = itps[0];
        PTRef interpolant = termUtils.varSubstitute(interpolantPrime, prime2base);
        // auto ok = is_clause(logic, interpolant);
        // assert(is_clause(is_clause, interpolant));
        // itp_solver.pop();
        return {interpolant, interpolantPrime};
    };

    auto lemma = logic.getTerm_false();
    auto interpolantPrime = logic.getTerm_false();

    do {
        cti_solver.assertProp(logic.mkNot(interpolantPrime));

        cti_solver.push();
        cti_solver.assertProp(logic.mkImpl(guardVariable, lemma));
        // cti_solver.assertProp(logic.mkNot(interpolantPrime));
        // TODO: exploit incrementality
        auto res = cti_solver.check();
        if (res == SMTSolver::Answer::UNSAT) { break; }
        if (res != SMTSolver::Answer::SAT) {
            throw std::logic_error("Error in looking for CTIs.");
        }
        auto cti = cti_solver.getModel();
        PTRef implicant = mbp_solver.getModelBasedImplicant(logic.mkAnd(A, T), xs, *cti);
        auto pair = get_local_itp(implicant);
        // PTRef mbp = mbp_solver.keepOnly(logic.mkAnd(A, T), xsPrime, *cti);
        // auto pair = get_local_unsatcore(mbp);
        lemma = logic.mkOr(lemma, pair.first);
        // auto pair = get_local_itp(logic.mkOr(interpolantPrime, implicant));
        // lemma = pair.first;
        interpolantPrime = pair.second;
        cti_solver.pop();
    } while (true);

    if (logic.isAnd(lemma) or logic.isOr(lemma)) {
        lemma = ::rewriteMaxArityAggresive(logic, lemma);
        lemma = ::simplifyUnderAssignment_Aggressive(lemma, logic);
    }

    return lemma;
}

} // namespace golem

#endif // GOLEM_INDUCTIVE_ITP_H

