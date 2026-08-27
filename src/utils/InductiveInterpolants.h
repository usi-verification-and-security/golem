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

namespace {

bool check_init(Logic& logic, PTRef A, PTRef B, PTRef T01, PTRef T02, PTRef T12) {
    SMTSolver debug_solver(logic);
    debug_solver.assertProp(A);
    debug_solver.assertProp(B);
    return (debug_solver.check() == SMTSolver::Answer::UNSAT);
}

bool check_loop_invariant(Logic& logic,
                          PTRef A, PTRef B, PTRef T,
                          PTRef lemma01, PTRef lemma02, PTRef lemma12) {
    SMTSolver debug_solver(logic);
    debug_solver.assertProp(lemma02);
    debug_solver.assertProp(B);
    return (debug_solver.check() == SMTSolver::Answer::UNSAT);
}

bool check_end(Logic& logic, PTRef A, PTRef T,
               PTRef lemma01, PTRef lemma02, PTRef lemma12) {
    SMTSolver debug_solver(logic);
    debug_solver.push();
    debug_solver.assertProp(T);
    debug_solver.assertProp(logic.mkNot(lemma01));
    if (debug_solver.check() != SMTSolver::Answer::UNSAT) { return false; }
    debug_solver.pop();

    debug_solver.push();
    debug_solver.assertProp(A);
    debug_solver.assertProp(lemma01);
    debug_solver.assertProp(lemma12);
    debug_solver.assertProp(logic.mkNot(lemma02));
    return debug_solver.check() == SMTSolver::Answer::UNSAT;
}

} // namespace

/* Given A(x, x', x''), B(x, x'') such that
   - A(x, x', x'') & B(x, x'') is unsatisfiable
   Return a formula P(x, x') such that
   - A(x, x', x'') & P(x, x') & P(x', x'') -> P(x, x'')
   - P(x, x'') & B(x, x'') is unsatisfiable
   - T(x, x') -> P(x, x')
*/
template <typename Func>
PTRef inductiveTransConflict(Logic& logic,
                             PTRef T, PTRef A, PTRef B,
                             Func getVarsAt
                             ) {
    TermUtils termUtils(logic);

    ModelBasedProjection mbp_solver(logic);

    vec<PTRef> vars = getVarsAt(0);
    vec<PTRef> nextVars = getVarsAt(1);
    vec<PTRef> nextNextVars = getVarsAt(2);
    TermUtils::substitutions_map shiftNext;
    TermUtils::substitutions_map shiftBack;
    TermUtils::substitutions_map shiftOnlyNext;
    for (auto i = 0; i < vars.size(); ++i) {
        shiftNext.emplace(vars[i], nextVars[i]);
        shiftNext.emplace(nextVars[i], nextNextVars[i]);
        shiftOnlyNext.emplace(nextVars[i], nextNextVars[i]);
        shiftBack.emplace(nextNextVars[i], nextVars[i]);
        shiftBack.emplace(nextVars[i], vars[i]);
    }

    auto guard = logic.mkBoolVar("guard#inditp#");
    // A(x, x', x'') := T(x, x'') or (guard and A(x, x', x''))
    A = logic.mkOr(termUtils.varSubstitute(T, shiftOnlyNext), logic.mkAnd(guard, A));

    SMTSolver cti_solver(logic, SMTSolver::WitnessProduction::ONLY_MODEL);
    cti_solver.assertProp(A);

    assert(check_init(logic, A, B,
                      T,
                      termUtils.varSubstitute(T, shiftOnlyNext),
                      termUtils.varSubstitute(T, shiftNext)));


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
        auto lemma02 = logic.mkAnd(terms);
        auto lemma01 = termUtils.varSubstitute(lemma02, shiftBack);
        // itp_solver.pop();
        return {lemma01, lemma02};
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
        PTRef lemma02 = itps[0];
        PTRef lemma01 = termUtils.varSubstitute(lemma02, shiftBack);
        // auto ok = is_clause(logic, interpolant);
        // assert(is_clause(is_clause, interpolant));
        // itp_solver.pop();
        return {lemma01, lemma02};
    };

    auto lemma01 = logic.getTerm_false();
    auto lemma12 = lemma01;
    auto lemma02 = lemma12;

    do {
        cti_solver.assertProp(logic.mkNot(lemma02));

        cti_solver.push();
        cti_solver.assertProp(logic.mkImpl(guard, lemma01));
        cti_solver.assertProp(logic.mkImpl(guard, lemma12));

        auto res = cti_solver.check();
        if (res == SMTSolver::Answer::UNSAT) { break; }
        if (res != SMTSolver::Answer::SAT) {
            throw std::logic_error("Error in looking for CTIs.");
        }
        auto cti = cti_solver.getModel();
        // PTRef implicant = mbp_solver.getModelBasedImplicant(A, nextVars, *cti);
        // auto pair = get_local_itp(implicant);
        PTRef mbp = mbp_solver.project(A, nextVars, *cti);
        auto pair = get_local_unsatcore(mbp);
        lemma01 = logic.mkOr(lemma01, pair.first);
        lemma02 = pair.second;
        lemma12 = termUtils.varSubstitute(lemma01, shiftNext);
        cti_solver.pop();

        assert(check_loop_invariant(logic, A, B, T,
                                    lemma01,
                                    termUtils.varSubstitute(lemma01, shiftOnlyNext),
                                    termUtils.varSubstitute(lemma01, shiftNext)));

    } while (true);

    assert(check_end(logic, A, T,
                     lemma01,
                     termUtils.varSubstitute(lemma01, shiftOnlyNext),
                     termUtils.varSubstitute(lemma01, shiftNext)));

    if (logic.isAnd(lemma01) or logic.isOr(lemma01)) {
        lemma01 = ::rewriteMaxArityAggresive(logic, lemma01);
        lemma01 = ::simplifyUnderAssignment_Aggressive(lemma01, logic);
    }

    return lemma01;
}

} // namespace golem

#endif // GOLEM_INDUCTIVE_ITP_H

