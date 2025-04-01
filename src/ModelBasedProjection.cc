//
// Created by Martin Blicha on 06.03.21.
//

#include "ModelBasedProjection.h"

#include "TermUtils.h"

#include <memory>


namespace{
    enum class BoundType {LOWER, UPPER};

    struct Bound {
        BoundType type;
        PTRef val;
        bool strict;
    };

    PTRef substituteBound(Bound const& what, Bound const& where, ArithLogic & logic) {
        if (what.type == BoundType::UPPER and where.type == BoundType::UPPER) {
            throw std::invalid_argument("Not implemented yet for two upper bounds");
        }
        if (where.type == BoundType::LOWER and what.type == BoundType::LOWER) {
            if (where.strict and not what.strict) {
                return logic.mkLt(where.val, what.val);
            } else {
                return logic.mkLeq(where.val, what.val);
            }
        } else {
            assert(where.type == BoundType::UPPER or what.type == BoundType::UPPER);
            assert(where.type == BoundType::LOWER or what.type == BoundType::LOWER);
            auto const & upper = where.type == BoundType::UPPER ? where : what;
            auto const & lower = where.type == BoundType::UPPER ? what : where;
            if (upper.strict or lower.strict) {
                return logic.mkLt(lower.val, upper.val);
            } else {
                return logic.mkLeq(lower.val, upper.val);
            }
        }
    }

    vec<PTRef> substituteBound(Bound const& what, std::vector<Bound> const& where, ArithLogic & logic) {
        vec<PTRef> res;
        for (Bound const & bound : where) {
            PTRef subResult = substituteBound(what, bound, logic);
            if (logic.isNumEq(subResult)) {
                throw std::logic_error("This should not happen anymore");
            }
            else if (subResult != logic.getTerm_true()) {
                res.push(subResult);
            }
        }
        return res;
    }

    struct LinearFactor {
        PTRef var;
        PTRef coeff;
    };

    LinearFactor splitLinearFactorToVarAndConst(PTRef tr, ArithLogic const & logic) {
        assert(logic.isLinearFactor(tr));
        auto [var, coeff] = logic.splitTermToVarAndConst(tr);
        return {var, coeff};
    }

    std::vector<LinearFactor> splitLinearTermToFactors(PTRef tr, ArithLogic const & logic ) {
        std::vector<LinearFactor> factors;
        assert(logic.isLinearTerm(tr));
        if (logic.isLinearFactor(tr)) { return {splitLinearFactorToVarAndConst(tr, logic)}; }

        Pterm const & t = logic.getPterm(tr);
        for (int i = 0; i < t.size(); ++i) {
            factors.push_back(splitLinearFactorToVarAndConst(t[i], logic));
        }
        return factors;
    }

    std::pair<LinearFactor, PTRef> separateVarFromTerm(PTRef var, PTRef term, ArithLogic & logic) {
        assert(logic.isVar(var) and logic.isLinearTerm(term));
        auto factors = splitLinearTermToFactors(term, logic);
        LinearFactor const * varFactor = nullptr;
        vec<PTRef> args;
        for (auto const & factor : factors) {
            if (factor.var == var) {
                assert(varFactor == nullptr);
                varFactor = &factor;
            } else {
                args.push(factor.var == PTRef_Undef ? factor.coeff : logic.mkTimes(factor.coeff, factor.var));
            }
        }
        assert(varFactor);
        return {*varFactor, args.size_() == 0 ? logic.getZeroForSort(logic.getSortRef(var)) : logic.mkPlus(args)};
    }

    template<typename TIt>
    void normalizeEqualities(TIt begin, TIt end, ArithLogic & logic) {
        std::for_each(begin, end, [&logic](PtAsgn & lit) {
            if (logic.isEquality(lit.tr)) {
                PTRef lhs = logic.getPterm(lit.tr)[0];
                PTRef rhs = logic.getPterm(lit.tr)[1];
                PTRef zero = logic.getZeroForSort(logic.getSortRef(lhs));
                if (lhs == zero or rhs == zero or logic.isNumConst(lhs) or logic.isNumConst(rhs)) {
                    // already normalized
                    return;
                }
                lit.tr = logic.mkEq(logic.mkMinus(lhs, rhs), zero);
            }
        });
    }
}

void ModelBasedProjection::postprocess(implicant_t & literals, ArithLogic & lalogic) {
    LATermUtils(lalogic).simplifyConjunction(literals);
}

ModelBasedProjection::implicant_t ModelBasedProjection::projectSingleVar(PTRef var, implicant_t implicant, Model & model) {
    assert(logic.isVar(var));
    // if the variable is boolean, simply remove it from implicant
    if (logic.hasSortBool(var)) {
        auto it = std::find_if(implicant.begin(), implicant.end(), [var](PtAsgn literal) { return literal.tr == var; });
        if (it != implicant.end()) {
            it = implicant.erase(it);
            // the same boolean variable cannot be present twice in the implicant
            assert(std::find_if(it, implicant.end(), [var](PtAsgn literal) { return literal.tr == var; }) == implicant.end());
        }
        return implicant;
    }
    ArithLogic * lalogic = dynamic_cast<ArithLogic *>(&logic);
    if (not lalogic or not lalogic->isNumVar(var)) {
        throw std::logic_error("Projection for other than Reals or Ints not supported");
    }
    // proper elimination of Real variable

    // Normalizing is necessary to avoid equalities like "x = x + y" in further analysis.
    // This could be done on OpenSMT level
    normalizeEqualities(implicant.begin(), implicant.end(), *lalogic);

    LATermUtils utils(*lalogic);
    auto containsVar = [var, &utils](PtAsgn lit) {
        return utils.atomContainsVar(lit.tr, var);
    };

    // split the literals to those containing var and those not containing var
    auto interestingEnd = std::partition(implicant.begin(), implicant.end(), containsVar);
    // preprocessing
    for (auto it = implicant.begin(); it != interestingEnd; ++it) {
        PtAsgn lit = *it;
        if (logic.isEquality(lit.tr)) {
            PTRef lhs = logic.getPterm(lit.tr)[0];
            PTRef rhs = logic.getPterm(lit.tr)[1];
            if (lit.sgn == l_True) { // if equality is present, we just use it to substitute the variable away
                assert(model.evaluate(lit.tr) == logic.getTerm_true());
                // express variable and substitute in the rest of literals
                PTRef zeroTerm = lalogic->mkMinus(lhs, rhs);
                PTRef substitutionTerm = utils.expressZeroTermFor(zeroTerm, var);
                MapWithKeys<PTRef, PTRef, PTRefHash> subst;
                subst.insert(var, substitutionTerm);
                Substitutor substitutor(logic, subst);
                for (auto it2 = implicant.begin(); it2 != interestingEnd; ++it2) {
                    it2->tr = substitutor.rewrite(it2->tr);
                }
                // remove the true terms
                assert(it->tr == logic.getTerm_true());
                auto size = implicant.size();
                for (std::size_t i = 0; i < size; /* manual control */) {
                    PtAsgn literal = implicant[i];
                    if ((literal.tr == logic.getTerm_true() and literal.sgn == l_True) or (literal.tr == logic.getTerm_false() and literal.sgn == l_False)) {
                        implicant[i] = implicant.back();
                        implicant.pop_back();
                        --size;
                        assert(size == implicant.size());
                    } else {
                        ++i;
                    }
                }
                return implicant;
            } else {
                assert(lit.sgn == l_False);
                // replace the non-equality with the strict inequality that is true in the model
                PTRef lt = lalogic->mkLt(lhs, rhs);
                PTRef replacement = model.evaluate(lt) == logic.getTerm_true() ? lt : lalogic->mkLt(rhs, lhs);
                if (replacement == logic.getTerm_true()) {
                    // This could happen if the original inequality is like "x != x + 1"
                    it->tr = logic.getTerm_true();
                    it->sgn = l_True;
                } else {
                    assert(logic.isNot(replacement)); // strict inequalities are expressed as negations of non-strict ones
                    it->tr = logic.getPterm(replacement)[0]; // we store the non-strict inequality, the sign is already set to false
                    assert(it->sgn == l_False);
                }
            }
        }
    }
    // at this point we have only strict and nonstrict inequalities

    // literals with the variable that we want to eliminate are now in the front of the vector
    // "interestingEnd" points to the first literal that does not contain the var anymore

    // collect the lower and upper bounds, remember if they are strict or non-strict
//    std::vector<Bound> bounds;
    std::vector<Bound> lBounds;
    std::vector<Bound> uBounds;
    std::vector<Bound> bounds;
    for (auto it = implicant.begin(); it != interestingEnd; ++it) {
        PTRef ineq = it->tr;
        lbool sign = it->sgn;
        assert(sign == l_True || sign == l_False);
        if (ineq == logic.getTerm_true()) { // this is still possible if we had true disequality at the beginning (x != x + 1)
            assert(sign == l_True);
            continue;
        }
        bool isStrict = sign == l_False;
        bool isLower = sign != l_False; // inequalities are of form "c <= t" where c is constant
        PTRef constant = lalogic->getPterm(ineq)[0];
        assert(lalogic->isConstant(constant));
        PTRef linTerm = lalogic->getPterm(ineq)[1];
        assert(lalogic->isLinearTerm(linTerm));
        auto factors = splitLinearTermToFactors(linTerm, *lalogic);
        auto interestingVarIt = std::find_if(factors.begin(), factors.end(), [var](LinearFactor factor) {
            return factor.var == var;
        });
        assert(interestingVarIt != factors.end());
        auto coeffPTRef = interestingVarIt->coeff;
        factors.erase(interestingVarIt);
        auto coeff = lalogic->getNumConst(coeffPTRef);
        if (coeff.sign() < 0) {
            isLower = !isLower;
        }
        SRef sortRef = logic.getSortRef(constant);
        PTRef newConstant = lalogic->mkConst(sortRef, lalogic->getNumConst(constant) / coeff);
        coeff.negate();
        // update the coefficients in the factor
        vec<PTRef> boundArgs;
        for (auto & factor : factors) { // in place update
            auto newCoeff = lalogic->getNumConst(factor.coeff) / coeff;
            factor.coeff = lalogic->mkConst(sortRef, newCoeff);
            boundArgs.push(lalogic->mkTimes(factor.var, factor.coeff)); // MB: no simplification, could be insertTermHash directly
        }
        boundArgs.push(newConstant);
        PTRef bound = lalogic->mkPlus(boundArgs); // MB: no simplification should happen, could be insertTermHash
        // Remember the bound
        auto boundType = isLower ? BoundType::LOWER : BoundType::UPPER;
        bounds.push_back(Bound{.type = boundType, .val = bound, .strict = isStrict});
        auto & whereToPush = isLower ? lBounds : uBounds;
        whereToPush.push_back(bounds.back());
    }

    if (lBounds.empty() or uBounds.empty()) {
        // if we are missing either upper or lower bounds altogether, no new literals are produced and we can just return those not containing this variable
        return implicant_t(interestingEnd, implicant.end());
    }

    implicant_t newLiterals;
    if (uBounds.size() == 1 or lBounds.size() == 1) {
        // Do full elimination with single bound; This yields more general result
        auto subRes = uBounds.size() == 1 ? substituteBound(uBounds[0], lBounds, *lalogic) : substituteBound(lBounds[0], uBounds, *lalogic);
        assert(std::all_of(subRes.begin(), subRes.end(), [&](PTRef lit) { return model.evaluate(lit) == logic.getTerm_true(); }));
        newLiterals.resize(subRes.size());
        std::transform(subRes.begin(), subRes.end(), newLiterals.begin(),
            [&](PTRef lit) { return lalogic->isNot(lit) ? PtAsgn(lalogic->getPterm(lit)[0], l_False) : PtAsgn(lit, l_True);});
    } else {
        // pick the correct literal based on the model
        assert(lalogic->isConstant(model.evaluate(var)));
        // pick substitution from lower bounds
        // pick highest lower bound according to the model
        Bound const * highestLowerBound = nullptr;
        for (auto const & bound : lBounds) {
            assert(bound.type == BoundType::LOWER);
            if (highestLowerBound == nullptr) {
                highestLowerBound = &bound;
                continue;
            }
            PTRef currentValRef = model.evaluate(highestLowerBound->val);
            PTRef otherValRef = model.evaluate(bound.val);
            assert(lalogic->isConstant(currentValRef) && lalogic->isConstant(otherValRef));
            auto const & currentVal = lalogic->getNumConst(currentValRef);
            auto const & otherVal = lalogic->getNumConst(otherValRef);
            if (otherVal > currentVal or (otherVal == currentVal and bound.strict)) {
                highestLowerBound = &bound;
            } else if (otherVal == currentVal) {
                // check if this bound should not be preferred because it is also upper bound
                auto it = std::find_if(uBounds.begin(), uBounds.end(), [&bound](Bound const & ubound) { return ubound.val == bound.val; });
                if (it != uBounds.end()) {
                    highestLowerBound = &bound;
                    break;
                }
            }
        }
        // perform substitution
        auto subRes = substituteBound(*highestLowerBound, bounds, *lalogic);
        assert(std::all_of(subRes.begin(), subRes.end(), [&](PTRef lit) { return model.evaluate(lit) == logic.getTerm_true(); }));
        newLiterals.resize(subRes.size());
        std::transform(subRes.begin(), subRes.end(), newLiterals.begin(),
            [&](PTRef lit) { return lalogic->isNot(lit) ? PtAsgn(lalogic->getPterm(lit)[0], l_False) : PtAsgn(lit, l_True);});
    }
    // don't forget the literals not containing the var to eliminate
    newLiterals.insert(newLiterals.end(), interestingEnd, implicant.end());
    postprocess(newLiterals, *lalogic);
    return newLiterals;
}

namespace{
void collectImplicant(Logic & logic, PTRef fla, Model & model, std::vector<char> & processed, std::vector<PtAsgn>& literals,
                      ModelBasedProjection::VarsInfo const & varsInfo) {
    auto id = Idx(logic.getPterm(fla).getId());
    if (id >= processed.size()) {
        throw std::logic_error("Should not happen!");
    }
    if (processed[id]) { return; }
    processed[id] = 1;
    PTRef trueTerm = logic.getTerm_true();
    assert(model.evaluate(fla) == trueTerm);
    if (logic.isAtom(fla)) {
        literals.push_back(PtAsgn(fla, l_True));
        return;
    }
    if (logic.isAnd(fla)) {
        // all children must be satisfied
        auto size = logic.getPterm(fla).size();
        for (int i = 0; i < size; ++i) {
            PTRef child = logic.getPterm(fla)[i];
            assert(model.evaluate(child) == trueTerm);
            collectImplicant(logic, child, model, processed, literals, varsInfo);
        }
        return;
    }
    if (logic.isOr(fla)) {
        bool hasInterestingVars = false;
        if (varsInfo.peek(fla, hasInterestingVars)) {
            if (not hasInterestingVars) {
                literals.push_back(PtAsgn(fla, l_True));
                return;
            }
        }
        // at least one child must be satisfied
        auto size = logic.getPterm(fla).size();
        for (int i = 0; i < size; ++i) {
            PTRef child = logic.getPterm(fla)[i];
            if (model.evaluate(child) == trueTerm) {
                collectImplicant(logic, child, model, processed, literals, varsInfo);
                return;
            }
        }
        assert(false);
        throw std::logic_error("Error in processing disjunction in collectImplicant!");
    }
    if (logic.isNot(fla)) {
        PTRef child = logic.getPterm(fla)[0];
        if (logic.isAtom(child)) {
            assert(model.evaluate(child) == logic.getTerm_false());
            literals.push_back(PtAsgn(child, l_False));
            return;
        }
        throw std::logic_error("Formula is not in NNF in collectImplicant!");
    }
    throw std::logic_error("Unexpected connective in formula in collectImplicant");
}

ModelBasedProjection::VarsInfo computeVarsInfo(PTRef fla, Logic & logic, PTRef const * const beg, PTRef const * const end) {
    Map<PTRef, bool, PTRefHash> res;
    vec<PTRef> queue;
    queue.push(fla);
    while (queue.size() != 0) {
        PTRef tr = queue.last();
        if (res.has(tr)) {
            queue.pop();
            continue;
        }
        bool unprocessed_children = false;
        for (int i = 0; i < logic.getPterm(tr).size(); i++) {
            PTRef c = logic.getPterm(tr)[i];
            if (res.has(c)) continue;
            else {
                queue.push(c);
                unprocessed_children = true;
            }
        }
        if (unprocessed_children == true) continue;
        queue.pop();
        if (logic.isVar(tr)) {
            bool ofInterest = std::find(beg, end, tr) != end;
            res.insert(tr, ofInterest);
        } else if (logic.isConstant(tr)) {
            res.insert(tr, false);
        } else {
            bool anyChildOfInterest = false;
            for (int i = 0; i < logic.getPterm(tr).size() and not anyChildOfInterest; i++) {
                PTRef c = logic.getPterm(tr)[i];
                assert(res.has(c));
                anyChildOfInterest = res[c];
            }
            res.insert(tr, anyChildOfInterest);
        }
    }
    return res;
}

}

ModelBasedProjection::implicant_t ModelBasedProjection::getImplicant(PTRef fla, Model & model, VarsInfo const & varsInfo) {
    assert(model.evaluate(fla) == logic.getTerm_true());
    std::vector<PtAsgn> literals;
    std::vector<char> processed;
    processed.resize(Idx(logic.getPterm(fla).getId()) + 1, 0);
    collectImplicant(logic, fla, model, processed, literals, varsInfo);
    return literals;
}

namespace{
void checkImplicant(ModelBasedProjection::implicant_t const & implicant, Logic & logic, Model & model) {
    (void)logic; (void)model;
    for (auto const& elem : implicant) {
        (void)elem;
        assert(elem.sgn == l_False or elem.sgn == l_True);
        assert((elem.sgn == l_False and model.evaluate(elem.tr) == logic.getTerm_false())
               or (elem.sgn == l_True and model.evaluate(elem.tr) == logic.getTerm_true()));
    }
}
}

PTRef ModelBasedProjection::keepOnly(PTRef fla, const vec<PTRef> & varsToKeep, Model & model) {
    auto allVars = TermUtils(logic).getVars(fla);
    vec<PTRef> toEliminate;
    for (PTRef var : allVars) {
        if (std::find(varsToKeep.begin(), varsToKeep.end(), var) == varsToKeep.end()) {
            toEliminate.push(var);
        }
    }
    return project(fla, toEliminate, model);
}

PTRef ModelBasedProjection::project(PTRef fla, const vec<PTRef> & varsToEliminate, Model & model) {
    vec<PTRef> tmp;
    varsToEliminate.copyTo(tmp);
    auto boolEndIt = std::stable_partition(tmp.begin(), tmp.end(), [&](PTRef var) {
        assert(logic.isVar(var));
        return logic.hasSortBool(var);
    });

    if (boolEndIt != tmp.begin()) { // there are some booleans
        MapWithKeys<PTRef, PTRef, PTRefHash> subst;
        for (auto it = tmp.begin(); it != boolEndIt; ++it) {
            subst.insert(*it, model.evaluate(*it));
        }
        fla = Substitutor(logic, subst).rewrite(fla);
    }
    if (boolEndIt == tmp.end()) {
        return fla;
    }

    PTRef nnf = TermUtils(logic).toNNF(fla);

    // compute map to know if given term contains any variable to eliminate
    auto varsInfo = computeVarsInfo(nnf, logic, boolEndIt, tmp.end());

//    auto implicant = getImplicant(nnf, model);
    auto implicant = getImplicant(nnf, model, varsInfo);

    // separate terms that do not contain variables of interest
    auto separator = std::stable_partition(implicant.begin(), implicant.end(), [&varsInfo](PtAsgn lit) {
       bool hasVar = true;
       if (varsInfo.peek(lit.tr, hasVar)) {
           return hasVar;
       }
       return true; // if we don't know, we pessimistically assume we need to process it
    });
    implicant_t withoutVarsToEliminate(separator, implicant.end());
    implicant.erase(separator, implicant.end());

//    dumpImplicant(std::cout, implicant);
    checkImplicant(implicant, logic, model);
    if (logic.hasIntegers()) {
        implicant = projectIntegerVars(boolEndIt, tmp.end(), std::move(implicant), model);
        implicant.insert(implicant.end(), withoutVarsToEliminate.begin(), withoutVarsToEliminate.end());
        postprocess(implicant, dynamic_cast<ArithLogic&>(logic));
        tmp.clear();
        for (PtAsgn literal : implicant) {
            tmp.push(literal.sgn == l_True ? literal.tr : logic.mkNot(literal.tr));
        }
        return logic.mkAnd(std::move(tmp));
    }
    for (auto it = boolEndIt; it != tmp.end(); ++it) {
        PTRef var = *it;
//        std::cout << "Eliminating " << logic.printTerm(var) << std::endl;
        implicant = projectSingleVar(var, std::move(implicant), model);
//        dumpImplicant(std::cout, implicant);
        checkImplicant(implicant, logic, model);
    }
    implicant.insert(implicant.end(), withoutVarsToEliminate.begin(), withoutVarsToEliminate.end());
    postprocess(implicant, dynamic_cast<ArithLogic&>(logic));
    tmp.clear();
    for (PtAsgn literal : implicant) {
        tmp.push(literal.sgn == l_True ? literal.tr : logic.mkNot(literal.tr));
    }
    return logic.mkAnd(std::move(tmp));
}

void ModelBasedProjection::dumpImplicant(std::ostream & out, implicant_t const& implicant) {
    out << "Implicant:\n";
    std::for_each(implicant.begin(), implicant.end(), [&](PtAsgn i) { out << logic.printTerm(i.tr) << ' ' << toInt(i.sgn) << '\n'; });
    out << std::endl;
}

ModelBasedProjection::implicant_t ModelBasedProjection::projectIntegerVars(PTRef * beg, PTRef * end, implicant_t implicant, Model & model) {
    auto & lialogic = dynamic_cast<ArithLogic&>(logic);
    assert(lialogic.hasIntegers());
    div_constraints_t divConstraints;
    auto isDivisibilityConstraint = [&lialogic](PtAsgn lit) {
        if (lialogic.isNumEq(lit.tr)) {
            PTRef lhs = lialogic.getPterm(lit.tr)[0];
            PTRef rhs = lialogic.getPterm(lit.tr)[1];
            if (lialogic.isMod(lialogic.getSymRef(lhs)) or lialogic.isMod(lialogic.getSymRef(rhs))) {
                return lit.sgn == l_True;
            }
        }
        return false;
    };
    auto toDivConstraint = [&lialogic](PtAsgn lit) {
        assert(lit.sgn == l_True);
        assert(lialogic.isNumEq(lit.tr));
        PTRef lhs = lialogic.getPterm(lit.tr)[0];
        PTRef rhs = lialogic.getPterm(lit.tr)[1];
        PTRef val = lialogic.isNumConst(lhs) ? lhs : rhs;
        PTRef mod = lialogic.isNumConst(lhs) ? rhs : lhs;
        (void)val;
        assert(val == lialogic.getTerm_IntZero());
        assert(lialogic.isMod(lialogic.getSymRef(mod)));
        PTRef term = lialogic.getPterm(mod)[0];
        PTRef constant = lialogic.getPterm(mod)[1];
        assert(lialogic.isNumConst(constant));
        return DivisibilityConstraint{.constant = constant, .term = term};
    };
    auto divConstraintsBeg = std::stable_partition(implicant.begin(), implicant.end(), [&](PtAsgn lit) { return not isDivisibilityConstraint(lit); });
    for (auto it = divConstraintsBeg; it != implicant.end(); ++it) {
        divConstraints.push_back(toDivConstraint(*it));
    }
    implicant.erase(divConstraintsBeg, implicant.end());
    for (PTRef * it = beg; it != end; ++it) {
        PTRef var = *it;
        if (not (lialogic.isNumVar(lialogic.getSymRef(var)) and lialogic.getSortRef(var) == lialogic.getSort_int())) {
            throw std::logic_error("Non-integer variable encountered in MBP for integers!");
        }
        if (not divConstraints.empty()) {
            processDivConstraints(var, divConstraints, implicant, model);
        } else {
            processClassicLiterals(var, divConstraints, implicant, model);
        }
        checkImplicant(implicant, logic, model);
    }

    if (not divConstraints.empty()) {
        for (auto const & constraint : divConstraints) {
            assert(lialogic.isConstant(constraint.constant));
            PTRef mod = lialogic.mkMod(constraint.term, constraint.constant);
            PTRef modConstraint = logic.mkEq(mod, lialogic.getTerm_IntZero());
            implicant.emplace_back(modConstraint, l_True);
        }
    }
    return implicant;
}

namespace {
// TODO: replace when available in FastRationals
FastRational mbp_fastrat_fdiv_r(FastRational const & n, FastRational const & d) {
    FastRational q = fastrat_fdiv_q(n, d);
    FastRational u = n - (q*d);
    return u;
}

std::unique_ptr<Model> extendModel(Model const & model, std::pair<PTRef, PTRef> const varValPair) {
    return model.extend(varValPair.first, varValPair.second);
}

template<class ForwardIt, class Funct>
ForwardIt maxElementWithProjection(ForwardIt first, ForwardIt last, Funct f) {
    if (first == last) return last;

    ForwardIt largest = first;
    auto valLargest = f(*first);
    ++first;
    for (; first != last; ++first) {
        if (auto val = f(*first); val > valLargest) {
            largest = first;
            valLargest = std::move(val);
        }
    }
    return largest;
}

}

/*
 * Projecting single integer variable in the presence of divisibility constraints.
 * Implemented according to the description from https://easychair.org/publications/paper/jmM
 * Bjorner & Janota, Playing with Quantified Satisfaction, LPAR-20, 2015
 */
void ModelBasedProjection::processDivConstraints(PTRef var, div_constraints_t & divConstraints, implicant_t & implicant, Model & model) {
    auto & lialogic = dynamic_cast<ArithLogic&>(logic);
    assert(lialogic.hasIntegers());
    auto itInterestingEnd = std::partition(divConstraints.begin(), divConstraints.end(), [&](DivisibilityConstraint const& c) {
        return LATermUtils(lialogic).termContainsVar(c.term, var);
    });
    if (itInterestingEnd != divConstraints.begin()) {
        // there are some div constraints for this variable
        auto beg = divConstraints.begin();
        auto end = itInterestingEnd;
        assert(std::all_of(beg, end, [&](DivisibilityConstraint const& constraint) {
            auto const & val = lialogic.getNumConst(constraint.constant);
            return val.isInteger() and val.sign() > 0;
        }));
        FastRational d = std::accumulate(beg + 1, end, lialogic.getNumConst(beg->constant),
            [&](auto const & acc, DivisibilityConstraint const & next) {
            return lcm(acc, lialogic.getNumConst(next.constant));
        });
        FastRational u = mbp_fastrat_fdiv_r(lialogic.getNumConst(model.evaluate(var)),d);
        assert(u.sign() >= 0 and u.isInteger());

        // update divisibility constraints by substituting u for v (var)
        // TODO: make this more efficient
        TermUtils::substitutions_map subst;
        subst.insert({var, lialogic.mkIntConst(u)});
        TermUtils tutils(logic);
        std::for_each(beg, end, [&tutils, &subst](DivisibilityConstraint & constraint) {
            constraint.term = tutils.varSubstitute(constraint.term, subst);
        });

        // update the classic constraints and the variable that needs to be eliminated
        PTRef replacementVar = lialogic.mkIntVar("MBP_LIA_tmp");
        subst.clear();
        // v -> u + d * v_tmp
        subst.insert({var, lialogic.mkPlus(lialogic.mkIntConst(u), lialogic.mkTimes(lialogic.mkIntConst(d), replacementVar))});
        // Before substitutions, compute the extended model
        FastRational replacementVarVal = (lialogic.getNumConst(model.evaluate(var)) - u) / d;
        assert(replacementVarVal.isInteger());
        auto extendedModel = extendModel(model, {replacementVar, lialogic.mkIntConst(replacementVarVal)});
        // Now we can substitute
        // TODO: only for those that contain the variable?
        std::for_each(implicant.begin(), implicant.end(), [&](PtAsgn & lit){
            assert(model.evaluate(lit.tr) == extendedModel->evaluate(lit.tr));
            lit.tr = tutils.varSubstitute(lit.tr, subst);
        });
        // Important: before proceeding with eliminating the temporary variable, we need to make the model aware of its true value
        // Otherwise it will use default value (zero), which is not correct!
        processClassicLiterals(replacementVar, divConstraints, implicant, *extendedModel);
    } else {
        processClassicLiterals(var, divConstraints, implicant, model);
    }
}

/*
 * At this point, the var is not present in the divisibility constraints, we only need to process the proper literals in the implicant.
 * These literals might still contain equalities, disequalities or strict inequalities (TODO: verify?)
 */
void ModelBasedProjection::processClassicLiterals(PTRef var, div_constraints_t & divConstraints, implicant_t & implicant, Model & model) {
    auto & lialogic = dynamic_cast<ArithLogic &>(logic);
    assert(lialogic.hasIntegers());
    assert(lialogic.isNumVar(var));

    // Normalizing is necessary to avoid equalities like "x = x + y" in further analysis.
    // This could be done on OpenSMT level
    normalizeEqualities(implicant.begin(), implicant.end(), lialogic);

    auto containsVar = [var, &lialogic](PtAsgn lit) {
        return LATermUtils(lialogic).atomContainsVar(lit.tr, var);
    };
    // split the literals to those containing var and those not containing var
    auto interestingEnd = std::partition(implicant.begin(), implicant.end(), containsVar);

    // search for equality, replace disequalities and strict inequalities
    std::vector<LIABoundLower> lower;
    std::vector<LIABoundUpper> upper;
    std::vector<LIABound> equal;
    for (auto it = implicant.begin(); it != interestingEnd; ++it) {
        PtAsgn literal = *it;
        if (lialogic.isEquality(literal.tr)) {
            PTRef lhs = lialogic.getPterm(literal.tr)[0];
            PTRef rhs = lialogic.getPterm(literal.tr)[1];
            if (literal.sgn == l_True) {
                // Express as "ax = t" where "a > 0"
                PTRef zeroTerm = lialogic.mkMinus(lhs, rhs);
                auto res = separateVarFromTerm(var, zeroTerm, lialogic);
                LinearFactor factor = res.first;
                FastRational const& coeff = lialogic.getNumConst(factor.coeff);
                if (coeff.sign() < 0) {
                    equal.push_back(LIABound{.term = res.second, .coeff = lialogic.mkIntConst(-coeff)});
                } else {
                    assert(coeff.sign() > 0);
                    equal.push_back(LIABound{.term = lialogic.mkNeg(res.second), .coeff = factor.coeff});
                }
            } else {
                assert(literal.sgn == l_False);
                // replace the non-equality with the inequality that is true in the model
                PTRef zeroTerm = lialogic.mkMinus(lhs, rhs);
                PTRef valterm = model.evaluate(zeroTerm);
                assert(lialogic.getNumConst(valterm) >= 1 or lialogic.getNumConst(valterm) <= -1);
                FastRational const& val = lialogic.getNumConst(valterm);
                auto res = separateVarFromTerm(var, zeroTerm, lialogic);
                LinearFactor factor = res.first;
                FastRational const& coeff = lialogic.getNumConst(factor.coeff);
                if (val.sign() > 0) {
                    if (coeff.sign() > 0) {
                        lower.push_back(LIABoundLower{.term = lialogic.mkPlus(lialogic.getTerm_IntOne(), lialogic.mkNeg(res.second)), .coeff = factor.coeff});
                    } else {
                        upper.push_back(LIABoundUpper{.term = lialogic.mkPlus(lialogic.getTerm_IntMinusOne(), res.second), .coeff = lialogic.mkIntConst(-coeff)});
                    }
                } else {
                    assert(val.sign() < 0);
                    if (coeff.sign() > 0) {
                        upper.push_back(LIABoundUpper{.term = lialogic.mkPlus(lialogic.getTerm_IntMinusOne(), lialogic.mkNeg(res.second)), .coeff = factor.coeff});
                    } else {
                        lower.push_back(LIABoundLower{.term = lialogic.mkPlus(lialogic.getTerm_IntOne(), res.second), .coeff = lialogic.mkIntConst(-coeff)});
                    }
                }
            }
        } else {
            assert(lialogic.isLeq(literal.tr));
            if (literal.sgn == l_False) { // not (c <= t) <=> c > t <=> c - 1 >= t
                literal.sgn = l_True;
                auto sides = lialogic.leqToConstantAndTerm(literal.tr);
                assert(lialogic.isNumConst(sides.first));
                literal.tr = lialogic.mkGeq(lialogic.mkIntConst(lialogic.getNumConst(sides.first) - 1), sides.second);
            }
            assert(literal.sgn == l_True);
            auto sides = lialogic.leqToConstantAndTerm(literal.tr);
            PTRef zeroTerm = lialogic.mkMinus(sides.second, sides.first);
            auto res = separateVarFromTerm(var, zeroTerm, lialogic);
            LinearFactor factor = res.first;
            FastRational const& coeff = lialogic.getNumConst(factor.coeff);
            if (coeff.sign() > 0) {
                lower.push_back(LIABoundLower{.term = lialogic.mkNeg(res.second), .coeff = factor.coeff});
            } else {
                upper.push_back(LIABoundUpper{.term = res.second, .coeff = lialogic.mkIntConst(-coeff)});
            }
        }
    }

    if (equal.empty()) {
        // only upper and lower bounds
        if (lower.empty() or upper.empty()) { // this variable can be eliminated without any additional constraints
            implicant.erase(implicant.begin(), interestingEnd);
            return;
        }
        // pick greatest lower bound in the model
        auto greatestLowerBoundIt = maxElementWithProjection(lower.begin(), lower.end(), [&](LIABoundLower const& bound) {
            assert(lialogic.getNumConst(bound.coeff) >= 1);
            return lialogic.getNumConst(model.evaluate(bound.term)) / lialogic.getNumConst(bound.coeff);
        });
        implicant_t newLiterals;
        FastRational const& glbCoeff = lialogic.getNumConst(greatestLowerBoundIt->coeff);
        // handle lower bounds
        for (auto it = lower.begin(); it != lower.end(); ++it) {
            if (it == greatestLowerBoundIt) { continue; }
            auto const & bound = *it;
            PTRef lhs = glbCoeff.isOne() ? bound.term : lialogic.mkTimes(bound.term, greatestLowerBoundIt->coeff);
            PTRef rhs = lialogic.getNumConst(bound.coeff).isOne() ? greatestLowerBoundIt->term : lialogic.mkTimes(greatestLowerBoundIt->term, bound.coeff);
            PTRef nBound = lialogic.mkLeq(lhs, rhs);
            if (nBound != lialogic.getTerm_true()) { // This can happen when we have a stronger and weaker bound on the same term
                newLiterals.emplace_back(nBound, l_True);
            }
        }
        // handle upper bounds
        for (auto const& bound : upper) {
            auto res = resolve(*greatestLowerBoundIt, bound, model, lialogic);
            assert(res.bounds.size() <= 2);
            for (PTRef nBound : res.bounds) {
                assert(nBound != lialogic.getTerm_true());
                newLiterals.emplace_back(nBound, l_True);
            }
            if (res.hasDivConstraint) {
                divConstraints.push_back(res.constraint);
            }
        }
        // add literals not containing the variable
        newLiterals.insert(newLiterals.end(), interestingEnd, implicant.end());
        implicant = std::move(newLiterals);
        return;
    } else {
        implicant_t newLiterals;
        LIABound const& eqBound = equal[0];
        assert(lialogic.getNumConst(eqBound.coeff).sign() > 0 and lialogic.getNumConst(eqBound.coeff).isInteger());
        // equal bounds
        for (auto it = equal.begin() + 1; it != equal.end(); ++it) {
            // ax = t; bx = s => as = bt
            LIABound const & otherBound = *it;
            assert(lialogic.getNumConst(otherBound.coeff).sign() > 0 and lialogic.getNumConst(otherBound.coeff).isInteger());
            PTRef lhs = lialogic.mkTimes(otherBound.term, eqBound.coeff);
            PTRef rhs = lialogic.mkTimes(eqBound.term, otherBound.coeff);
            PTRef newLit = lialogic.mkEq(lhs, rhs);
            if (newLit != lialogic.getTerm_true()) {
                newLiterals.emplace_back(newLit, l_True);
            }
        }
        // lower bounds
        for (auto const & lowerBound : lower) {
            assert(lialogic.getNumConst(lowerBound.coeff).sign() > 0 and lialogic.getNumConst(lowerBound.coeff).isInteger());
            // ax = t; s <= bx => as <= bt
            PTRef lhs = lialogic.mkTimes(lowerBound.term, eqBound.coeff);
            PTRef rhs = lialogic.mkTimes(eqBound.term, lowerBound.coeff);
            PTRef newLit = lialogic.mkLeq(lhs, rhs);
            if (newLit != lialogic.getTerm_true()) {
                newLiterals.emplace_back(newLit, l_True);
            }
        }
        // upper bounds
        for (auto const & upperBound : upper) {
            assert(lialogic.getNumConst(upperBound.coeff).sign() > 0 and lialogic.getNumConst(upperBound.coeff).isInteger());
            // ax = t; s >= bx => as >= bt
            PTRef lhs = lialogic.mkTimes(upperBound.term, eqBound.coeff);
            PTRef rhs = lialogic.mkTimes(eqBound.term, upperBound.coeff);
            PTRef newLit = lialogic.mkGeq(lhs, rhs);
            if (newLit != lialogic.getTerm_true()) {
                newLiterals.emplace_back(newLit, l_True);
            }
        }
        // From the equality ax = t it also follows that t must be divisible by a
        assert(lialogic.getNumConst(eqBound.coeff).sign() > 0);
        if (eqBound.coeff != lialogic.getTerm_IntOne()) {
            divConstraints.push_back(DivisibilityConstraint{.constant = eqBound.coeff, .term = eqBound.term});
        }
        // add literals not containing the variable
        newLiterals.insert(newLiterals.end(), interestingEnd, implicant.end());
        implicant = std::move(newLiterals);
        return;
    }
    throw std::logic_error("UNREACHABLE!");
}

/*
 * Resolves the lower bound with the upper bound (on some variable) under the given model M.
 * Possibly adds new divisibility constraints.
 *
 * Given upper bound ax <= t and lower bound bx >= s, the resolvent is
 * 1. as + (a-1)(b-1) <= bt                             if (a-1)(b-1) <= M(bt - as)
 * 2. as <= bt and a(s+d) <= bt and b|(s+d)             elif a>=b and d:=M(-s) mod b
 * 3. as <= bt and as <= b(t-d) and a|(t-d)             else b>a and d:=M(t) mod a
 * */
ModelBasedProjection::ResolveResult ModelBasedProjection::resolve(LIABoundLower const & lower, LIABoundUpper const & upper, Model & model, ArithLogic & lialogic) {
    assert(logic.hasIntegers());
    ResolveResult result;
    PTRef a_term = upper.coeff;
    PTRef b_term = lower.coeff;
    auto const& a = lialogic.getNumConst(a_term);
    auto const& b = lialogic.getNumConst(b_term);
    assert(a.isInteger() and b.isInteger());
    assert(a.sign() > 0 and b.sign() > 0);
    PTRef t_term = upper.term;
    PTRef s_term = lower.term;
    PTRef as_term = lialogic.mkTimes(a_term, s_term);
    PTRef bt_term = lialogic.mkTimes(b_term, t_term);
    auto const& t = lialogic.getNumConst(model.evaluate(t_term));
    auto const& s = lialogic.getNumConst(model.evaluate(s_term));

    FastRational mul = (a-1)*(b-1);
    if (mul <= (b*t - a*s)) {
        // case 1
        PTRef nBound = lialogic.mkLeq(lialogic.mkPlus(as_term, lialogic.mkIntConst(mul)), bt_term);
        if (nBound != lialogic.getTerm_true()) {
            result.bounds.push_back(nBound);
        }
        result.hasDivConstraint = false;
        return result;
    }

    PTRef firstBound = lialogic.mkLeq(as_term, bt_term);
    if (firstBound != lialogic.getTerm_true()) {
        result.bounds.push_back(firstBound);
    }
    if (a >= b) {
        // case 2
        FastRational d = mbp_fastrat_fdiv_r(-s, b);
        assert(d.isInteger());
        PTRef modified = lialogic.mkPlus(s_term, lialogic.mkIntConst(d));
        if (not d.isZero()) {
            PTRef secondBound = lialogic.mkLeq(lialogic.mkTimes(a_term, modified), bt_term);
            if (secondBound != lialogic.getTerm_true()) {
                result.bounds.push_back(secondBound);
            }
        }
        result.constraint.constant = b_term;
        result.constraint.term = modified;
        result.hasDivConstraint = true;
    } else {
        // case 3
        FastRational d = mbp_fastrat_fdiv_r(t, a);
        assert(d.isInteger());
        PTRef modified = lialogic.mkMinus(t_term, lialogic.mkIntConst(d));
        if (not d.isZero()) {
            PTRef secondBound = lialogic.mkLeq(as_term, lialogic.mkTimes(b_term, modified));
            assert(secondBound != lialogic.getTerm_true());
            result.bounds.push_back(secondBound);
        }
        result.constraint.constant = a_term;
        result.constraint.term = modified;
        result.hasDivConstraint = true;
    }
    return result;
}

