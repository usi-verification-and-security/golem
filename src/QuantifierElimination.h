//
// Created by Martin Blicha on 12.06.21.
//

#ifndef OPENSMT_QUANTIFIERELIMINATION_H
#define OPENSMT_QUANTIFIERELIMINATION_H

#include "osmt_terms.h"

/*
 * A utility for precise elimination of (existential) quantifiers from a formula.
 *
 * Given a formula F(x,y) we want to compute a formula G(x) such that G(x) \equiv \exist y F(x,y)
 */
class QuantifierElimination {
    Logic & logic;
public:
    QuantifierElimination(Logic & logic) : logic(logic) {}

    PTRef eliminate(PTRef fla, PTRef var);
    PTRef eliminate(PTRef fla, vec<PTRef> const & vars);
    PTRef keepOnly(PTRef, vec<PTRef> const & vars);
};


#endif //OPENSMT_QUANTIFIERELIMINATION_H
