/*
 * Copyright (c) 2021-2022, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "TestTemplate.h"
#include "engine/Lawi.h"

class LAWI_LRA_Test : public LRAEngineTest {
};


TEST_F(LAWI_LRA_Test, test_LAWI_simple) {
    options.addOption(Options::LOGIC, "QF_LIA");
    options.addOption(Options::COMPUTE_WITNESS, "true");
    SymRef s1 = mkPredicateSymbol("s1", {realSort()});
    PTRef current = instantiatePredicate(s1, {x});
    PTRef next = instantiatePredicate(s1, {xp});
    std::vector<ChClause> clauses{
        { // x' = 0 => S1(x')
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{{logic->mkEq(xp, zero)}, {}}
        },
        { // S1(x) and x' = x + 1 => S1(x')
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{{logic->mkEq(xp, logic->mkPlus(x, one))}, {UninterpretedPredicate{current}}}
        },
        { // S1(x) and x < 0 => false
            ChcHead{UninterpretedPredicate{logic->getTerm_false()}},
            ChcBody{{logic->mkLt(x, zero)}, {UninterpretedPredicate{current}}}
        }
    };
    Lawi engine(*logic, options);
    solveSystem(clauses, engine, VerificationAnswer::SAFE, true);
}

TEST_F(LAWI_LRA_Test, test_LAWI_branch) {
    options.addOption(Options::LOGIC, "QF_LIA");
    options.addOption(Options::COMPUTE_WITNESS, "true");
    SymRef first = mkPredicateSymbol("s1", {realSort(), realSort()});
    SymRef second = mkPredicateSymbol("s2", {realSort(), realSort()});
    PTRef y = mkRealVar("y");
    PTRef yp = mkRealVar("yp");
    PTRef s1 = instantiatePredicate(first, {x, y});
    PTRef s1p = instantiatePredicate(first, {xp, yp});
    PTRef s2 = instantiatePredicate(second, {x, y});
    PTRef s2p = instantiatePredicate(second, {xp, yp});
    std::vector<ChClause> clauses{
        {
            ChcHead{UninterpretedPredicate{s1p}},
            ChcBody{{logic->mkEq(xp, zero)}, {}}
        },
        {
            ChcHead{UninterpretedPredicate{s1p}},
            ChcBody{{logic->mkEq(xp, logic->mkPlus(x, one))}, {UninterpretedPredicate{s1}}}
        },
        {
            ChcHead{UninterpretedPredicate{s2}},
            ChcBody{{logic->mkLt(y, zero)}, {UninterpretedPredicate{s1}}}
        },
        {
            ChcHead{UninterpretedPredicate{s2}},
            ChcBody{{logic->mkGeq(y, zero)}, {UninterpretedPredicate{s1}}}
        },
        {
            ChcHead{UninterpretedPredicate{s2p}},
            ChcBody{{logic->mkAnd(logic->mkEq(yp, logic->mkPlus(y, one)), logic->mkEq(xp, x))}, {UninterpretedPredicate{s2}}}
        },
        {
            ChcHead{UninterpretedPredicate{logic->getTerm_false()}},
            ChcBody{{logic->mkLt(x, zero)}, {UninterpretedPredicate{s2}}}
        }
    };
    Lawi engine(*logic, options);
    solveSystem(clauses, engine, VerificationAnswer::SAFE, true);
}

TEST_F(LAWI_LRA_Test, test_LAWI_unreachable_state) {
    options.addOption(Options::LOGIC, "QF_LRA");
    options.addOption(Options::COMPUTE_WITNESS, "true");
    SymRef s1 = mkPredicateSymbol("s1", {realSort()});
    SymRef bin = mkPredicateSymbol("bin", {realSort()});
    PTRef current = instantiatePredicate(s1, {x});
    PTRef next = instantiatePredicate(s1, {xp});
    PTRef binCurrent = instantiatePredicate(bin, {x});
    PTRef binNext = instantiatePredicate(bin, {xp});
    std::vector<ChClause> clauses{
        {
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{{logic->mkEq(xp, zero)}, {}}    
        },
        {
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{{logic->mkEq(xp, logic->mkPlus(x, one))}, {UninterpretedPredicate{current}}}    
        },
        {
            ChcHead{UninterpretedPredicate{logic->getTerm_false()}},
            ChcBody{{logic->mkLt(x, zero)}, {UninterpretedPredicate{current}}}
        },
        {
            ChcHead{UninterpretedPredicate{binNext}},
            ChcBody{{logic->mkEq(xp, logic->mkPlus(x, one))}, {UninterpretedPredicate{binCurrent}}}
        },
        {
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{{logic->mkAnd(logic->mkEq(xp, x), logic->mkLt(x, zero))}, {UninterpretedPredicate{binCurrent}}}
        }

    };
    
    Lawi engine(*logic, options);
    solveSystem(clauses, engine, VerificationAnswer::SAFE, true);
}

TEST_F(LAWI_LRA_Test, test_LAWI_simple_unsafe) {
    options.addOption(Options::LOGIC, "QF_LRA");
    options.addOption(Options::COMPUTE_WITNESS, "true");
    SymRef s1 = mkPredicateSymbol("s1", {realSort()});
    PTRef current = instantiatePredicate(s1, {x});
    PTRef next = instantiatePredicate(s1, {xp});
    std::vector<ChClause> clauses{
        {
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{{logic->mkEq(xp, zero)}, {}}
        },
        {
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{{logic->mkEq(xp, logic->mkPlus(x, one))}, {UninterpretedPredicate{current}}}
        },
        {
            ChcHead{UninterpretedPredicate{logic->getTerm_false()}},
            ChcBody{{logic->mkEq(x, one)}, {UninterpretedPredicate{current}}}
        }
    };
    Lawi engine(*logic, options);
    solveSystem(clauses, engine, VerificationAnswer::UNSAFE);
}

class LAWI_LIA_Test : public LIAEngineTest {
};

TEST_F(LAWI_LIA_Test, test_LAWI_auxiliaryVar) {
    options.addOption(Options::COMPUTE_WITNESS, "true");
    SymRef s = mkPredicateSymbol("s", {intSort()});
    PTRef x = mkIntVar("x");
    PTRef xp = mkIntVar("xp");
    PTRef b = mkBoolVar("b");
    PTRef current = instantiatePredicate(s, {x});
    PTRef next = instantiatePredicate(s, {xp});
    std::vector<ChClause> clauses{
        // x' = 0 => S(x')
        {ChcHead{UninterpretedPredicate{next}}, ChcBody{{logic->mkEq(xp, zero)}, {}}},
        { // S(x) and x' = ite(b, x, x + 1) => S(x')
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{{logic->mkEq(xp, logic->mkIte(b, x, logic->mkPlus(x, one)))}, {UninterpretedPredicate{current}}}
        },
        { // S(x) and x = 2 => false
            ChcHead{UninterpretedPredicate{logic->getTerm_false()}},
            ChcBody{{logic->mkEq(x, two)}, {UninterpretedPredicate{current}}}
        }
    };
    Lawi engine(*logic, options);
    solveSystem(clauses, engine, VerificationAnswer::UNSAFE, true);
}

TEST_F(LAWI_LIA_Test, test_LAWI_auxiliaryVarElimination) {
    options.addOption(Options::COMPUTE_WITNESS, "true");
    SymRef s = mkPredicateSymbol("s", {boolSort()});
    PTRef b = mkBoolVar("b");
    PTRef c = mkBoolVar("c");
    PTRef d = mkBoolVar("d");
    PTRef x = mkBoolVar("x");
    PTRef xp = mkBoolVar("xp");
    PTRef current = instantiatePredicate(s, {x});
    PTRef next = instantiatePredicate(s, {xp});
    std::vector<ChClause> clauses{
        // ~b and b = c and c = d and ~d = xp => S(xp)
        {ChcHead{UninterpretedPredicate{next}}, ChcBody{{logic->mkAnd({
            logic->mkEq(xp, logic->mkNot(d)), logic->mkEq(c,d), logic->mkEq(b,c), logic->mkNot(b)})}, {}
        }},
        { // S(x) and x = false => false
            ChcHead{UninterpretedPredicate{logic->getTerm_false()}},
            ChcBody{{logic->mkEq(x, logic->getTerm_false())}, {UninterpretedPredicate{current}}}
        }
    };
    Lawi engine(*logic, options);
    solveSystem(clauses, engine, VerificationAnswer::SAFE, true);
}

TEST_F(LAWI_LIA_Test, test_LAWI_auxiliaryVarElimination2) {
    options.addOption(Options::COMPUTE_WITNESS, "true");
    SymRef s = mkPredicateSymbol("s", {intSort()});
    PTRef x = mkIntVar("x");
    PTRef y = mkIntVar("y");
    PTRef z = mkIntVar("z");
    PTRef current = instantiatePredicate(s, {x});
    std::vector<ChClause> clauses{
        { //  z = 0 and x = 3y + z => S(x)
            ChcHead{UninterpretedPredicate{current}},
            ChcBody{{logic->mkAnd(logic->mkEq(z, zero), logic->mkEq(x, logic->mkPlus(z, logic->mkTimes(y, logic->mkIntConst(3)))))},{}}
        },
        { // S(x) and x = 32 => false
        ChcHead{UninterpretedPredicate{logic->getTerm_false()}},
        ChcBody{{logic->mkEq(x, logic->mkIntConst(32))}, {UninterpretedPredicate{current}}}
        }
    };
    Lawi engine(*logic, options);
    solveSystem(clauses, engine, VerificationAnswer::SAFE, true);
}

TEST_F(LAWI_LIA_Test, test_LAWI_bug) {
    options.addOption(Options::COMPUTE_WITNESS, "true");
    SymRef s = mkPredicateSymbol("s", {intSort(), intSort(), intSort()});
    PTRef x = mkIntVar("x");
    PTRef y = mkIntVar("y");
    PTRef z = mkIntVar("z");
    PTRef xp = mkIntVar("xp");
    PTRef yp = mkIntVar("yp");
    PTRef zp = mkIntVar("zp");
    PTRef current = instantiatePredicate(s, {x, y, z});
    PTRef next = instantiatePredicate(s, {xp, yp, zp});
    std::vector<ChClause> clauses{
        { //  S(x,y,z) and x = 1 and y = 1 and z = 0 and xp = 0 and yp = 0 and zp = 1 => S(xp,yp,zp)
            ChcHead{UninterpretedPredicate{next}},
            ChcBody{{logic->mkAnd({
                logic->mkEq(z, zero), logic->mkEq(x, one), logic->mkEq(y, one),
                logic->mkEq(zp, one), logic->mkEq(xp, zero), logic->mkEq(yp, zero)
            })},{UninterpretedPredicate{current}}}
        },
        { //  x = 0 and y = 0 and z = 0 => S(x,y,z)
            ChcHead{UninterpretedPredicate{current}},
            ChcBody{{logic->mkAnd({logic->mkEq(z, zero), logic->mkEq(x, zero), logic->mkEq(y, zero)})},{}}
        },
        { //  x = 1 and y = 1 and z = 0 => S(x,y,z)
            ChcHead{UninterpretedPredicate{current}},
            ChcBody{{logic->mkAnd({logic->mkEq(z, zero), logic->mkEq(x, one), logic->mkEq(y, one)})},{}}
        },
        { // S(x,y,z) and x = 0 and y = 0 and z = 1 => false
            ChcHead{UninterpretedPredicate{logic->getTerm_false()}},
            ChcBody{{logic->mkAnd({logic->mkEq(x, zero), logic->mkEq(y, zero), logic->mkEq(z, one)})}, {UninterpretedPredicate{current}}}
        },
        { // S(x,y,z) and x = 1 and y = 1 and z = 1 => false
            ChcHead{UninterpretedPredicate{logic->getTerm_false()}},
                ChcBody{{logic->mkAnd({logic->mkEq(x, one), logic->mkEq(y, one), logic->mkEq(z, one)})}, {UninterpretedPredicate{current}}}
        }
    };
    Lawi engine(*logic, options);
    solveSystem(clauses, engine, VerificationAnswer::UNSAFE, true);
}
