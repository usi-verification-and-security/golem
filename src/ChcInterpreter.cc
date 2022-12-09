/*
 * Copyright (c) 2020-2022, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include <engine/Bmc.h>
#include <engine/Kind.h>
#include <engine/Lawi.h>
#include <engine/Spacer.h>
#include <engine/TPA.h>
#include <engine/IMC.h>
#include "ChcInterpreter.h"
#include "ChcGraph.h"
#include "graph/GraphTransformations.h"
#include "Validator.h"
#include "Normalizer.h"
#include "transformers/RemoveUnreachableNodes.h"
#include "transformers/SimpleChainSummarizer.h"
#include "transformers/TransformationPipeline.h"

using namespace osmttokens;

namespace {
bool addLetFrame(const vec<char *> & names, vec<PTRef> const& args, Logic & logic, LetRecords& letRecords) {
    assert(names.size() == args.size());
    if (names.size() > 1) {
        // check that they are pairwise distinct;
        std::unordered_set<const char*, StringHash, Equal<const char*>> namesAsSet(names.begin(), names.end());
        if (namesAsSet.size() != names.size_()) {
            return false;
        }
    }
    for (int i = 0; i < names.size(); ++i) {
        const char* name = names[i];
        if (logic.hasSym(name) && logic.getSym(logic.symNameToRef(name)[0]).noScoping()) {
            return false;
        }
        letRecords.addBinding(name, args[i]);
    }
    return true;
}
}

std::unique_ptr<ChcSystem> ChcInterpreter::interpretSystemAst(Logic & logic, const ASTNode * root) {
    ChcInterpreterContext ctx(logic, opts);
    return ctx.interpretSystemAst(root);
}

std::unique_ptr<ChcSystem> ChcInterpreterContext::interpretSystemAst(const ASTNode * root) {
    if (not root) {
        return std::unique_ptr<ChcSystem>();
    }
    this->system.reset();
    auto it = root->children->begin();
    for (; it != root->children->end() && not this->doExit; ++it) {
        interpretCommand(**it);
//        delete *it;
//        *it = nullptr;
    }
    return std::move(this->system);
}

void ChcInterpreterContext::interpretCommand(ASTNode & node) {
    assert(node.getType() == CMD_T);
    const smt2token cmd = node.getToken();
    switch (cmd.x) {
        case t_setlogic: {
            ASTNode & logic_n = **(node.children->begin());
            const char * logic_name = logic_n.getValue();
            if (strcmp(logic_name, "HORN") == 0) {
                system.reset(new ChcSystem());
            } else {
                reportError("Invalid (set-logic) comand");
            }
            break;
        }
        case t_setinfo: {
            // TODO: implement this
            break;
        }
        case t_declarefun: {
            if (not system) {
                reportError("Missing (set-logic) command, ignoring (declare-fun)");
            } else {
                interpretDeclareFun(node);
            }
            break;
        }
        case t_assert: {
            if (not system) {
                reportError("Missing (set-logic) command, ignoring (assert)");
            } else {
                interpretAssert(node);
            }
            break;
        }
        case t_checksat: {
            if (not system) {
                reportError("Missing (set-logic) command, ignoring (check-sat)");
            } else {
                interpretCheckSat();
            }
            break;
        }
        case t_exit: {
            this->doExit = true;
            break;
        }
        case t_getmodel: {
            /* Silently ignore for now */
            break;
        }
        case t_setoption: {
            /* Silently ignore for now */
            break;
        }
        default:
            reportError("Unknown command, ignoring");
    }
}

SRef ChcInterpreterContext::sortFromASTNode(ASTNode const & node) const {
    if (node.getType() == SYM_T) {
        SortSymbol symbol(node.getValue(), 0);
        SSymRef symRef;
        bool known = logic.peekSortSymbol(symbol, symRef);
        if (not known) { return SRef_Undef; }
        return logic.getSort(symRef, {});
    } else {
        assert(node.getType() == LID_T and node.children and not node.children->empty());
        ASTNode const & name = **(node.children->begin());
        SortSymbol symbol(name.getValue(), node.children->size() - 1);
        SSymRef symRef;
        bool known = logic.peekSortSymbol(symbol, symRef);
        if (not known) { return SRef_Undef; }
        vec<SRef> args;
        for (auto it = node.children->begin() + 1; it != node.children->end(); ++it) {
            SRef argSortRef = sortFromASTNode(**it);
            if (argSortRef == SRef_Undef) { return SRef_Undef; }
            args.push(argSortRef);
        }
        return logic.getSort(symRef, std::move(args));
    }
}

void ChcInterpreterContext::interpretDeclareFun(ASTNode & node) {
    auto it = node.children->begin();
    ASTNode& name_node = **(it++);
    ASTNode& args_node = **(it++);
    ASTNode& ret_node  = **(it++);
    assert(it == node.children->end());

    const char * fname = name_node.getValue();
    SRef codomainSort = sortFromASTNode(ret_node);

    if (codomainSort == SRef_Undef) {
        reportError("Unknown return sort of " +  std::string(fname));
        return;
    }
    else if (codomainSort != logic.getSort_bool()) {
        reportError("Return sort of uninterpeted predicate must be Bool");
        return;
    }

    // domain sorts
    vec<SRef> args;
    for (auto childNode : *(args_node.children)) {
        SRef argSort = sortFromASTNode(*childNode);
        if (argSort != SRef_Undef) {
            args.push(argSort);
        } else {
            reportError("Undefined sort in function " +  std::string(fname));
            return;
        }
    }
    SymRef rval = logic.declareFun(fname, codomainSort, args);

    if (rval == SymRef_Undef) {
        reportError("While declare-fun " + std::string(fname));
        return;
    }
    system->addUninterpretedPredicate(rval);
}

void ChcInterpreterContext::interpretAssert(ASTNode & node) {
    ASTNode& termNode = **(node.children->begin());
    PTRef term = parseTerm(termNode);
    assert(term != PTRef_Undef);
//    std::cout << backgroundTheory->getLogic().printTerm(term) << std::endl;
    if (logic.getTerm_true() == term) { return; }
    auto chclause = chclauseFromPTRef(term);
    system->addClause(std::move(chclause));
}

PTRef ChcInterpreterContext::parseTerm(const ASTNode & termNode) {
    ASTType t = termNode.getType();
    if (t == TERM_T) {
        const char* name = (**(termNode.children->begin())).getValue();
        return logic.mkConst(name);
    }
    else if (t == FORALL_T) { // Forall has two children: sorted_var_list and term
        auto it = termNode.children->begin();
        ASTNode& qvars = **it;
        assert(qvars.getType() == SVL_T);
        // HACK! Using let frames to properly parse formula with universal quantifiers (same variable name might already be assoociated with multiple sorts
        class QuantifierHack{
            std::size_t counter = 0;
            LetRecords & rec;
        public:
            QuantifierHack(LetRecords& rec): rec(rec) {}
            ~QuantifierHack() {
                for (std::size_t i = 0; i < counter; ++i) {
                    rec.popFrame();
                }
            }

            void addBinding(const char* name, PTRef term) {
                rec.pushFrame();
                rec.addBinding(name, term);
                ++counter;
            }
        } quantifierHack(letRecords);
        for (ASTNode * var : *qvars.children) {
            assert(var && var->getType() == SV_T);
            // make sure the term store know about these variables
            const char* name = var->getValue();
            SRef sort = sortFromASTNode(**var->children->begin());
            PTRef varTerm = logic.mkVar(sort, name);
            quantifierHack.addBinding(name, varTerm);
//            std::cout << var->getValue() << std::endl; // name of the variable
//            std::cout << backgroundTheory->getLogic().getSortName(getSort(**var->children->begin())) << std::endl; // sort of th variable
        }
        ++it;
        ASTNode& innerTerm = **it;
        return parseTerm(innerTerm);
    }
    else if (t == QID_T) {
        const char* name = (**(termNode.children->begin())).getValue();
        PTRef tr = letRecords.getOrUndef(name);
        if (tr != PTRef_Undef) {
            return tr;
        }
        tr = logic.resolveTerm(name, {});
        assert(tr != PTRef_Undef);
        return tr;
    }
    else if (t == LQID_T) {
        auto node_iter = termNode.children->begin();
        const char* name = (**node_iter).getValue(); node_iter++;
        // Parse the arguments
        vec<PTRef> args;
        for (; node_iter != termNode.children->end(); node_iter++) {
            PTRef arg_term = parseTerm(**node_iter);
            if (arg_term == PTRef_Undef) {
                assert(false);
                return PTRef_Undef;
            }
            else
                args.push(arg_term);
        }
        assert(args.size() > 0);
        PTRef tr = PTRef_Undef;
        tr = logic.resolveTerm(name, std::move(args));
        assert(tr != PTRef_Undef);
        return tr;
    }
    else if (t == LET_T) {
        auto ch = termNode.children->begin();
        auto vbl = (**ch).children->begin();
        vec<PTRef> tmp_args;
        vec<char*> names;
        // use RAII idiom to guard the scope of new LetFrame (and ensure the cleaup of names)
        class Guard {
            LetRecords& rec;
            vec<char*>& names;
        public:
            Guard(LetRecords& rec, vec<char*>& names): rec(rec), names(names) { rec.pushFrame(); }
            ~Guard() { rec.popFrame(); for (int i = 0; i < names.size(); i++) { free(names[i]); }}
        } scopeGuard(letRecords, names);
        // First read the term declarations in the let statement
        while (vbl != (**ch).children->end()) {
            PTRef let_tr = parseTerm(**((**vbl).children->begin()));
            if (let_tr == PTRef_Undef) return PTRef_Undef;
            tmp_args.push(let_tr);
            char* name = strdup((**vbl).getValue());
            names.push(name);
            vbl++;
        }
        // Only then insert them to the table
        bool success = addLetFrame(names, tmp_args, logic, letRecords);
        if (not success) {
            return PTRef_Undef;
        }
        ch++;
        // This is now constructed with the let declarations context in let_branch
        PTRef tr = parseTerm(**(ch));
        if (tr == PTRef_Undef) {
            return PTRef_Undef;
        }
        return tr;
    }
    else {
        std::cout << "Unknown type: " << termNode.typeToStr() << std::endl;
        throw std::logic_error("Type not handled in parsing!\n");
    }
}

void ChcInterpreterContext::interpretCheckSat() {
    bool validateWitness = opts.hasOption(Options::VALIDATE_RESULT);
    assert(not validateWitness || opts.getOption(Options::VALIDATE_RESULT) == std::string("true"));
    bool printWitness = opts.hasOption(Options::PRINT_WITNESS);
    assert(not printWitness || opts.getOption(Options::PRINT_WITNESS) == std::string("true"));

//    ChcPrinter(logic).print(*system, std::cout);
    auto normalizedSystem = Normalizer(logic).normalize(*system);
    auto hypergraph = ChcGraphBuilder(logic).buildGraph(normalizedSystem);
    std::unique_ptr<ChcDirectedHyperGraph> originalGraph {nullptr};
    if (validateWitness) { // Store copy of the original graph for validating purposes
        originalGraph = std::make_unique<ChcDirectedHyperGraph>(*hypergraph);
    }

    TransformationPipeline::pipeline_t transformations;
    transformations.push_back(std::make_unique<SimpleChainSummarizer>(logic));
    transformations.push_back(std::make_unique<RemoveUnreachableNodes>());
    auto [newGraph, translator] = TransformationPipeline(std::move(transformations)).transform(std::move(hypergraph));
    hypergraph = std::move(newGraph);

    auto engine = getEngine();
    auto result = engine->solve(*hypergraph);
    switch (result.getAnswer()) {
        case VerificationAnswer::SAFE: {
            std::cout << "sat" << std::endl;
            break;
        }
        case VerificationAnswer::UNSAFE: {
            std::cout << "unsat" << std::endl;
            break;
        }
        case VerificationAnswer::UNKNOWN:
            std::cout << "unknown" << std::endl;
            return;
    }
    if (validateWitness || printWitness) {
        result = translator->translate(std::move(result));
        if (printWitness) {
            result.printWitness(std::cout, logic);
        }
        if (validateWitness) {
            assert(originalGraph);
            auto validationResult = Validator(logic).validate(*originalGraph, result);
            switch (validationResult) {
                case Validator::Result::VALIDATED: {
                    std::cout << "Internal witness validation successful!" << std::endl;
                    break;
                }
                case Validator::Result::NOT_VALIDATED: {
                    std::cout << "Internal witness validation failed!" << std::endl;
                    break;
                }
                default:
                    throw std::logic_error("Unexpected case in result validation!");
            }
        }
    }
}

void ChcInterpreterContext::reportError(std::string msg) {
    std::cout << "(error " << '"' << msg << '"' << ")\n";
}

ChClause ChcInterpreterContext::chclauseFromPTRef(PTRef ref) {
    assert(ref != PTRef_Undef);
    Logic & logic = this->logic;
    PTRef disjunction = ref;
    if (not logic.isOr(disjunction)) {
        // special cases
        // 1. Head with empty body
        if (isUninterpretedPredicate(ref)) {
            return ChClause{.head = PTRefToCHC::constructHead(ref), .body = PTRefToCHC::constructBody(logic.getTerm_true(), {})};
        } else if (logic.isNot(ref)) {
            PTRef argOfNot = logic.getPterm(ref)[0];
            // 2. Empty head, single predicate in body
            if (isUninterpretedPredicate(argOfNot)) {
                return ChClause{.head = PTRefToCHC::constructHead(logic.getTerm_false()), .body = PTRefToCHC::constructBody(logic.getTerm_true(), {argOfNot})};
            } else if(logic.isAnd(argOfNot)) {
                // The clause is represented as negation of conjunction, turn it into disjunction
                vec<PTRef> args;
                for (int i = 0; i < logic.getPterm(argOfNot).size(); ++i) {
                    PTRef arg = logic.getPterm(argOfNot)[i];
                    args.push(logic.mkNot(arg));
                }
                disjunction = logic.mkOr(args);
            } else {
                throw std::logic_error(std::string("Unknown format of in parsing CHC: ") + logic.printTerm(ref));
            }
        }
    }
    assert(logic.isOr(disjunction));
    // identify interpreted part and uninterpreted part
    vec<PTRef> disjuncts = TermUtils(logic).getTopLevelDisjuncts(disjunction);
    // find uninterpreted predicates (positive or negative)
    auto uninterpretedEnd = std::partition(disjuncts.begin(), disjuncts.end(), [this, &logic](PTRef arg) {
        return this->isUninterpretedPredicate(arg) || (logic.isNot(arg) && this->isUninterpretedPredicate(logic.getPterm(arg)[0]));
    });

    // find positive uninterpreted predicates
    auto positiveEnd = std::partition(disjuncts.begin(), uninterpretedEnd, [&logic](PTRef arg) {
        return not logic.isNot(arg);
    });
    if (positiveEnd - disjuncts.begin() > 1) {
        throw std::logic_error(std::string("More than one positive uninterpreted predicate in clause"));
    }
    ChcHead head = positiveEnd == disjuncts.begin() ? PTRefToCHC::constructHead(logic.getTerm_false()) : PTRefToCHC::constructHead(*disjuncts.begin());
    // Negate the body so that it represents antecedent of the implication
    std::transform(positiveEnd, disjuncts.end(), positiveEnd, [&logic](PTRef bodyArg) { return logic.mkNot(bodyArg); });
    vec<PTRef> interpretedArgs;
    std::for_each(uninterpretedEnd, disjuncts.end(), [&interpretedArgs](PTRef arg) { interpretedArgs.push(arg); });
    PTRef interpretedPart = logic.mkAnd(interpretedArgs);

    ChcBody body = PTRefToCHC::constructBody(interpretedPart, positiveEnd, uninterpretedEnd);

    return ChClause{.head = std::move(head), .body = std::move(body)};
}

bool ChcInterpreterContext::isUninterpretedPredicate(PTRef ref) const {
    return system->isUninterpretedPredicate(logic.getSymRef(ref));
}

std::unique_ptr<Engine> ChcInterpreterContext::getEngine() const {
    std::string engineStr = opts.hasOption(Options::ENGINE) ? opts.getOption(Options::ENGINE) : "spacer";
    if (engineStr == TPAEngine::TPA or engineStr == TPAEngine::SPLIT_TPA) {
        return std::unique_ptr<Engine>(new TPAEngine(logic, opts));
    } else if (engineStr == "bmc") {
        return std::unique_ptr<Engine>(new BMC(logic, opts));
    } else if (engineStr == "lawi") {
        return std::unique_ptr<Engine>(new Lawi(logic, opts));
    } else if (engineStr == "spacer") {
        return std::unique_ptr<Engine>(new Spacer(logic, opts));
    } else if (engineStr == "kind") {
        return std::unique_ptr<Engine>(new Kind(logic, opts));
    } else if (engineStr == "imc") {
        return std::unique_ptr<Engine>(new IMC(logic, opts));
    } else {
        throw std::invalid_argument("Unknown engine specified");
    }
}
