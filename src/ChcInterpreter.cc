/*
 * Copyright (c) 2020-2025, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "ChcInterpreter.h"
#include "Normalizer.h"
#include "Validator.h"
#include "engine/EngineFactory.h"
#include "graph/ChcGraph.h"
#include "graph/ChcGraphBuilder.h"
#include "proofs/Term.h"
#include "transformers/BasicTransformationPipelines.h"
#include "utils/ScopeGuard.h"

#include <csignal>
#include <memory>

#include <sys/mman.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>

using namespace opensmt::tokens;

namespace golem {
namespace {
bool addLetFrame(const vec<char *> & names, vec<PTRef> const & args, Logic & logic, LetRecords & letRecords) {
    assert(names.size() == args.size());
    if (names.size() > 1) {
        // check that they are pairwise distinct;
        std::unordered_set<const char *, StringHash, Equal<const char *>> namesAsSet(names.begin(), names.end());
        if (namesAsSet.size() != names.size_()) { return false; }
    }
    for (int i = 0; i < names.size(); ++i) {
        const char * name = names[i];
        if (logic.hasSym(name) && logic.getSym(logic.symNameToRef(name)[0]).noScoping()) { return false; }
        letRecords.addBinding(name, args[i]);
    }
    return true;
}
} // namespace

std::unique_ptr<ChcSystem> ChcInterpreter::interpretSystemAst(ArithLogic & logic, const ASTNode * root) {
    ChcInterpreterContext ctx(logic, opts);
    return ctx.interpretSystemAst(root);
}

std::unique_ptr<ChcSystem> ChcInterpreterContext::interpretSystemAst(const ASTNode * root) {
    if (not root) { return {}; }
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
    ASTNode & name_node = **(it++);
    ASTNode & args_node = **(it++);
    ASTNode & ret_node = **(it++);
    assert(it == node.children->end());

    const char * fname = name_node.getValue();
    SRef codomainSort = sortFromASTNode(ret_node);

    if (codomainSort == SRef_Undef) {
        reportError("Unknown return sort of " + std::string(fname));
        return;
    } else if (codomainSort != logic.getSort_bool()) {
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
            reportError("Undefined sort in function " + std::string(fname));
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

namespace {
class QuantifiedConstraintException : public std::runtime_error {
public:
    QuantifiedConstraintException()
        : std::runtime_error("Encountered quantified constraint, these are not supported!") {}
};
} // namespace

void ChcInterpreterContext::interpretAssert(ASTNode & node) {
    ASTNode & termNode = **(node.children->begin());
    try {
        PTRef term = parseTopLevelAssertion(termNode);
        assert(term != PTRef_Undef);
        if (logic.getTerm_true() == term) { return; }
        auto chclause = chclauseFromPTRef(term);
        if (not chclause) {
            reportError("Assertion is not a Horn clause: " + logic.printTerm(term));
            doExit = true;
            return;
        }
        system->addClause(std::move(*chclause));
        if (opts.hasOption(Options::PRINT_WITNESS)) { originalAssertions.push_back(ASTtoTerm(termNode)); }
    } catch (QuantifiedConstraintException const & e) {
        reportError(e.what());
        doExit = true;
    }
}

std::shared_ptr<Term> ChcInterpreterContext::ASTtoTerm(const ASTNode & node) {

    ASTType t = node.getType();
    if (t == TERM_T) {
        std::string name = (**(node.children->begin())).getValue();
        if (name.find('.') != std::string::npos) {
            return std::make_shared<Terminal>(name, Term::REAL);
        } else {
            return std::make_shared<Terminal>(name, Term::INT);
        }
    } else if (t == FORALL_T) { // Forall has two children: sorted_var_list and term
        auto it = node.children->begin();
        ASTNode & qvars = **it;
        assert(qvars.getType() == SVL_T);
        std::vector<std::shared_ptr<Term>> vars;
        std::vector<std::shared_ptr<Term>> sorts;
        for (ASTNode * var : *qvars.children) {
            assert(var && var->getType() == SV_T);
            // make sure the term store know about these variables
            std::string name = var->getValue();
            auto var_term = std::make_shared<Terminal>(name, Term::VAR);
            std::string sort = (*var->children->begin())->getValue();
            auto sort_term = std::make_shared<Terminal>(sort, Term::SORT);
            vars.push_back(var_term);
            sorts.push_back(sort_term);
        }
        assert(vars.size() == sorts.size());
        ASTNode & innerTerm = **(++it);
        return std::make_shared<Quant>("forall", vars, sorts, ASTtoTerm(innerTerm));
    } else if (t == QID_T) {
        std::string name = (**(node.children->begin())).getValue();
        if (name == "true" or name == "false") {
            return std::make_shared<Terminal>(name, Term::BOOL);
        } else {
            return std::make_shared<Terminal>(logic.protectName(name, false), Term::VAR);
        }
    } else if (t == LQID_T) {
        auto it = node.children->begin();
        std::string op = (**it).getValue();
        it++;
        std::vector<std::shared_ptr<Term>> args;
        for (; it != node.children->end(); it++) {
            std::shared_ptr arg_term = ASTtoTerm(**it);
            args.push_back(arg_term);
        }
        assert(not args.empty());
        if (op == "-" and args.size() == 1 and args[0]->getTermType() == Term::termType::TERMINAL) {
            return std::make_shared<Terminal>("(- " + args[0]->printTerm() + ")", args[0]->getTerminalType());
        }
        if (isOperator(op)) {
            return std::make_shared<Op>(op, args);
        } else {
            return std::make_shared<App>(logic.protectName(op, false), args);
        }
    } else if (t == LET_T) {
        auto ch = node.children->begin();
        auto vbl = (**ch).children->begin();
        std::vector<std::shared_ptr<Term>> declarations;
        std::vector<std::string> termNames;

        // First read the term declarations in the let statement
        while (vbl != (**ch).children->end()) {
            std::shared_ptr<Term> declaration = ASTtoTerm(**((**vbl).children->begin()));
            declarations.push_back(declaration);
            std::string name = (**vbl).getValue();
            termNames.push_back(name);
            vbl++;
        }

        ch++;
        // This is now constructed with the let declarations context in let_branch
        std::shared_ptr<Term> application = ASTtoTerm(**(ch));
        return std::make_shared<Let>(termNames, declarations, application);
    }

    throw std::logic_error("Unknown term encountered!");
}
PTRef ChcInterpreterContext::parseTopLevelAssertion(const ASTNode & termNode) {
    if (termNode.getType() == FORALL_T) { // Forall has two children: sorted_var_list and term
        auto it = termNode.children->begin();
        ASTNode & qvars = **it;
        assert(qvars.getType() == SVL_T);
        // HACK! Using let frames to properly parse formula with universal quantifiers (same variable name might already
        // be assoociated with multiple sorts
        class QuantifierHack {
            std::size_t counter = 0;
            LetRecords & rec;

        public:
            explicit QuantifierHack(LetRecords & rec) : rec(rec) {}
            ~QuantifierHack() {
                for (std::size_t i = 0; i < counter; ++i) {
                    rec.popFrame();
                }
            }

            void addBinding(const char * name, PTRef term) {
                rec.pushFrame();
                rec.addBinding(name, term);
                ++counter;
            }
        } quantifierHack(letRecords);
        for (ASTNode * var : *qvars.children) {
            assert(var && var->getType() == SV_T);
            // make sure the term store know about these variables
            const char * name = var->getValue();
            SRef sort = sortFromASTNode(**var->children->begin());
            PTRef varTerm = logic.mkVar(sort, name);
            quantifierHack.addBinding(name, varTerm);
        }
        ++it;
        ASTNode & innerTerm = **it;
        return parseTopLevelAssertion(innerTerm);
    }
    return parseTerm(termNode);
}

PTRef ChcInterpreterContext::parseTerm(const ASTNode & termNode) {
    ASTType t = termNode.getType();
    if (t == TERM_T) {
        const char * name = (**(termNode.children->begin())).getValue();
        return logic.mkConst(name);
    } else if (t == QID_T) {
        const char * name = (**(termNode.children->begin())).getValue();
        PTRef tr = letRecords.getOrUndef(name);
        if (tr != PTRef_Undef) { return tr; }
        tr = logic.resolveTerm(name, {});
        assert(tr != PTRef_Undef);
        return tr;
    } else if (t == LQID_T) {
        auto node_iter = termNode.children->begin();
        const char * name = (**node_iter).getValue();
        node_iter++;
        // Parse the arguments
        vec<PTRef> args;
        for (; node_iter != termNode.children->end(); node_iter++) {
            PTRef arg_term = parseTerm(**node_iter);
            if (arg_term == PTRef_Undef) {
                assert(false);
                return PTRef_Undef;
            } else
                args.push(arg_term);
        }
        assert(args.size() > 0);
        PTRef tr = PTRef_Undef;
        tr = logic.resolveTerm(name, std::move(args));
        assert(tr != PTRef_Undef);
        return tr;
    } else if (t == LET_T) {
        auto ch = termNode.children->begin();
        auto vbl = (**ch).children->begin();
        vec<PTRef> tmp_args;
        vec<char *> names;
        // use RAII idiom to guard the scope of new LetFrame (and ensure the cleaup of names)
        class Guard {
            LetRecords & rec;
            vec<char *> & names;

        public:
            Guard(LetRecords & rec, vec<char *> & names) : rec(rec), names(names) { rec.pushFrame(); }
            ~Guard() {
                rec.popFrame();
                for (int i = 0; i < names.size(); i++) {
                    free(names[i]);
                }
            }
        } scopeGuard(letRecords, names);
        // First read the term declarations in the let statement
        while (vbl != (**ch).children->end()) {
            PTRef let_tr = parseTerm(**((**vbl).children->begin()));
            if (let_tr == PTRef_Undef) return PTRef_Undef;
            tmp_args.push(let_tr);
            char * name = strdup((**vbl).getValue());
            names.push(name);
            vbl++;
        }
        // Only then insert them to the table
        bool success = addLetFrame(names, tmp_args, logic, letRecords);
        if (not success) { return PTRef_Undef; }
        ch++;
        // This is now constructed with the let declarations context in let_branch
        PTRef tr = parseTerm(**(ch));
        if (tr == PTRef_Undef) { return PTRef_Undef; }
        return tr;
    } else if (t == FORALL_T) {
        throw QuantifiedConstraintException{};
    } else {
        std::cout << "Unknown type: " << termNode.typeToStr() << std::endl;
        throw std::logic_error("Type not handled in parsing!\n");
    }
}

VerificationResult ChcInterpreterContext::solve(std::string const & engine_s,
                                                ChcDirectedHyperGraph const & hypergraph) {
    auto engine = EngineFactory(logic, opts).getEngine(engine_s);
    auto result = engine->solve(hypergraph);
    return result;
}

bool ChcInterpreterContext::hasWorkAfterAnswer() const {
    bool validateWitness = opts.hasOption(Options::VALIDATE_RESULT);
    assert(not validateWitness || opts.getOption(Options::VALIDATE_RESULT) == std::string("true"));
    bool printWitness = opts.hasOption(Options::PRINT_WITNESS);
    assert(not printWitness || opts.getOption(Options::PRINT_WITNESS) == std::string("true"));
    return printWitness or validateWitness;
}

void ChcInterpreterContext::doWorkAfterAnswer(VerificationResult result, ChcDirectedHyperGraph const & originalGraph,
                                              WitnessBackTranslator & translator,
                                              Normalizer::Equalities const & normalizingEqualities) const {
    bool validateWitness = opts.hasOption(Options::VALIDATE_RESULT);
    assert(not validateWitness || opts.getOption(Options::VALIDATE_RESULT) == std::string("true"));
    bool printWitness = opts.hasOption(Options::PRINT_WITNESS);
    assert(not printWitness || opts.getOption(Options::PRINT_WITNESS) == std::string("true"));
    if (not printWitness and not validateWitness) { return; }

    result = translator.translate(std::move(result));
    if (not result.hasWitness()) {
        if (validateWitness) { std::cout << "Internal witness validation failed!" << std::endl; }
        std::cerr << ";No witness has been computed.\n;Reason: " << result.getNoWitnessReason() << std::endl;
        return;
    }
    if (printWitness) {
        auto format = opts.getOrDefault(Options::PROOF_FORMAT, "legacy");
        result.printWitness(std::cout, logic, originalGraph, originalAssertions, normalizingEqualities, format);
    }
    if (validateWitness) {
        auto validationResult = Validator(logic).validate(originalGraph, result);
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

namespace {
void printAnswer(VerificationAnswer answer) {
    switch (answer) {
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
            break;
    }
}
} // namespace

void ChcInterpreterContext::solveWithMultipleEngines(std::string const & engineStr,
                                                     std::unique_ptr<ChcDirectedHyperGraph> hyperGraph,
                                                     std::unique_ptr<ChcDirectedHyperGraph> originalGraph,
                                                     std::unique_ptr<WitnessBackTranslator> translator,
                                                     Normalizer::Equalities const & normalizingEqualities) {
    std::vector<std::string> engines;
    std::stringstream ss(engineStr);
    std::string token;
    while (std::getline(ss, token, ',')) {
        engines.push_back(token);
    }
    pid_t const parent = getpid();
    std::vector<pid_t> processes;
    void * mptr = mmap(nullptr, sizeof(pid_t), PROT_READ | PROT_WRITE, MAP_SHARED | MAP_ANONYMOUS, -1, 0);
    if (mptr == MAP_FAILED) {
        reportError("Problem setting up multi-engine run");
        exit(1);
    }
    pid_t * winner_pid = static_cast<pid_t *>(mptr);
    *winner_pid = -1;
    for (uint i = 0; i < engines.size(); i++) {
        if (getpid() == parent) { processes.push_back(fork()); }
        if (processes[i] == 0) {
            // child process
            auto result = solve(engines[i], *hyperGraph);
            if (result.getAnswer() == VerificationAnswer::UNKNOWN) { exit(1); }
            if (__sync_bool_compare_and_swap(winner_pid, -1, getpid())) {
                printAnswer(result.getAnswer());
                if (hasWorkAfterAnswer()) {
                    doWorkAfterAnswer(std::move(result), *originalGraph, *translator, normalizingEqualities);
                }
                exit(0);
            } else {
                exit(1); // Exit with error so that the main process would not kill the child working on witness
            }
        }
    }

    auto guard = ScopeGuard{[&]() { munmap(winner_pid, sizeof(pid_t)); }};
    while (true) {
        int status;
        // Parent process waits until at least one child finishes
        pid_t done = wait(&status);
        if (done == -1) {
            // If all the children processes are finished, we stop
            if (errno == ECHILD) return;
        } else {
            // If some child process encountered error, we continue, otherwise if it returned
            // SAT/UNSAT we stop all other children and exit the parent process
            if (!WIFEXITED(status) || WEXITSTATUS(status) != 0) { continue; }
            for (auto k_p : processes) {
                kill(k_p, SIGKILL);
            }
            return;
        }
    }
}

void ChcInterpreterContext::interpretCheckSat() {
    Normalizer normalizer(logic);
    auto normalizedSystem = normalizer.normalize(*system);

    auto hypergraph = ChcGraphBuilder(logic).buildGraph(normalizedSystem);
    std::unique_ptr<ChcDirectedHyperGraph> originalGraph{nullptr};
    if (hasWorkAfterAnswer()) { // Store copy of the original graph for validating purposes
        originalGraph = std::make_unique<ChcDirectedHyperGraph>(*hypergraph);
    }

    auto pipeline = Transformations::defaultTransformationPipeline();
    auto [newGraph, translator] = pipeline.transform(std::move(hypergraph));
    hypergraph = std::move(newGraph);
    // This if is needed to run the portfolio of multiple engines
    auto engineName = opts.getOrDefault(Options::ENGINE, "spacer");
    if (engineName.find(',') != std::string::npos) {
        solveWithMultipleEngines(engineName, std::move(hypergraph), std::move(originalGraph), std::move(translator),
                                 normalizer.getNormalizingEqualities());
        return;
    }

    auto result = solve(engineName, *hypergraph);
    printAnswer(result.getAnswer());
    if (result.getAnswer() != VerificationAnswer::UNKNOWN and hasWorkAfterAnswer()) {
        doWorkAfterAnswer(std::move(result), *originalGraph, *translator, normalizer.getNormalizingEqualities());
    }
}

void ChcInterpreterContext::reportError(std::string const & msg) {
    std::cout << "(error " << '"' << msg << '"' << ")\n";
}

std::optional<ChClause> ChcInterpreterContext::chclauseFromPTRef(PTRef ref) {
    assert(ref != PTRef_Undef);
    Logic & logic = this->logic;
    PTRef disjunction = ref;
    if (not logic.isOr(disjunction)) {
        // special cases
        // 1. Head with empty body
        if (isUninterpretedPredicate(ref)) {
            return ChClause{.head = PTRefToCHC::constructHead(ref),
                            .body = PTRefToCHC::constructBody(logic.getTerm_true(), {})};
        } else if (logic.isNot(ref)) {
            PTRef argOfNot = logic.getPterm(ref)[0];
            // 2. Empty head, single predicate in body
            if (isUninterpretedPredicate(argOfNot)) {
                return ChClause{.head = PTRefToCHC::constructHead(logic.getTerm_false()),
                                .body = PTRefToCHC::constructBody(logic.getTerm_true(), {argOfNot})};
            } else if (logic.isAnd(argOfNot)) {
                // The clause is represented as negation of conjunction, turn it into disjunction
                vec<PTRef> args;
                for (int i = 0; i < logic.getPterm(argOfNot).size(); ++i) {
                    PTRef arg = logic.getPterm(argOfNot)[i];
                    args.push(logic.mkNot(arg));
                }
                disjunction = logic.mkOr(args);
            }
        }
    }
    if (not logic.isOr(disjunction)) { return std::nullopt; }
    // identify interpreted part and uninterpreted part
    vec<PTRef> disjuncts = TermUtils(logic).getTopLevelDisjuncts(disjunction);
    // find uninterpreted predicates (positive or negative)
    auto uninterpretedEnd = std::stable_partition(disjuncts.begin(), disjuncts.end(), [this, &logic](PTRef arg) {
        return this->isUninterpretedPredicate(arg) ||
               (logic.isNot(arg) && this->isUninterpretedPredicate(logic.getPterm(arg)[0]));
    });

    // find positive uninterpreted predicates
    auto positiveEnd = std::stable_partition(disjuncts.begin(), uninterpretedEnd,
                                             [&logic](PTRef arg) { return not logic.isNot(arg); });
    if (positiveEnd - disjuncts.begin() > 1) { return std::nullopt; }
    ChcHead head = positiveEnd == disjuncts.begin() ? PTRefToCHC::constructHead(logic.getTerm_false())
                                                    : PTRefToCHC::constructHead(*disjuncts.begin());
    // Negate the body so that it represents antecedent of the implication
    std::transform(positiveEnd, disjuncts.end(), positiveEnd, [&logic](PTRef bodyArg) { return logic.mkNot(bodyArg); });
    vec<PTRef> interpretedArgs;
    std::for_each(uninterpretedEnd, disjuncts.end(), [&interpretedArgs](PTRef arg) { interpretedArgs.push(arg); });
    PTRef interpretedPart = logic.mkAnd(interpretedArgs);
    if (matchingSubTerms(logic, interpretedPart, [&](PTRef term) {
            return this->isUninterpretedPredicate(term);
        }).size() > 0) {
        return std::nullopt;
    }

    ChcBody body = PTRefToCHC::constructBody(interpretedPart, positiveEnd, uninterpretedEnd);

    return ChClause{.head = std::move(head), .body = std::move(body)};
}

bool ChcInterpreterContext::isUninterpretedPredicate(PTRef ref) const {
    return system->isUninterpretedPredicate(logic.getSymRef(ref));
}
} // namespace golem