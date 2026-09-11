/*
 * Copyright (c) 2025 Verification and Security lab @ USI
 *
 * SPDX-License-Identifier: MIT
 */

/*
 * golem-qe: a standalone front end for golem's quantifier elimination.
 *
 * OpenSMT's term store is quantifier free, so a quantified formula can never
 * be built as a PTRef.  Its SMT-LIB2 *parser*, however, does understand
 * `exists`.  This front end exploits that: it parses the input into an AST,
 * strips the top level existential quantifier, turns every bound variable
 * into an ordinary free variable of the (quantifier free) logic, and hands
 * that list of variables to QuantifierElimination.  Nothing quantified ever
 * reaches the term store.
 *
 * Expected input shape:
 *
 *     (set-logic LIA)
 *     (declare-fun x () Int)            ; variables to preserve
 *     (assert (exists ((y Int) (b Bool)) <quantifier free body>))
 *     (check-sat)
 *
 * Any assertion without a quantifier is taken as is; several assertions are
 * conjoined and their existential prefixes merged.
 */

#include "QuantifierElimination.h"

#include "ChcInterpreter.h" // for golem::LetRecords
#include "osmt_parser.h"
#include "osmt_terms.h"

#include <chrono>
#include <cstdlib>
#include <cstring>
#include <iostream>
#include <optional>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <vector>

using namespace opensmt::tokens;

namespace {

std::string const versionString = "golem-qe 0.1 (golem " GOLEM_VERSION ")";

// ---------------------------------------------------------------------------
// Command line
// ---------------------------------------------------------------------------

enum class Mode { eliminate, keep };

struct CliOptions {
    std::string inputFile;
    std::optional<std::string> logic;
    Mode mode = Mode::eliminate;
    golem::QEOptions qe{};
    bool printUnder = false;
    bool printOver = false;
    bool csv = false;
    bool csvHeader = false;
    bool quiet = false;
    bool parseOnly = false;
};

[[noreturn]] void die(std::string const & msg) {
    std::cerr << "golem-qe: " << msg << '\n';
    std::exit(1);
}

void printUsage(std::ostream & out) {
    out << "usage: golem-qe [options] <file.smt2>\n"
           "\n"
           "Eliminates the existentially quantified variables of the input and reports\n"
           "the result together with timing information.\n"
           "\n"
           "Quantifier elimination options (QEOptions):\n"
           "  --over                    compute the over-approximation as well\n"
           "                            (QEOptions::compute_overapproximation; default: off,\n"
           "                            i.e. plain MBP producing only the precise result)\n"
           "  --max-disjunctions <n>    QEOptions::max_disjunctions_in_over; cap on the number\n"
           "                            of disjuncts of the over-approximation. 0 = no limit,\n"
           "                            1 = convex polyhedron. Implies --over. (default: 0)\n"
           "  --max-mbp-per-poly <n>    QEOptions::max_mbp_per_poly; cap on the number of MBPs\n"
           "                            per convex implicant. 0 = no limit; when exceeded the\n"
           "                            under-approximation is no longer precise.\n"
           "                            Implies --over. (default: 0)\n"
           "\n"
           "Model-based projection options (MBPOptions), passed to every MBP the\n"
           "procedure creates:\n"
           "  --fm-bound-threshold <n>  MBPOptions::fm_bound_threshold; up to this many bounds\n"
           "                            on a side, eliminate a variable by complete\n"
           "                            Fourier-Motzkin resolution instead of picking the\n"
           "                            single model-best bound (default: 3)\n"
           "  --[no-]pick-best-side     MBPOptions::pick_best_side; resolve on the side with\n"
           "                            fewer bounds, rather than always on the lower bounds\n"
           "                            (default: on)\n"
           "  --[no-]unsat-core         MBPOptions::use_unsat_core; collect the implicant with\n"
           "                            an unsat core instead of a plain model-based traversal\n"
           "                            (default: on)\n"
           "\n"
           "Problem options:\n"
           "  --mode <eliminate|keep>   call QuantifierElimination::eliminate on the bound\n"
           "                            variables (default), or ::keepOnly on the declared\n"
           "                            free variables\n"
           "  --logic <name>            override the logic; one of QF_LIA, QF_LRA, QF_ALIA\n"
           "                            (LIA/LRA/ALIA are accepted as aliases)\n"
           "\n"
           "Output options:\n"
           "  --print-under             print the under-approximation as SMT-LIB2\n"
           "  --print-over              print the over-approximation as SMT-LIB2\n"
           "  --print-result            same as --print-under --print-over\n"
           "  --csv                     emit one machine-readable CSV line instead of a report\n"
           "  --csv-header              print the CSV header and exit\n"
           "  --parse-only              read the problem and report its shape, run no QE\n"
           "  -q, --quiet               suppress the human-readable report\n"
           "  -h, --help                show this help\n"
           "  --version                 show the version\n";
}

int parseNonNegative(char const * text, char const * flag) {
    char * end = nullptr;
    long const value = std::strtol(text, &end, 10);
    if (end == text or *end != '\0' or value < 0 or value > 32767) {
        die(std::string(flag) + ": expected an integer in [0, 32767], got '" + text + "'");
    }
    return static_cast<int>(value);
}

CliOptions parseCli(int argc, char ** argv) {
    CliOptions options;
    bool sawOverFlag = false;
    for (int i = 1; i < argc; ++i) {
        std::string const arg = argv[i];
        auto next = [&](char const * flag) -> char const * {
            if (i + 1 >= argc) { die(std::string(flag) + " requires an argument"); }
            return argv[++i];
        };
        if (arg == "-h" or arg == "--help") {
            printUsage(std::cout);
            std::exit(0);
        } else if (arg == "--version") {
            std::cout << versionString << '\n';
            std::exit(0);
        } else if (arg == "--csv-header") {
            options.csvHeader = true;
        } else if (arg == "--over") {
            options.qe.compute_overapproximation = true;
            sawOverFlag = true;
        } else if (arg == "--max-disjunctions") {
            options.qe.max_disjunctions_in_over = static_cast<short>(parseNonNegative(next("--max-disjunctions"), "--max-disjunctions"));
            sawOverFlag = true;
        } else if (arg == "--max-mbp-per-poly") {
            options.qe.max_mbp_per_poly = static_cast<short>(parseNonNegative(next("--max-mbp-per-poly"), "--max-mbp-per-poly"));
            sawOverFlag = true;
        } else if (arg == "--fm-bound-threshold") {
            options.qe.mbp_options.fm_bound_threshold =
                static_cast<short>(parseNonNegative(next("--fm-bound-threshold"), "--fm-bound-threshold"));
        } else if (arg == "--pick-best-side") {
            options.qe.mbp_options.pick_best_side = true;
        } else if (arg == "--no-pick-best-side") {
            options.qe.mbp_options.pick_best_side = false;
        } else if (arg == "--unsat-core") {
            options.qe.mbp_options.use_unsat_core = true;
        } else if (arg == "--no-unsat-core") {
            options.qe.mbp_options.use_unsat_core = false;
        } else if (arg == "--mode") {
            std::string const value = next("--mode");
            if (value == "eliminate") {
                options.mode = Mode::eliminate;
            } else if (value == "keep") {
                options.mode = Mode::keep;
            } else {
                die("--mode: expected 'eliminate' or 'keep', got '" + value + "'");
            }
        } else if (arg == "--logic") {
            options.logic = next("--logic");
        } else if (arg == "--print-under") {
            options.printUnder = true;
        } else if (arg == "--print-over") {
            options.printOver = true;
        } else if (arg == "--print-result") {
            options.printUnder = options.printOver = true;
        } else if (arg == "--csv") {
            options.csv = true;
        } else if (arg == "--parse-only") {
            options.parseOnly = true;
        } else if (arg == "-q" or arg == "--quiet") {
            options.quiet = true;
        } else if (not arg.empty() and arg[0] == '-') {
            die("unknown option '" + arg + "' (try --help)");
        } else if (options.inputFile.empty()) {
            options.inputFile = arg;
        } else {
            die("more than one input file given ('" + options.inputFile + "' and '" + arg + "')");
        }
    }
    // The limits only have an effect when the over-approximation is computed.
    if (sawOverFlag) { options.qe.compute_overapproximation = true; }
    return options;
}

// ---------------------------------------------------------------------------
// Logic selection
// ---------------------------------------------------------------------------

std::unique_ptr<ArithLogic> makeLogic(std::string const & name) {
    if (name == "QF_LIA" or name == "LIA") { return std::make_unique<ArithLogic>(opensmt::Logic_t::QF_LIA); }
    if (name == "QF_LRA" or name == "LRA") { return std::make_unique<ArithLogic>(opensmt::Logic_t::QF_LRA); }
    if (name == "QF_ALIA" or name == "ALIA") { return std::make_unique<ArithLogic>(opensmt::Logic_t::QF_ALIA); }
    die("unsupported logic '" + name + "'; expected QF_LIA, QF_LRA or QF_ALIA");
}

// The logic object has to exist before any declaration is interpreted, so the
// (set-logic) command is looked up in a separate, very cheap pass.
std::optional<std::string> findSetLogic(ASTNode const & root) {
    if (not root.children) { return std::nullopt; }
    for (ASTNode const * command : *root.children) {
        if (command->getType() == CMD_T and command->getToken().x == t_setlogic and command->children and
            not command->children->empty()) {
            char const * name = (**command->children->begin()).getValue();
            if (name) { return std::string(name); }
        }
    }
    return std::nullopt;
}

// ---------------------------------------------------------------------------
// AST -> PTRef
// ---------------------------------------------------------------------------

struct ParseError : public std::runtime_error {
    explicit ParseError(std::string const & msg) : std::runtime_error(msg) {}
};

class QEFrontend {
public:
    explicit QEFrontend(ArithLogic & logic) : logic(logic) {}

    // Interprets the whole script.  Afterwards `formula` is the conjunction of
    // all assertions, `existentials` the merged existential prefix and
    // `preserved` the top level declarations, in declaration order.
    void interpret(ASTNode const & root) {
        if (not root.children) { throw ParseError("empty input"); }
        for (ASTNode * command : *root.children) {
            if (command->getType() != CMD_T) { continue; }
            switch (command->getToken().x) {
                case t_setlogic:
                case t_setinfo:
                case t_setoption:
                case t_checksat:
                case t_getmodel:
                    break; // handled elsewhere or irrelevant here
                case t_exit:
                    return;
                case t_declarefun:
                case t_declareconst:
                    declareVariable(*command);
                    break;
                case t_assert:
                    assertions.push(parseAssertion(**command->children->begin()));
                    break;
                default:
                    throw ParseError(std::string("unsupported command '") +
                                     tokenToName.at(command->getToken().x) + "'");
            }
        }
    }

    PTRef getFormula() const {
        if (assertions.size() == 0) { return logic.getTerm_true(); }
        return logic.mkAnd(assertions);
    }
    vec<PTRef> const & getExistentials() const { return existentials; }
    vec<PTRef> const & getPreserved() const { return preserved; }

private:
    ArithLogic & logic;
    golem::LetRecords letRecords;
    std::unordered_map<std::string, SRef> declaredSorts;
    vec<PTRef> assertions;
    vec<PTRef> existentials;
    vec<PTRef> preserved;

    // Same shape for (declare-fun name () S) and (declare-const name S):
    // children are [name, sort list, codomain sort].
    void declareVariable(ASTNode const & node) {
        auto it = node.children->begin();
        ASTNode const & nameNode = **(it++);
        ASTNode const & argsNode = **(it++);
        ASTNode const & sortNode = **(it++);
        char const * name = nameNode.getValue();
        if (not name) { throw ParseError("declaration without a name"); }
        if (argsNode.children and not argsNode.children->empty()) {
            throw ParseError(std::string("'") + name +
                             "' is declared with arguments; golem-qe only accepts variables "
                             "(0-ary declarations)");
        }
        preserved.push(mkVariable(name, sortFromASTNode(sortNode)));
    }

    PTRef mkVariable(char const * name, SRef sort) {
        auto [it, inserted] = declaredSorts.emplace(name, sort);
        if (not inserted and it->second != sort) {
            throw ParseError(std::string("'") + name + "' is used with two different sorts (" +
                             logic.printSort(it->second) + " and " + logic.printSort(sort) + ")");
        }
        return logic.mkVar(sort, name);
    }

    SRef sortFromASTNode(ASTNode const & node) const {
        SRef sort = SRef_Undef;
        if (node.getType() == SYM_T) {
            SortSymbol const symbol(node.getValue(), 0);
            SSymRef symRef;
            if (logic.peekSortSymbol(symbol, symRef)) { sort = logic.getSort(symRef, {}); }
        } else if (node.getType() == LID_T and node.children and not node.children->empty()) {
            ASTNode const & name = **(node.children->begin());
            SortSymbol const symbol(name.getValue(), node.children->size() - 1);
            SSymRef symRef;
            if (logic.peekSortSymbol(symbol, symRef)) {
                vec<SRef> args;
                for (auto it = node.children->begin() + 1; it != node.children->end(); ++it) {
                    args.push(sortFromASTNode(**it));
                }
                sort = logic.getSort(symRef, std::move(args));
            }
        }
        if (sort == SRef_Undef) { throw ParseError("unknown sort in declaration"); }
        return sort;
    }

    // Pops the let frames it pushed, in reverse order, when it goes out of scope.
    class FrameGuard {
        golem::LetRecords & records;
        std::size_t count = 0;

    public:
        explicit FrameGuard(golem::LetRecords & records) : records(records) {}
        FrameGuard(FrameGuard const &) = delete;
        FrameGuard & operator=(FrameGuard const &) = delete;
        ~FrameGuard() {
            for (std::size_t i = 0; i < count; ++i) {
                records.popFrame();
            }
        }
        void bind(char const * name, PTRef term) {
            records.pushFrame();
            records.addBinding(name, term);
            ++count;
        }
    };

    // Strips the (possibly nested) existential prefix of a top level assertion.
    // Bound variables become plain free variables and are collected for QE.
    // A separate frame per variable mirrors ChcInterpreter's handling of
    // `forall`: the same name may be bound at several sorts in one file.
    PTRef parseAssertion(ASTNode const & node) {
        if (node.getType() == FORALL_T) {
            throw ParseError("universal quantification is not supported; "
                             "golem-qe eliminates existentials only");
        }
        if (node.getType() != EXISTS_T) { return parseTerm(node); }

        auto it = node.children->begin();
        ASTNode const & boundVars = **(it++);
        assert(boundVars.getType() == SVL_T);
        FrameGuard guard(letRecords);
        for (ASTNode const * var : *boundVars.children) {
            assert(var and var->getType() == SV_T);
            char const * name = var->getValue();
            PTRef const term = mkVariable(name, sortFromASTNode(**var->children->begin()));
            guard.bind(name, term);
            existentials.push(term);
        }
        return parseAssertion(**it);
    }

    PTRef parseTerm(ASTNode const & node) {
        switch (node.getType()) {
            case TERM_T:
                return logic.mkConst((**node.children->begin()).getValue());
            case QID_T: {
                char const * name = (**node.children->begin()).getValue();
                PTRef const bound = letRecords.getOrUndef(name);
                if (bound != PTRef_Undef) { return bound; }
                PTRef const term = logic.resolveTerm(name, {});
                if (term == PTRef_Undef) {
                    throw ParseError(std::string("undeclared symbol '") + name + "'");
                }
                return term;
            }
            case LQID_T: {
                auto it = node.children->begin();
                char const * name = (**it).getValue();
                vec<PTRef> args;
                for (++it; it != node.children->end(); ++it) {
                    args.push(parseTerm(**it));
                }
                PTRef const term = logic.resolveTerm(name, std::move(args));
                if (term == PTRef_Undef) {
                    throw ParseError(std::string("cannot resolve application of '") + name + "'");
                }
                return term;
            }
            case LET_T:
                return parseLet(node);
            case EXISTS_T:
            case FORALL_T:
                throw ParseError("quantifier below the top level of an assertion is not supported");
            default:
                throw ParseError(std::string("unexpected term of type ") + node.typeToStr());
        }
    }

    PTRef parseLet(ASTNode const & node) {
        auto it = node.children->begin();
        // Every bound term is built in the enclosing scope, before any of the
        // new names becomes visible.
        std::vector<std::string> names;
        vec<PTRef> values;
        for (ASTNode const * binding : *(**it).children) {
            values.push(parseTerm(**binding->children->begin()));
            names.emplace_back(binding->getValue());
        }
        FrameGuard guard(letRecords);
        for (std::size_t i = 0; i < names.size(); ++i) {
            // `names` outlives the guard, so these pointers stay valid.
            guard.bind(names[i].c_str(), values[static_cast<int>(i)]);
        }
        ++it;
        return parseTerm(**it);
    }
};

// ---------------------------------------------------------------------------
// Reporting
// ---------------------------------------------------------------------------

std::string asSmtLib(ArithLogic const & logic, PTRef term) {
    std::string out;
    for (PTRef var : opensmt::variables(logic, term)) {
        out += "(declare-fun " + logic.printTerm(var) + " () " + logic.printSort(logic.getSortRef(var)) + ")\n";
    }
    out += "(assert " + logic.printTerm(term) + ")\n";
    return out;
}

std::size_t nodeCount(ArithLogic const & logic, PTRef term) {
    return term == PTRef_Undef ? 0 : static_cast<std::size_t>(opensmt::subTerms(logic, term).size());
}

char const * csvHeaderLine =
    "file,logic,mode,compute_over,max_disjunctions,max_mbp_per_poly,"
    "fm_bound_threshold,pick_best_side,unsat_core,preserved,eliminated,"
    "parse_ms,qe_ms,precise_under,precise_over,under_nodes,over_nodes,under_vars,status";

} // namespace

int main(int argc, char ** argv) {
    CliOptions const options = parseCli(argc, argv);
    if (options.csvHeader) {
        std::cout << csvHeaderLine << '\n';
        if (options.inputFile.empty()) { return 0; }
    }
    if (options.inputFile.empty()) { die("no input file given (try --help)"); }

    FILE * in = fopen(options.inputFile.c_str(), "rt");
    if (in == nullptr) { die("cannot open '" + options.inputFile + "'"); }

    auto const parseStart = std::chrono::steady_clock::now();
    Smt2newContext context(in);
    int const parseResult = osmt_yyparse(&context);
    fclose(in);
    if (parseResult != 0) { die("cannot parse '" + options.inputFile + "'"); }
    ASTNode const * root = context.getRoot();
    if (root == nullptr) { die("empty input '" + options.inputFile + "'"); }

    std::string const logicName =
        options.logic.value_or(findSetLogic(*root).value_or("QF_LIA"));
    auto logic = makeLogic(logicName);

    QEFrontend frontend(*logic);
    PTRef formula = PTRef_Undef;
    try {
        frontend.interpret(*root);
        formula = frontend.getFormula();
    } catch (ParseError const & error) {
        die(options.inputFile + ": " + error.what());
    }
    auto const parseEnd = std::chrono::steady_clock::now();

    auto const & existentials = frontend.getExistentials();
    auto const & preserved = frontend.getPreserved();

    auto millis = [](auto from, auto to) {
        return std::chrono::duration_cast<std::chrono::milliseconds>(to - from).count();
    };
    auto const parseMs = millis(parseStart, parseEnd);

    if (options.parseOnly) {
        if (not options.quiet) {
            std::cout << options.inputFile << ": logic=" << logicName << " preserved=" << preserved.size()
                      << " eliminated=" << existentials.size() << " formula-nodes=" << nodeCount(*logic, formula)
                      << " parse-ms=" << parseMs << '\n';
        }
        return 0;
    }

    auto const qeStart = std::chrono::steady_clock::now();
    golem::QEResult result = options.mode == Mode::eliminate
                                 ? golem::QuantifierElimination(*logic).eliminate(formula, existentials, options.qe)
                                 : golem::QuantifierElimination(*logic).keepOnly(formula, preserved, options.qe);
    auto const qeEnd = std::chrono::steady_clock::now();

    auto const qeMs = millis(qeStart, qeEnd);

    bool const haveOver = options.qe.compute_overapproximation and result.over != PTRef_Undef;
    std::size_t const underNodes = nodeCount(*logic, result.under);
    std::size_t const overNodes = haveOver ? nodeCount(*logic, result.over) : 0;
    std::size_t const underVars =
        result.under == PTRef_Undef ? 0 : static_cast<std::size_t>(opensmt::variables(*logic, result.under).size());
    char const * status = result.under == logic->getTerm_true()    ? "true"
                          : result.under == logic->getTerm_false() ? "false"
                                                                   : "formula";

    if (options.csv) {
        std::cout << options.inputFile << ',' << logicName << ','
                  << (options.mode == Mode::eliminate ? "eliminate" : "keep") << ','
                  << (options.qe.compute_overapproximation ? 1 : 0) << ','
                  << options.qe.max_disjunctions_in_over << ',' << options.qe.max_mbp_per_poly << ','
                  << options.qe.mbp_options.fm_bound_threshold << ','
                  << (options.qe.mbp_options.pick_best_side ? 1 : 0) << ','
                  << (options.qe.mbp_options.use_unsat_core ? 1 : 0) << ','
                  << preserved.size() << ',' << existentials.size() << ',' << parseMs << ',' << qeMs << ','
                  << (result.precise_under ? 1 : 0) << ',' << (haveOver ? (result.precise_over ? 1 : 0) : -1) << ','
                  << underNodes << ',' << (haveOver ? static_cast<long>(overNodes) : -1L) << ',' << underVars << ','
                  << status << '\n';
    } else if (not options.quiet) {
        std::cout << "input                  : " << options.inputFile << '\n'
                  << "logic                  : " << logicName << '\n'
                  << "mode                   : " << (options.mode == Mode::eliminate ? "eliminate" : "keepOnly") << '\n'
                  << "compute_overapprox     : " << (options.qe.compute_overapproximation ? "true" : "false") << '\n'
                  << "max_disjunctions_in_over: " << options.qe.max_disjunctions_in_over << '\n'
                  << "max_mbp_per_poly       : " << options.qe.max_mbp_per_poly << '\n'
                  << "fm_bound_threshold     : " << options.qe.mbp_options.fm_bound_threshold << '\n'
                  << "pick_best_side         : " << (options.qe.mbp_options.pick_best_side ? "true" : "false") << '\n'
                  << "use_unsat_core         : " << (options.qe.mbp_options.use_unsat_core ? "true" : "false") << '\n'
                  << "preserved variables    : " << preserved.size() << '\n'
                  << "eliminated variables   : " << existentials.size() << '\n'
                  << "parse time             : " << parseMs << " ms\n"
                  << "qe time                : " << qeMs << " ms\n"
                  << "result                 : " << status << '\n'
                  << "under: precise=" << (result.precise_under ? "yes" : "no") << " nodes=" << underNodes
                  << " vars=" << underVars << '\n';
        if (haveOver) {
            std::cout << "over : precise=" << (result.precise_over ? "yes" : "no") << " nodes=" << overNodes << '\n';
        }
    }

    if (options.printUnder and result.under != PTRef_Undef) {
        std::cout << "; under-approximation (precise result unless stated otherwise)\n"
                  << "(set-logic " << logicName << ")\n"
                  << asSmtLib(*logic, result.under) << "(check-sat)\n";
    }
    if (options.printOver and haveOver) {
        std::cout << "; over-approximation\n"
                  << "(set-logic " << logicName << ")\n"
                  << asSmtLib(*logic, result.over) << "(check-sat)\n";
    }
    return 0;
}
