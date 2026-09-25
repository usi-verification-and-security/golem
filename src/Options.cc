/*
 * Copyright (c) 2020-2025, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "Options.h"
#include "getopt.h"

#include <cassert>
#include <cstring>
#include <iostream>

namespace golem {
const std::string Options::INPUT_FILE = "input";
const std::string Options::LOGIC = "logic";
const std::string Options::ENGINE = "engine";
const std::string Options::ANALYSIS_FLOW = "flow";
const std::string Options::VALIDATE_RESULT = "validate";
const std::string Options::COMPUTE_WITNESS = "compute-witness";
const std::string Options::PRINT_WITNESS = "print-witness";
const std::string Options::LRA_ITP_ALG = "lra-itp-algorithm";
const std::string Options::FORCED_COVERING = "forced-covering";
const std::string Options::VERBOSE = "verbose";
const std::string Options::TPA_USE_QE = "tpa.use-qe";
const std::string Options::IC3IA_USE_UNSAT_CORE_GENERALIZATION = "ic3ia.unsat-core-generalization";
const std::string Options::IC3IA_ADD_INITIAL_RESET = "ic3ia.initial-reset";
const std::string Options::SPACER_MAYPOB = "spacer.maypob";
const std::string Options::SPACER_BMBP = "spacer.bmbp";
const std::string Options::SPACER_CC = "spacer.cc";
const std::string Options::SPACER_CC_LEMMA = "spacer.cc-lemma";
const std::string Options::SPACER_CC_POB = "spacer.cc-pob";
const std::string Options::SPACER_INDGEN = "spacer.indgen";
const std::string Options::SPACER_RELIND = "spacer.relind";
const std::string Options::SPACER_MBP_MAY_SUMMARY = "spacer.mbp-may-summary";
const std::string Options::SPACER_GLOBAL_POB_DB = "spacer.global-pob-db";
const std::string Options::SPACER_MAYPO_GAS = "spacer.maypo-gas";
const std::string Options::SPACER_MAYPO_TRIGGER = "spacer.maypo-trigger";
const std::string Options::SPACER_MAX_LEMMAS_CC = "spacer.max-lemmas-cc";
const std::string Options::SPACER_MIN_POBS_CC = "spacer.min-pobs-cc";
const std::string Options::SPACER_MAX_POBS_CC = "spacer.max-pobs-cc";
const std::string Options::FORCE_TS = "force-ts";
const std::string Options::SIMPLIFY_NESTED = "simplify-nested";
const std::string Options::PROOF_FORMAT = "proof-format";
const std::string Options::TERMINATION_BACKEND = "termination-backend";

namespace {

void printUsage() {
    std::cout
        << "Usage: golem [options] [-i] file\n"
           "\n"
           "-h,--help                       Print this help message\n"
           "--version                       Print version number of Golem\n"
           "-l,--logic <name>               SMT-LIB logic to use (required); possible values: QF_LRA, QF_LIA\n"
           "-e,--engine <name>              Select engine to use; supported engines:\n"
           "                                  bmc - Bounded Model Checking (only linear systems)\n"
           "                                  dar - Dual Approximated Reachability (only linear systems)\n"
           "                                  ic3ia - IC3 with Implicit Predicate Abstraction (only linear systems)\n"
           "                                  imc - McMillan's original Interpolation-based model checking (only linear systems)\n"
           "                                  kind - basic k-induction algorithm (only transition systems)\n"
           "                                  lawi - Lazy Abstraction with Interpolants (only linear systems)\n"
           "                                  pa - basic predicate abstraction with CEGAR (any system)\n"
           "                                  pdkind - Property directed k-induction (only linear systems)\n"
           "                                  se - forward symbolic execution (only linear system)\n"
           "                                  spacer - custom implementation of Spacer (any system)\n"
           "                                  split-tpa - Split Transition Power Abstraction (only linear systems)\n"
           "                                  tpa - Transition Power Abstraction (only linear systems)\n"
           "                                  trl - Transitive Relations Learning (only linear systems)\n"
           "--validate                      Internally validate computed solution\n"
           "--print-witness                 Print computed solution\n"
           "--proof-format <name>           Proof format to use; supported formats:\n"
           "                                  legacy (default) - golem's original proof format\n"
           "                                  intermediate - intermediate proof format (includes variable instantiation)\n"
           "                                  alethe (verifiable) - alethe proof format\n"
           "-v                              Increase verbosity (can be applied multiple times)\n"
           "-i,--input <file>               Input file (option not required)\n"
           "--force-ts                      Always encode linear system into transition system (affects BMC and TPA)\n"
           "--spacer.maypob[=bool]          Spacer: enable may-proof-obligations from all\n"
           "                                  sources (implies --spacer.bmbp --spacer.cc)\n"
           "--spacer.bmbp[=bool]            Spacer: may-POBs from bidirectional MBP\n"
           "--spacer.cc[=bool]              Spacer: may-POBs from both convex closures\n"
           "                                  (implies --spacer.cc-lemma --spacer.cc-pob)\n"
           "--spacer.cc-lemma[=bool]        Spacer: may-POBs from convex closure of lemmas\n"
           "--spacer.cc-pob[=bool]          Spacer: may-POBs from convex closure of the\n"
           "                                  under-approximations of the predecessors\n"
           "--spacer.indgen[=bool]          Spacer: inductive generalization of learnt lemmas;\n"
           "                                  also drives relative induction unless\n"
           "                                  --spacer.relind is given\n"
           "--spacer.relind[=bool]          Spacer: try to block a pob by relative induction before\n"
           "                                  creating predecessors\n"
           "--spacer.mbp-may-summary[=bool] Spacer: keep the may-summary in the MBP argument\n"
           "                                  when computing a predecessor (default: false)\n"
           "--spacer.global-pob-db[=bool]   Spacer: store the blocking lemmas of a pob independently\n"
           "                                  of its bound, and trigger CC-lemma on its visits across\n"
           "                                  bounds; the predecessor caches of BMBP and CC-pob stay\n"
           "                                  per bound (default: false)\n"
           "--spacer.maypo-gas <n>          Spacer: length of the predecessor chain a may-POB\n"
           "                                  may spawn; n >= 1 (default: 20)\n"
           "--spacer.maypo-trigger <n>      Spacer: visits of a pob before may-POBs are built\n"
           "                                  from it; n >= 1 (default: 3)\n"
           "--spacer.max-lemmas-cc <n>      Spacer: blocking lemmas kept per pob for CC-lemma,\n"
           "                                  oldest dropped first; n >= 1 (default: 7)\n"
           "--spacer.min-pobs-cc <n>        Spacer: under-approximations of a predecessor needed\n"
           "                                  before CC-pob fires; n >= 1 (default: 2)\n"
           "--spacer.max-pobs-cc <n>        Spacer: under-approximations kept per predecessor for\n"
           "                                  CC-pob, oldest dropped first; n >= 1 (default: 7)\n"
           "--ic3ia.unsat-core-generalization[=bool]\n"
           "                                Use unsat-core-only cube generalization in IC3IA (default: true)\n"
           "--ic3ia.initial-reset[=bool]\n"
           "                                Add a reset state so IC3IA does not seed from the full init formula (default: true)\n"
           "--termination-backend <name>    Select backend algorithm for termination problems:\n"
           "                                  lasso-finder - searches for lasso in the system\n"
           "                                  nontermination-via-safety - gradually eliminates terminating traces from the system\n"
           "                                  step-counter - searches for upper bound on number of steps the system can make\n";
    std::cout << std::flush;
}

bool isDisableKeyword(const char * word) {
    return strcmp(word, "no") == 0 or strcmp(word, "false") == 0 or strcmp(word, "disable") == 0;
}
} // namespace

Options CommandLineParser::parse(int argc, char ** argv) {

    Options res;
    int validate = 0;
    int printWitness = 0;
    int computeWitness = 0;
    int lraItpAlg = 0;
    int forcedCovering = 0;
    int verbose = 0;
    int tpaUseQE = 0;
    int ic3iaUseUnsatCoreGeneralization = 0;
    int ic3iaAddInitialReset = 1;
    int printVersion = 0;
    int forceTS = 0;
    int simplifyNested = 0;
    // -1 means "not given on the command line"; getopt sets the flag to 1 when it sees the
    // option, and the handler below then resolves it to 0 or 1 according to the argument.
    int spacerMayPob = -1;
    int spacerBmbp = -1;
    int spacerCc = -1;
    int spacerCcLemma = -1;
    int spacerCcPob = -1;
    int spacerIndGen = -1;
    int spacerRelInd = -1;
    int spacerMbpMaySummary = -1;
    int spacerGlobalPobDb = -1;
    // identity tokens only: the raw argument is stored, so it can be validated with a
    // proper message instead of being silently atoi'd to 0
    int spacerMayPoGas = 0;
    int spacerMayPoTrigger = 0;
    int spacerMaxLemmasCc = 0;
    int spacerMinPobsCc = 0;
    int spacerMaxPobsCc = 0;

    struct option long_options[] = {{"help", no_argument, nullptr, 'h'},
                                    {"version", no_argument, &printVersion, 1},
                                    {Options::ENGINE.c_str(), required_argument, nullptr, 'e'},
                                    {Options::LOGIC.c_str(), required_argument, nullptr, 'l'},
                                    {Options::INPUT_FILE.c_str(), required_argument, nullptr, 'i'},
                                    {Options::ANALYSIS_FLOW.c_str(), required_argument, nullptr, 'f'},
                                    {Options::VALIDATE_RESULT.c_str(), no_argument, &validate, 1},
                                    {Options::PRINT_WITNESS.c_str(), no_argument, &printWitness, 1},
                                    {Options::COMPUTE_WITNESS.c_str(), optional_argument, &computeWitness, 1},
                                    {Options::LRA_ITP_ALG.c_str(), required_argument, &lraItpAlg, 0},
                                    {Options::FORCED_COVERING.c_str(), optional_argument, &forcedCovering, 1},
                                    {Options::VERBOSE.c_str(), optional_argument, &verbose, 1},
                                    {Options::TPA_USE_QE.c_str(), optional_argument, &tpaUseQE, 1},
                                    {Options::IC3IA_USE_UNSAT_CORE_GENERALIZATION.c_str(), optional_argument, &ic3iaUseUnsatCoreGeneralization, 1},
                                    {Options::IC3IA_ADD_INITIAL_RESET.c_str(), optional_argument, &ic3iaAddInitialReset, 1},
                                    {Options::SPACER_MAYPOB.c_str(), optional_argument, &spacerMayPob, 1},
                                    {Options::SPACER_BMBP.c_str(), optional_argument, &spacerBmbp, 1},
                                    {Options::SPACER_CC.c_str(), optional_argument, &spacerCc, 1},
                                    {Options::SPACER_CC_LEMMA.c_str(), optional_argument, &spacerCcLemma, 1},
                                    {Options::SPACER_CC_POB.c_str(), optional_argument, &spacerCcPob, 1},
                                    {Options::SPACER_INDGEN.c_str(), optional_argument, &spacerIndGen, 1},
                                    {Options::SPACER_RELIND.c_str(), optional_argument, &spacerRelInd, 1},
                                    {Options::SPACER_MBP_MAY_SUMMARY.c_str(), optional_argument, &spacerMbpMaySummary, 1},
                                    {Options::SPACER_GLOBAL_POB_DB.c_str(), optional_argument, &spacerGlobalPobDb, 1},
                                    {Options::SPACER_MAYPO_GAS.c_str(), required_argument, &spacerMayPoGas, 1},
                                    {Options::SPACER_MAYPO_TRIGGER.c_str(), required_argument, &spacerMayPoTrigger, 1},
                                    {Options::SPACER_MAX_LEMMAS_CC.c_str(), required_argument, &spacerMaxLemmasCc, 1},
                                    {Options::SPACER_MIN_POBS_CC.c_str(), required_argument, &spacerMinPobsCc, 1},
                                    {Options::SPACER_MAX_POBS_CC.c_str(), required_argument, &spacerMaxPobsCc, 1},
                                    {Options::PROOF_FORMAT.c_str(), required_argument, nullptr, 'p'},
                                    {Options::FORCE_TS.c_str(), no_argument, &forceTS, 1},
                                    {Options::SIMPLIFY_NESTED.c_str(), no_argument, &simplifyNested, 1},
                                    {Options::TERMINATION_BACKEND.c_str(), required_argument, nullptr, 0},
                                    {0, 0, 0, 0}};

    while (true) {
        int option_index = 0;

        int c = getopt_long(argc, argv, "e:l:i:f:vhp:", long_options, &option_index);
        if (c == -1) { break; }

        switch (c) {
            case 0:
                if (long_options[option_index].flag == &printVersion) {
                    std::cout << "Golem " << GOLEM_VERSION << std::endl;
                    exit(0);
                }
                if (long_options[option_index].flag == &computeWitness and optarg) {
                    if (isDisableKeyword(optarg)) { computeWitness = 0; }
                } else if (long_options[option_index].flag == &forcedCovering and optarg) {
                    if (isDisableKeyword(optarg)) {
                        forcedCovering = 0;
                    } else {
                        forcedCovering = 1;
                    }
                } else if (long_options[option_index].flag == &tpaUseQE) {
                    tpaUseQE = 1;
                } else if (long_options[option_index].flag == &ic3iaUseUnsatCoreGeneralization and optarg) {
                    if (isDisableKeyword(optarg)) {
                        ic3iaUseUnsatCoreGeneralization = 0;
                    } else {
                        ic3iaUseUnsatCoreGeneralization = 1;
                    }
                } else if (long_options[option_index].flag == &ic3iaAddInitialReset and optarg) {
                    if (isDisableKeyword(optarg)) {
                        ic3iaAddInitialReset = 0;
                    } else {
                        ic3iaAddInitialReset = 1;
                    }
                } else if (long_options[option_index].flag == &lraItpAlg) {
                    assert(optarg);
                    lraItpAlg = std::atoi(optarg);
                } else if (long_options[option_index].flag == &verbose) {
                    assert(optarg);
                    verbose = std::atoi(optarg);
                } else if (long_options[option_index].flag == &spacerMayPob) {
                    spacerMayPob = (optarg and isDisableKeyword(optarg)) ? 0 : 1;
                } else if (long_options[option_index].flag == &spacerBmbp) {
                    spacerBmbp = (optarg and isDisableKeyword(optarg)) ? 0 : 1;
                } else if (long_options[option_index].flag == &spacerCc) {
                    spacerCc = (optarg and isDisableKeyword(optarg)) ? 0 : 1;
                } else if (long_options[option_index].flag == &spacerCcLemma) {
                    spacerCcLemma = (optarg and isDisableKeyword(optarg)) ? 0 : 1;
                } else if (long_options[option_index].flag == &spacerCcPob) {
                    spacerCcPob = (optarg and isDisableKeyword(optarg)) ? 0 : 1;
                } else if (long_options[option_index].flag == &spacerIndGen) {
                    spacerIndGen = (optarg and isDisableKeyword(optarg)) ? 0 : 1;
                } else if (long_options[option_index].flag == &spacerRelInd) {
                    spacerRelInd = (optarg and isDisableKeyword(optarg)) ? 0 : 1;
                } else if (long_options[option_index].flag == &spacerMbpMaySummary) {
                    spacerMbpMaySummary = (optarg and isDisableKeyword(optarg)) ? 0 : 1;
                } else if (long_options[option_index].flag == &spacerGlobalPobDb) {
                    spacerGlobalPobDb = (optarg and isDisableKeyword(optarg)) ? 0 : 1;
                } else if (long_options[option_index].flag == &spacerMayPoGas) {
                    assert(optarg);
                    res.addOption(Options::SPACER_MAYPO_GAS, optarg);
                } else if (long_options[option_index].flag == &spacerMayPoTrigger) {
                    assert(optarg);
                    res.addOption(Options::SPACER_MAYPO_TRIGGER, optarg);
                } else if (long_options[option_index].flag == &spacerMaxLemmasCc) {
                    assert(optarg);
                    res.addOption(Options::SPACER_MAX_LEMMAS_CC, optarg);
                } else if (long_options[option_index].flag == &spacerMinPobsCc) {
                    assert(optarg);
                    res.addOption(Options::SPACER_MIN_POBS_CC, optarg);
                } else if (long_options[option_index].flag == &spacerMaxPobsCc) {
                    assert(optarg);
                    res.addOption(Options::SPACER_MAX_POBS_CC, optarg);
                } else if (long_options[option_index].flag == &forceTS) {
                    forceTS = 1;
                } else if (long_options[option_index].flag == &simplifyNested) {
                    simplifyNested = 1;
                } else if (long_options[option_index].name == Options::TERMINATION_BACKEND.c_str()) {
                    res.addOption(Options::TERMINATION_BACKEND, optarg);
                }
                break;
            case 'e':
                res.addOption(Options::ENGINE, optarg);
                break;
            case 'l':
                res.addOption(Options::LOGIC, optarg);
                break;
            case 'i':
                res.addOption(Options::INPUT_FILE, optarg);
                break;
            case 'f':
                res.addOption(Options::ANALYSIS_FLOW, optarg);
                break;
            case 'p':
                res.addOption(Options::PROOF_FORMAT, optarg);
                break;
            case 'v':
                ++verbose;
                break;
            case 'h':
                printUsage();
                exit(0);
            default:
                abort();
        }
    }
    if (optind < argc) {
        if (optind < argc - 1 || res.hasOption(Options::INPUT_FILE)) {
            std::cerr << "Error in parsing the command line argument" << '\n';
            printUsage();
            exit(1);
        }
        // Assume the last argument not assigned to any option is input file
        res.addOption(Options::INPUT_FILE, argv[optind]);
    }
    if (spacerMayPob >= 0) { res.addOption(Options::SPACER_MAYPOB, spacerMayPob ? "true" : "false"); }
    if (spacerBmbp >= 0) { res.addOption(Options::SPACER_BMBP, spacerBmbp ? "true" : "false"); }
    if (spacerCc >= 0) { res.addOption(Options::SPACER_CC, spacerCc ? "true" : "false"); }
    if (spacerCcLemma >= 0) { res.addOption(Options::SPACER_CC_LEMMA, spacerCcLemma ? "true" : "false"); }
    if (spacerCcPob >= 0) { res.addOption(Options::SPACER_CC_POB, spacerCcPob ? "true" : "false"); }
    if (spacerIndGen >= 0) { res.addOption(Options::SPACER_INDGEN, spacerIndGen ? "true" : "false"); }
    if (spacerRelInd >= 0) { res.addOption(Options::SPACER_RELIND, spacerRelInd ? "true" : "false"); }
    if (spacerMbpMaySummary >= 0) {
        res.addOption(Options::SPACER_MBP_MAY_SUMMARY, spacerMbpMaySummary ? "true" : "false");
    }
    if (spacerGlobalPobDb >= 0) {
        res.addOption(Options::SPACER_GLOBAL_POB_DB, spacerGlobalPobDb ? "true" : "false");
    }
    if (validate) { res.addOption(Options::VALIDATE_RESULT, "true"); }
    if (printWitness) { res.addOption(Options::PRINT_WITNESS, "true"); }
    if (validate || computeWitness || printWitness) { res.addOption(Options::COMPUTE_WITNESS, "true"); }
    if (forcedCovering) { res.addOption(Options::FORCED_COVERING, "true"); }
    if (tpaUseQE) { res.addOption(Options::TPA_USE_QE, "true"); }
    res.addOption(Options::IC3IA_USE_UNSAT_CORE_GENERALIZATION, ic3iaUseUnsatCoreGeneralization ? "true" : "false");
    res.addOption(Options::IC3IA_ADD_INITIAL_RESET, ic3iaAddInitialReset ? "true" : "false");
    if (forceTS) { res.addOption(Options::FORCE_TS, "true"); }
    if (simplifyNested) { res.addOption(Options::SIMPLIFY_NESTED, "true"); }
    res.addOption(Options::LRA_ITP_ALG, std::to_string(lraItpAlg));
    res.addOption(Options::VERBOSE, std::to_string(verbose));

    return res;
}
} // namespace golem
