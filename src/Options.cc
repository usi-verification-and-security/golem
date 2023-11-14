/*
 * Copyright (c) 2020-2022, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "Options.h"
#include "getopt.h"

#include <iostream>
#include <cstring>
#include <cassert>

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
const std::string Options::FORCE_TS = "force-ts";
const std::string Options::PROOF_FORMAT = "proof-format";

namespace{

void printUsage() {
    std::cout <<
        "Usage: golem [options] [-i] file\n"
        "\n"
        "-h,--help                  Print this help message\n"
        "--version                  Print version number of Golem\n"
        "-l,--logic <name>          SMT-LIB logic to use (required); possible values: QF_LRA, QF_LIA\n"
        "-e,--engine <name>         Select engine to use; supported engines:\n"
        "                               bmc - Bounded Model Checking (only transition systems)\n"
        "                               imc - McMillan's original Interpolation-based model checking (only transition systems)\n"
        "                               kind - basic k-induction algorithm (only transition systems)\n"
        "                               lawi - Lazy Abstraction with Interpolants (only linear CHC systems)\n"
        "                               spacer - custom implementation of Spacer (any CHC system)\n"
        "                               split-tpa - Split Transition Power Abstraction (only transition systems)\n"
        "                               tpa - Transition Power Abstraction (only transition systems)\n"
        "--validate                 Internally validate computed solution\n"
        "--print-witness            Print computed solution\n"
        "--proof-format <name>      Proof format to use; supported formats:\n"
        "                               legacy (default) - golem's original proof format\n"
        "                               intermediate - intermediate proof format (includes variable instantiation)\n"
        "                               alethe (verifiable) - alethe proof format\n"
        "-v                         Increase verbosity (can be applied multiple times)\n"
        "-i,--input <file>          Input file (option not required)\n"
        "--force-ts                 Enforces solving for a single TS (in case if there is a structure of TS, it is simplified into a single TS)\n"
        ;
    std::cout << std::flush;
}

bool isDisableKeyword(const char* word) {
    return strcmp(word, "no") == 0 or strcmp(word, "false") == 0 or strcmp(word, "disable") == 0;
}
}

Options CommandLineParser::parse(int argc, char ** argv) {

    Options res;
    int validate = 0;
    int printWitness = 0;
    int computeWitness = 0;
    int lraItpAlg = 0;
    int forcedCovering = 0;
    int verbose = 0;
    int tpaUseQE = 0;
    int printVersion = 0;
    int forceTS = 0;

    struct option long_options[] =
        {
            {"help", no_argument, nullptr, 'h'},
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
            {Options::PROOF_FORMAT.c_str(), required_argument, nullptr, 'p'},
            {Options::FORCE_TS.c_str(), no_argument, &forceTS, 1},
            {0, 0, 0, 0}
        };

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
                    if (isDisableKeyword(optarg)) {
                        computeWitness = 0;
                    }
                } else if (long_options[option_index].flag == &forcedCovering and optarg) {
                    if (isDisableKeyword(optarg)) {
                        forcedCovering = 0;
                    } else {
                        forcedCovering = 1;
                    }
                } else if (long_options[option_index].flag == &tpaUseQE) {
                    tpaUseQE = 1;
                } else if (long_options[option_index].flag == &lraItpAlg) {
                    assert(optarg);
                    lraItpAlg = std::atoi(optarg);
                }
                else if (long_options[option_index].flag == &verbose) {
                    assert(optarg);
                    verbose = std::atoi(optarg);
                } else if (long_options[option_index].flag == &forceTS) {
                    forceTS = 1;
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
    if (validate) {
        res.addOption(Options::VALIDATE_RESULT, "true");
    }
    if (printWitness) {
        res.addOption(Options::PRINT_WITNESS, "true");
    }
    if (validate || computeWitness || printWitness) {
        res.addOption(Options::COMPUTE_WITNESS, "true");
    }
    if (forcedCovering) {
        res.addOption(Options::FORCED_COVERING, "true");
    }
    if (tpaUseQE) {
        res.addOption(Options::TPA_USE_QE, "true");
    }
    if (forceTS) {
        res.addOption(Options::FORCE_TS, "true");
    }
    res.addOption(Options::LRA_ITP_ALG, std::to_string(lraItpAlg));
    res.addOption(Options::VERBOSE, std::to_string(verbose));

    return res;
}
