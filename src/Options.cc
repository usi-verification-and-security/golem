//
// Created by Martin Blicha on 07.08.20.
//

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
const std::string Options::ACCELERATE_LOOPS = "accelerate-loops";
const std::string Options::COMPUTE_WITNESS = "compute-witness";
const std::string Options::PRINT_WITNESS = "print-witness";
const std::string Options::LRA_ITP_ALG = "lra-itp-algorithm";
const std::string Options::FORCED_COVERING = "forced-covering";
const std::string Options::VERBOSE = "verbose";

namespace{
bool isDisableKeyword(const char* word) {
    return strcmp(word, "no") == 0 or strcmp(word, "false") == 0 or strcmp(word, "disable") == 0;
}
}

Options CommandLineParser::parse(int argc, char ** argv) {

    Options res;
    int validate = 0;
    int printWitness = 0;
    int accelerateLoops = 0;
    int computeWitness = 0;
    int lraItpAlg = 0;
    int forcedCovering = 0;
    int verbose = 0;

    struct option long_options[] =
        {
            {Options::ENGINE.c_str(), required_argument, nullptr, 'e'},
            {Options::LOGIC.c_str(), required_argument, nullptr, 'l'},
            {Options::INPUT_FILE.c_str(), required_argument, nullptr, 'i'},
            {Options::ANALYSIS_FLOW.c_str(), required_argument, nullptr, 'f'},
            {Options::VALIDATE_RESULT.c_str(), no_argument, &validate, 1},
            {Options::PRINT_WITNESS.c_str(), no_argument, &printWitness, 1},
            {Options::ACCELERATE_LOOPS.c_str(), optional_argument, &accelerateLoops, 1},
            {Options::COMPUTE_WITNESS.c_str(), optional_argument, &computeWitness, 1},
            {Options::LRA_ITP_ALG.c_str(), required_argument, &lraItpAlg, 0},
            {Options::FORCED_COVERING.c_str(), optional_argument, &forcedCovering, 1},
            {Options::VERBOSE.c_str(), optional_argument, &verbose, 1},
            {0, 0, 0, 0}
        };
    while (true) {
        int option_index = 0;

        int c = getopt_long(argc, argv, "e:l:i:f:v", long_options, &option_index);
        if (c == -1) { break; }

        switch (c) {
            case 0:
                if (long_options[option_index].flag == &accelerateLoops and optarg) {
                    if (isDisableKeyword(optarg)) {
                        accelerateLoops = 0;
                    } else {
                        accelerateLoops = 1;
                    }
                } else if (long_options[option_index].flag == &computeWitness and optarg) {
                    if (isDisableKeyword(optarg)) {
                        computeWitness = 0;
                    }
                } else if (long_options[option_index].flag == &forcedCovering and optarg) {
                    if (isDisableKeyword(optarg)) {
                        forcedCovering = 0;
                    } else {
                        forcedCovering = 1;
                    }
                } else if (long_options[option_index].flag == &lraItpAlg) {
                    assert(optarg);
                    lraItpAlg = std::atoi(optarg);
                }
                else if (long_options[option_index].flag == &verbose) {
                    assert(optarg);
                    verbose = std::atoi(optarg);
                }
                break;
            case 'e':
                res.addOption(Options::ENGINE, optarg);
//                printf ("option -e with value `%s'\n", optarg);
                break;
            case 'l':
                res.addOption(Options::LOGIC, optarg);
//                printf ("option -l with value `%s'\n", optarg);
                break;
            case 'i':
                res.addOption(Options::INPUT_FILE, optarg);
//                printf ("option -i with value `%s'\n", optarg);
                break;
            case 'f':
                res.addOption(Options::ANALYSIS_FLOW, optarg);
                break;
            case 'v':
                ++verbose;
                break;
            default:
                abort();
        }
    }
    if (optind < argc) {
        if (optind < argc - 1 || res.hasOption(Options::INPUT_FILE)) {
            std::cerr << "Error in parsing the command line argument" << std::endl;
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
    if (accelerateLoops) {
        res.addOption(Options::ACCELERATE_LOOPS, "true");
    }
    if (validate || printWitness || computeWitness) {
        res.addOption(Options::COMPUTE_WITNESS, "true");
    }
    if (forcedCovering) {
        res.addOption(Options::FORCED_COVERING, "true");
    }
    res.addOption(Options::LRA_ITP_ALG, std::to_string(lraItpAlg));
    res.addOption(Options::VERBOSE, std::to_string(verbose));

    return res;
}
