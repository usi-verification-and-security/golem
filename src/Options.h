/*
 * Copyright (c) 2020-2022, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef GOLEM_OPTIONS_H
#define GOLEM_OPTIONS_H

#include <map>
#include <string>

class Options {
    std::map<std::string, std::string> options;
public:
    void addOption(std::string key, std::string value) {
        options.emplace(std::move(key), std::move(value));
    }

    std::string getOption(std::string const & key) const {
        auto it = options.find(key);
        return it == options.end() ? "" : it->second;
    }

    bool hasOption(std::string const & key) const {
        auto it = options.find(key);
        return it != options.end();
    }

    static const std::string INPUT_FILE;
    static const std::string LOGIC;
    static const std::string ENGINE;
    static const std::string ANALYSIS_FLOW;
    static const std::string VALIDATE_RESULT;
    static const std::string COMPUTE_WITNESS;
    static const std::string PRINT_WITNESS;
    static const std::string PROOF_FORMAT;
    static const std::string LRA_ITP_ALG;
    static const std::string FORCED_COVERING;
    static const std::string VERBOSE;
    static const std::string TPA_USE_QE;
    static const std::string FORCE_TS;
};

class CommandLineParser {
public:
    Options parse(int argc, char * argv[]);
};

#endif //GOLEM_OPTIONS_H
