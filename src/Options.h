/*
 * Copyright (c) 2020-2025, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef GOLEM_OPTIONS_H
#define GOLEM_OPTIONS_H

#include <map>
#include <optional>
#include <string>

namespace golem {
class Options {
    std::map<std::string, std::string> options;

public:
    void addOption(std::string key, std::string value) { options.emplace(std::move(key), std::move(value)); }

    [[nodiscard]] std::optional<std::string> getOption(std::string const & key) const {
        auto it = options.find(key);
        return it == options.end() ? std::nullopt : std::optional<std::string>(it->second);
    }

    [[nodiscard]] std::string getOrDefault(std::string const & key, std::string const & def) const {
        auto it = options.find(key);
        return it == options.end() ? def : it->second;
    }

    [[nodiscard]] bool hasOption(std::string const & key) const {
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
    static const std::string IC3IA_USE_UNSAT_CORE_GENERALIZATION;
    static const std::string IC3IA_ADD_INITIAL_RESET;
    static const std::string SPACER_MAYPOB;
    static const std::string SPACER_BMBP;
    static const std::string SPACER_CC;
    static const std::string SPACER_CC_LEMMA;
    static const std::string SPACER_CC_POB;
    static const std::string SPACER_CC_UPDATE;
    static const std::string SPACER_INDGEN;
    static const std::string SPACER_RELIND;
    static const std::string SPACER_MBP_MAY_SUMMARY;
    static const std::string SPACER_GLOBAL_POB_DB;
    static const std::string SPACER_MAYPO_GAS;
    static const std::string SPACER_MAYPO_TRIGGER;
    static const std::string SPACER_MAX_LEMMAS_CC;
    static const std::string SPACER_MIN_POBS_CC;
    static const std::string SPACER_MAX_POBS_CC;
    static const std::string FORCE_TS;
    static const std::string SIMPLIFY_NESTED;
    static const std::string TERMINATION_BACKEND;
};

class CommandLineParser {
public:
    Options parse(int argc, char * argv[]);
};
} // namespace golem
#endif // GOLEM_OPTIONS_H
