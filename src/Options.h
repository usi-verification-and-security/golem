//
// Created by Martin Blicha on 07.08.20.
//

#ifndef OPENSMT_OPTIONS_H
#define OPENSMT_OPTIONS_H

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
    static const std::string ACCELERATE_LOOPS;
    static const std::string COMPUTE_WITNESS;
    static const std::string PRINT_WITNESS;
    static const std::string LRA_ITP_ALG;
    static const std::string FORCED_COVERING;
    static const std::string VERBOSE;
    static const std::string TPA_USE_QE;
};

class CommandLineParser {
public:
    Options parse(int argc, char * argv[]);
};

#endif //OPENSMT_OPTIONS_H
