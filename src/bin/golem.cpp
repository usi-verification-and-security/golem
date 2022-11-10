/*
 * Copyright (c) 2020-2022, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "ChcInterpreter.h"
#include "Options.h"

#include "osmt_terms.h"
#include "osmt_parser.h"

#include <memory>

void error(std::string const & msg) {
    std::cerr << msg << '\n';
    exit(1);
}

int main( int argc, char * argv[] ) {
    SMTConfig c;

    CommandLineParser parser;
    auto options = parser.parse(argc, argv);
    auto inputFile = options.getOption(Options::INPUT_FILE);
    auto logicToUse = options.getOption(Options::LOGIC);
    auto logic = [](std::string const & logic_str) -> std::unique_ptr<Logic> {
        if (logic_str == std::string("QF_LRA")) {
            return std::make_unique<ArithLogic>(opensmt::Logic_t::QF_LRA);
        } else if (logic_str == std::string("QF_LIA")) {
            return std::make_unique<ArithLogic>(opensmt::Logic_t::QF_LIA);
        } else {
            error("Unknown logic specified: " + logic_str);
            exit(1);
        }
    }(logicToUse);

    if (inputFile.empty()) {
        error("No input file provided");
    }
    {
        FILE * fin = nullptr;
        // check the file
        const char * filename = inputFile.c_str();
        assert(filename);

        if ((fin = fopen(filename, "rt")) == nullptr) {
            error("can't open file");
        }

        const char * extension = strrchr( filename, '.' );
        if (extension != nullptr && strcmp(extension, ".smt2") == 0) {
            Smt2newContext context(fin);
            int rval = smt2newparse(&context);
            if (rval != 0) {
                fclose(fin);
                error("Eror when parsing input file");
            }
            ChcInterpreter interpreter(options);
            interpreter.interpretSystemAst(*logic, context.getRoot());
            fclose(fin);
        }
        else {
            fclose(fin);
            error(inputFile + " extension not recognized. File must be in smt-lib2 format (extension .smt2)");
        }
    }
}

