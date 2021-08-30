//
// Created by Martin Blicha on 15.07.20.
//

#include "ChcInterpreter.h"
#include "Options.h"

#include "osmt_terms.h"
#include "osmt_parser.h"

#include <memory>

int main( int argc, char * argv[] ) {
    SMTConfig c;

    CommandLineParser parser;
    auto options = parser.parse(argc, argv);
    auto inputFile = options.getOption(Options::INPUT_FILE);
    auto logicToUse = options.getOption(Options::LOGIC);
    auto logic = [](std::string const & logic_str) {
        if (logic_str == std::string("QF_LRA")) {
            return std::unique_ptr<Logic>(new LRALogic());
        } else if (logic_str == std::string("QF_LIA")) {
            return std::unique_ptr<Logic>(new LIALogic());
        } else {
            opensmt_error2(logic_str.c_str(), "Unknown logic specified!");
        }
    }(logicToUse);
    logic->enableExtendedSignature(true);

    if (inputFile.empty()) {
        opensmt_error("No input file provided");
    }
    {
        FILE * fin = nullptr;
        // check the file
        const char * filename = inputFile.c_str();
        assert( filename );

        if ((fin = fopen(filename, "rt")) == nullptr) {
            opensmt_error("can't open file");
        }

        const char * extension = strrchr( filename, '.' );
        if ( extension != nullptr && strcmp( extension, ".smt2" ) == 0 ) {
            Smt2newContext context(fin);
            int rval = smt2newparse(&context);
            if (rval != 0) {
                fclose(fin);
                opensmt_error("Eror when parsing input file");
            }
            ChcInterpreter interpreter(options);
            interpreter.interpretSystemAst(*logic, context.getRoot());
            fclose(fin);
        }
        else {
            fclose(fin);
            opensmt_error2(filename, " extension not recognized. File must be in smt-lib2 format (extension .smt2)");
        }
    }



}

