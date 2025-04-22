/*
 * Copyright (c) 2020-2025, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "ChcInterpreter.h"
#include "Options.h"

#include "osmt_terms.h"
#include "osmt_parser.h"

namespace {
std::string tryDetectLogic(ASTNode const * root) {
    if (not root or not root->children) { return ""; }
    auto const & children = *(root->children);
    bool hasReals = false;
    bool hasIntegers = false;
    bool hasArrays = false;
    auto decide = [&]() -> std::string {
        if (hasReals and hasIntegers) { return ""; }
        return std::string("QF_") + (hasArrays ? "A" : "") + "L" + (hasIntegers ? "I" : "R") + "A";
    };
    for (ASTNode * child : children) {
        const tokens::smt2token token = child->getToken();
        switch (token.x) {
            case tokens::t_declarefun:
            {
                auto it = child->children->begin();
                ASTNode const & name_node = **(it++); (void)name_node;
                ASTNode const & args_node = **(it++);
                ASTNode const & ret_node  = **(it++); (void)ret_node;
                assert(it == child->children->end());
                auto checkForRealsAndInts = [&](ASTNode const * const node) {
                        hasReals = hasReals or strcmp(node->getValue(), "Real") == 0;
                        hasIntegers = hasIntegers or strcmp(node->getValue(), "Int") == 0;
                };
                for (ASTNode const * const argNode : *(args_node.children)) {
                    if (argNode->getType() == SYM_T) {
                        checkForRealsAndInts(argNode);
                    } else if (argNode->getType() == LID_T and argNode->children) {
                        for (ASTNode const * const node : *(argNode->children)) {
                            if (node->getType() == SYM_T) {
                                hasArrays = hasArrays or strcmp(node->getValue(), "Array") == 0;
                                checkForRealsAndInts(node);
                            }
                        }
                    }
                }
                break;
            }
            case tokens::t_assert:
                return decide();
            default:
                ;
        }
    }
    return "";
}

void error(std::string const & msg) {
    std::cerr << msg << '\n';
    exit(1);
}
} // namespace

using namespace golem;

int main( int argc, char * argv[] ) {
    SMTConfig c;

    CommandLineParser parser;
    auto options = parser.parse(argc, argv);
    auto inputFile = options.getOrDefault(Options::INPUT_FILE, "");
    auto logicFromString = [](std::string const & logic_str) -> std::unique_ptr<Logic> {
        if (logic_str == std::string("QF_LRA")) {
            return std::make_unique<ArithLogic>(opensmt::Logic_t::QF_LRA);
        } else if (logic_str == std::string("QF_LIA")) {
            return std::make_unique<ArithLogic>(opensmt::Logic_t::QF_LIA);
        } else if (logic_str == std::string("QF_ALIA")) {
            return std::make_unique<ArithLogic>(opensmt::Logic_t::QF_ALIA);
        } else {
            error("Unknown logic specified: " + logic_str);
            exit(1);
        }
    };
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
            int rval = osmt_yyparse(&context);
            if (rval != 0) {
                fclose(fin);
                error("Error when parsing input file");
            }
            auto logicStr = options.hasOption(Options::LOGIC) ? options.getOption(Options::LOGIC).value() : tryDetectLogic(context.getRoot());
            auto logic = logicFromString(logicStr);
            ChcInterpreter interpreter(options);
            interpreter.interpretSystemAst(*logic, context.getRoot());
            fclose(fin);
        }
        else {
            fclose(fin);
            error(inputFile + " extension not recognized. File must be in smt-lib2 format (extension .smt2)");
        }
    }
    return 0;
}

