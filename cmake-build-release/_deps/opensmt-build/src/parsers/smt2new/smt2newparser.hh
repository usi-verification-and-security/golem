/* A Bison parser, made by GNU Bison 3.8.2.  */

/* Bison interface for Yacc-like parsers in C

   Copyright (C) 1984, 1989-1990, 2000-2015, 2018-2021 Free Software Foundation,
   Inc.

   This program is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <https://www.gnu.org/licenses/>.  */

/* As a special exception, you may create a larger work that contains
   part or all of the Bison parser skeleton and distribute that work
   under terms of your choice, so long as that work isn't itself a
   parser generator using the skeleton or a modified version thereof
   as a parser skeleton.  Alternatively, if you modify or redistribute
   the parser skeleton itself, you may (at your option) remove this
   special exception, which will cause the skeleton and the resulting
   Bison output files to be licensed under the GNU General Public
   License without this special exception.

   This special exception was added by the Free Software Foundation in
   version 2.2 of Bison.  */

/* DO NOT RELY ON FEATURES THAT ARE NOT DOCUMENTED in the manual,
   especially those whose name start with YY_ or yy_.  They are
   private implementation details that can be changed or removed.  */

#ifndef YY_SMT2NEW_HOME_MAMBO_GOLEM_CMAKE_BUILD_RELEASE_DEPS_OPENSMT_BUILD_SRC_PARSERS_SMT2NEW_SMT2NEWPARSER_HH_INCLUDED
# define YY_SMT2NEW_HOME_MAMBO_GOLEM_CMAKE_BUILD_RELEASE_DEPS_OPENSMT_BUILD_SRC_PARSERS_SMT2NEW_SMT2NEWPARSER_HH_INCLUDED
/* Debug traces.  */
#ifndef YYDEBUG
# define YYDEBUG 0
#endif
#if YYDEBUG
extern int smt2newdebug;
#endif

/* Token kinds.  */
#ifndef YYTOKENTYPE
# define YYTOKENTYPE
  enum yytokentype
  {
    YYEMPTY = -2,
    YYEOF = 0,                     /* "end of file"  */
    YYerror = 256,                 /* error  */
    YYUNDEF = 257,                 /* "invalid token"  */
    TK_AS = 258,                   /* TK_AS  */
    TK_DECIMAL = 259,              /* TK_DECIMAL  */
    TK_EXISTS = 260,               /* TK_EXISTS  */
    TK_FORALL = 261,               /* TK_FORALL  */
    TK_LET = 262,                  /* TK_LET  */
    TK_NUMERAL = 263,              /* TK_NUMERAL  */
    TK_PAR = 264,                  /* TK_PAR  */
    TK_STRING = 265,               /* TK_STRING  */
    TK_ASSERT = 266,               /* TK_ASSERT  */
    TK_CHECKSAT = 267,             /* TK_CHECKSAT  */
    TK_DECLARESORT = 268,          /* TK_DECLARESORT  */
    TK_DECLAREFUN = 269,           /* TK_DECLAREFUN  */
    TK_DECLARECONST = 270,         /* TK_DECLARECONST  */
    TK_DEFINESORT = 271,           /* TK_DEFINESORT  */
    TK_DEFINEFUN = 272,            /* TK_DEFINEFUN  */
    TK_EXIT = 273,                 /* TK_EXIT  */
    TK_GETASSERTIONS = 274,        /* TK_GETASSERTIONS  */
    TK_GETASSIGNMENT = 275,        /* TK_GETASSIGNMENT  */
    TK_GETINFO = 276,              /* TK_GETINFO  */
    TK_GETOPTION = 277,            /* TK_GETOPTION  */
    TK_GETPROOF = 278,             /* TK_GETPROOF  */
    TK_GETUNSATCORE = 279,         /* TK_GETUNSATCORE  */
    TK_GETVALUE = 280,             /* TK_GETVALUE  */
    TK_GETMODEL = 281,             /* TK_GETMODEL  */
    TK_POP = 282,                  /* TK_POP  */
    TK_PUSH = 283,                 /* TK_PUSH  */
    TK_SETLOGIC = 284,             /* TK_SETLOGIC  */
    TK_SETINFO = 285,              /* TK_SETINFO  */
    TK_SETOPTION = 286,            /* TK_SETOPTION  */
    TK_THEORY = 287,               /* TK_THEORY  */
    TK_GETITPS = 288,              /* TK_GETITPS  */
    TK_WRSTATE = 289,              /* TK_WRSTATE  */
    TK_RDSTATE = 290,              /* TK_RDSTATE  */
    TK_SIMPLIFY = 291,             /* TK_SIMPLIFY  */
    TK_WRFUNS = 292,               /* TK_WRFUNS  */
    TK_ECHO = 293,                 /* TK_ECHO  */
    TK_NUM = 294,                  /* TK_NUM  */
    TK_SYM = 295,                  /* TK_SYM  */
    TK_QSYM = 296,                 /* TK_QSYM  */
    TK_KEY = 297,                  /* TK_KEY  */
    TK_STR = 298,                  /* TK_STR  */
    TK_DEC = 299,                  /* TK_DEC  */
    TK_HEX = 300,                  /* TK_HEX  */
    TK_BIN = 301,                  /* TK_BIN  */
    KW_SORTS = 302,                /* KW_SORTS  */
    KW_FUNS = 303,                 /* KW_FUNS  */
    KW_SORTSDESCRIPTION = 304,     /* KW_SORTSDESCRIPTION  */
    KW_FUNSDESCRIPTION = 305,      /* KW_FUNSDESCRIPTION  */
    KW_DEFINITION = 306,           /* KW_DEFINITION  */
    KW_NOTES = 307,                /* KW_NOTES  */
    KW_THEORIES = 308,             /* KW_THEORIES  */
    KW_EXTENSIONS = 309,           /* KW_EXTENSIONS  */
    KW_VALUES = 310,               /* KW_VALUES  */
    KW_PRINTSUCCESS = 311,         /* KW_PRINTSUCCESS  */
    KW_EXPANDDEFINITIONS = 312,    /* KW_EXPANDDEFINITIONS  */
    KW_INTERACTIVEMODE = 313,      /* KW_INTERACTIVEMODE  */
    KW_PRODUCEPROOFS = 314,        /* KW_PRODUCEPROOFS  */
    KW_PRODUCEUNSATCORES = 315,    /* KW_PRODUCEUNSATCORES  */
    KW_PRODUCEMODELS = 316,        /* KW_PRODUCEMODELS  */
    KW_PRODUCEASSIGNMENTS = 317,   /* KW_PRODUCEASSIGNMENTS  */
    KW_REGULAROUTPUTCHANNEL = 318, /* KW_REGULAROUTPUTCHANNEL  */
    KW_DIAGNOSTICOUTPUTCHANNEL = 319, /* KW_DIAGNOSTICOUTPUTCHANNEL  */
    KW_RANDOMSEED = 320,           /* KW_RANDOMSEED  */
    KW_VERBOSITY = 321,            /* KW_VERBOSITY  */
    KW_ERRORBEHAVIOR = 322,        /* KW_ERRORBEHAVIOR  */
    KW_NAME = 323,                 /* KW_NAME  */
    KW_NAMED = 324,                /* KW_NAMED  */
    KW_AUTHORS = 325,              /* KW_AUTHORS  */
    KW_VERSION = 326,              /* KW_VERSION  */
    KW_STATUS = 327,               /* KW_STATUS  */
    KW_REASONUNKNOWN = 328,        /* KW_REASONUNKNOWN  */
    KW_ALLSTATISTICS = 329         /* KW_ALLSTATISTICS  */
  };
  typedef enum yytokentype yytoken_kind_t;
#endif

/* Value type.  */
#if ! defined YYSTYPE && ! defined YYSTYPE_IS_DECLARED
union YYSTYPE
{
#line 66 "smt2newparser.yy"

  char  *                      str;
  ASTNode *                    snode;
  std::vector< ASTNode * > *   snode_list;
  osmttokens::smt2token        tok;

#line 145 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.hh"

};
typedef union YYSTYPE YYSTYPE;
# define YYSTYPE_IS_TRIVIAL 1
# define YYSTYPE_IS_DECLARED 1
#endif

/* Location type.  */
#if ! defined YYLTYPE && ! defined YYLTYPE_IS_DECLARED
typedef struct YYLTYPE YYLTYPE;
struct YYLTYPE
{
  int first_line;
  int first_column;
  int last_line;
  int last_column;
};
# define YYLTYPE_IS_DECLARED 1
# define YYLTYPE_IS_TRIVIAL 1
#endif




int smt2newparse (Smt2newContext* context);


#endif /* !YY_SMT2NEW_HOME_MAMBO_GOLEM_CMAKE_BUILD_RELEASE_DEPS_OPENSMT_BUILD_SRC_PARSERS_SMT2NEW_SMT2NEWPARSER_HH_INCLUDED  */
