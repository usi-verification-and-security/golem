/* A Bison parser, made by GNU Bison 3.8.2.  */

/* Bison implementation for Yacc-like parsers in C

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

/* C LALR(1) parser skeleton written by Richard Stallman, by
   simplifying the original so-called "semantic" parser.  */

/* DO NOT RELY ON FEATURES THAT ARE NOT DOCUMENTED in the manual,
   especially those whose name start with YY_ or yy_.  They are
   private implementation details that can be changed or removed.  */

/* All symbols defined below should begin with yy or YY, to avoid
   infringing on user name space.  This should be done even for local
   variables, as they might otherwise be expanded by user macros.
   There are some unavoidable exceptions within include files to
   define necessary library symbols; they are noted "INFRINGES ON
   USER NAME SPACE" below.  */

/* Identify Bison output, and Bison version.  */
#define YYBISON 30802

/* Bison version string.  */
#define YYBISON_VERSION "3.8.2"

/* Skeleton name.  */
#define YYSKELETON_NAME "yacc.c"

/* Pure parsers.  */
#define YYPURE 1

/* Push parsers.  */
#define YYPUSH 0

/* Pull parsers.  */
#define YYPULL 1


/* Substitute the variable and function names.  */
#define yyparse         smt2newparse
#define yylex           smt2newlex
#define yyerror         smt2newerror
#define yydebug         smt2newdebug
#define yynerrs         smt2newnerrs

/* First part of user prologue.  */
#line 35 "smt2newparser.yy"

#include <cstdio>
#include <cstdlib>
#include <cassert>
#include <vector>
#include <list>
#include <string>
#include <string.h>

#include "smt2newcontext.h"
#include "smt2newparser.hh"
#include "smt2tokens.h"

int smt2newlex(YYSTYPE* lvalp, YYLTYPE* llocp, void* scanner);

void smt2newerror( YYLTYPE* locp, Smt2newContext* context, const char * s )
{
  if (context->interactive)
    printf("At interactive input: %s\n", s);
  else
    printf( "At line %d: %s\n", locp->first_line, s );
//  exit( 1 );
}

#define scanner context->scanner

/* Overallocation to prevent stack overflow */
#define YYMAXDEPTH 1024 * 1024

#line 106 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"

# ifndef YY_CAST
#  ifdef __cplusplus
#   define YY_CAST(Type, Val) static_cast<Type> (Val)
#   define YY_REINTERPRET_CAST(Type, Val) reinterpret_cast<Type> (Val)
#  else
#   define YY_CAST(Type, Val) ((Type) (Val))
#   define YY_REINTERPRET_CAST(Type, Val) ((Type) (Val))
#  endif
# endif
# ifndef YY_NULLPTR
#  if defined __cplusplus
#   if 201103L <= __cplusplus
#    define YY_NULLPTR nullptr
#   else
#    define YY_NULLPTR 0
#   endif
#  else
#   define YY_NULLPTR ((void*)0)
#  endif
# endif

#include "smt2newparser.hh"
/* Symbol kind.  */
enum yysymbol_kind_t
{
  YYSYMBOL_YYEMPTY = -2,
  YYSYMBOL_YYEOF = 0,                      /* "end of file"  */
  YYSYMBOL_YYerror = 1,                    /* error  */
  YYSYMBOL_YYUNDEF = 2,                    /* "invalid token"  */
  YYSYMBOL_TK_AS = 3,                      /* TK_AS  */
  YYSYMBOL_TK_DECIMAL = 4,                 /* TK_DECIMAL  */
  YYSYMBOL_TK_EXISTS = 5,                  /* TK_EXISTS  */
  YYSYMBOL_TK_FORALL = 6,                  /* TK_FORALL  */
  YYSYMBOL_TK_LET = 7,                     /* TK_LET  */
  YYSYMBOL_TK_NUMERAL = 8,                 /* TK_NUMERAL  */
  YYSYMBOL_TK_PAR = 9,                     /* TK_PAR  */
  YYSYMBOL_TK_STRING = 10,                 /* TK_STRING  */
  YYSYMBOL_TK_ASSERT = 11,                 /* TK_ASSERT  */
  YYSYMBOL_TK_CHECKSAT = 12,               /* TK_CHECKSAT  */
  YYSYMBOL_TK_DECLARESORT = 13,            /* TK_DECLARESORT  */
  YYSYMBOL_TK_DECLAREFUN = 14,             /* TK_DECLAREFUN  */
  YYSYMBOL_TK_DECLARECONST = 15,           /* TK_DECLARECONST  */
  YYSYMBOL_TK_DEFINESORT = 16,             /* TK_DEFINESORT  */
  YYSYMBOL_TK_DEFINEFUN = 17,              /* TK_DEFINEFUN  */
  YYSYMBOL_TK_EXIT = 18,                   /* TK_EXIT  */
  YYSYMBOL_TK_GETASSERTIONS = 19,          /* TK_GETASSERTIONS  */
  YYSYMBOL_TK_GETASSIGNMENT = 20,          /* TK_GETASSIGNMENT  */
  YYSYMBOL_TK_GETINFO = 21,                /* TK_GETINFO  */
  YYSYMBOL_TK_GETOPTION = 22,              /* TK_GETOPTION  */
  YYSYMBOL_TK_GETPROOF = 23,               /* TK_GETPROOF  */
  YYSYMBOL_TK_GETUNSATCORE = 24,           /* TK_GETUNSATCORE  */
  YYSYMBOL_TK_GETVALUE = 25,               /* TK_GETVALUE  */
  YYSYMBOL_TK_GETMODEL = 26,               /* TK_GETMODEL  */
  YYSYMBOL_TK_POP = 27,                    /* TK_POP  */
  YYSYMBOL_TK_PUSH = 28,                   /* TK_PUSH  */
  YYSYMBOL_TK_SETLOGIC = 29,               /* TK_SETLOGIC  */
  YYSYMBOL_TK_SETINFO = 30,                /* TK_SETINFO  */
  YYSYMBOL_TK_SETOPTION = 31,              /* TK_SETOPTION  */
  YYSYMBOL_TK_THEORY = 32,                 /* TK_THEORY  */
  YYSYMBOL_TK_GETITPS = 33,                /* TK_GETITPS  */
  YYSYMBOL_TK_WRSTATE = 34,                /* TK_WRSTATE  */
  YYSYMBOL_TK_RDSTATE = 35,                /* TK_RDSTATE  */
  YYSYMBOL_TK_SIMPLIFY = 36,               /* TK_SIMPLIFY  */
  YYSYMBOL_TK_WRFUNS = 37,                 /* TK_WRFUNS  */
  YYSYMBOL_TK_ECHO = 38,                   /* TK_ECHO  */
  YYSYMBOL_TK_NUM = 39,                    /* TK_NUM  */
  YYSYMBOL_TK_SYM = 40,                    /* TK_SYM  */
  YYSYMBOL_TK_QSYM = 41,                   /* TK_QSYM  */
  YYSYMBOL_TK_KEY = 42,                    /* TK_KEY  */
  YYSYMBOL_TK_STR = 43,                    /* TK_STR  */
  YYSYMBOL_TK_DEC = 44,                    /* TK_DEC  */
  YYSYMBOL_TK_HEX = 45,                    /* TK_HEX  */
  YYSYMBOL_TK_BIN = 46,                    /* TK_BIN  */
  YYSYMBOL_KW_SORTS = 47,                  /* KW_SORTS  */
  YYSYMBOL_KW_FUNS = 48,                   /* KW_FUNS  */
  YYSYMBOL_KW_SORTSDESCRIPTION = 49,       /* KW_SORTSDESCRIPTION  */
  YYSYMBOL_KW_FUNSDESCRIPTION = 50,        /* KW_FUNSDESCRIPTION  */
  YYSYMBOL_KW_DEFINITION = 51,             /* KW_DEFINITION  */
  YYSYMBOL_KW_NOTES = 52,                  /* KW_NOTES  */
  YYSYMBOL_KW_THEORIES = 53,               /* KW_THEORIES  */
  YYSYMBOL_KW_EXTENSIONS = 54,             /* KW_EXTENSIONS  */
  YYSYMBOL_KW_VALUES = 55,                 /* KW_VALUES  */
  YYSYMBOL_KW_PRINTSUCCESS = 56,           /* KW_PRINTSUCCESS  */
  YYSYMBOL_KW_EXPANDDEFINITIONS = 57,      /* KW_EXPANDDEFINITIONS  */
  YYSYMBOL_KW_INTERACTIVEMODE = 58,        /* KW_INTERACTIVEMODE  */
  YYSYMBOL_KW_PRODUCEPROOFS = 59,          /* KW_PRODUCEPROOFS  */
  YYSYMBOL_KW_PRODUCEUNSATCORES = 60,      /* KW_PRODUCEUNSATCORES  */
  YYSYMBOL_KW_PRODUCEMODELS = 61,          /* KW_PRODUCEMODELS  */
  YYSYMBOL_KW_PRODUCEASSIGNMENTS = 62,     /* KW_PRODUCEASSIGNMENTS  */
  YYSYMBOL_KW_REGULAROUTPUTCHANNEL = 63,   /* KW_REGULAROUTPUTCHANNEL  */
  YYSYMBOL_KW_DIAGNOSTICOUTPUTCHANNEL = 64, /* KW_DIAGNOSTICOUTPUTCHANNEL  */
  YYSYMBOL_KW_RANDOMSEED = 65,             /* KW_RANDOMSEED  */
  YYSYMBOL_KW_VERBOSITY = 66,              /* KW_VERBOSITY  */
  YYSYMBOL_KW_ERRORBEHAVIOR = 67,          /* KW_ERRORBEHAVIOR  */
  YYSYMBOL_KW_NAME = 68,                   /* KW_NAME  */
  YYSYMBOL_KW_NAMED = 69,                  /* KW_NAMED  */
  YYSYMBOL_KW_AUTHORS = 70,                /* KW_AUTHORS  */
  YYSYMBOL_KW_VERSION = 71,                /* KW_VERSION  */
  YYSYMBOL_KW_STATUS = 72,                 /* KW_STATUS  */
  YYSYMBOL_KW_REASONUNKNOWN = 73,          /* KW_REASONUNKNOWN  */
  YYSYMBOL_KW_ALLSTATISTICS = 74,          /* KW_ALLSTATISTICS  */
  YYSYMBOL_75_ = 75,                       /* '('  */
  YYSYMBOL_76_ = 76,                       /* ')'  */
  YYSYMBOL_77___ = 77,                     /* '_'  */
  YYSYMBOL_78_ = 78,                       /* '!'  */
  YYSYMBOL_YYACCEPT = 79,                  /* $accept  */
  YYSYMBOL_script = 80,                    /* script  */
  YYSYMBOL_symbol = 81,                    /* symbol  */
  YYSYMBOL_command_list = 82,              /* command_list  */
  YYSYMBOL_command = 83,                   /* command  */
  YYSYMBOL_attribute_list = 84,            /* attribute_list  */
  YYSYMBOL_attribute = 85,                 /* attribute  */
  YYSYMBOL_attribute_value = 86,           /* attribute_value  */
  YYSYMBOL_identifier = 87,                /* identifier  */
  YYSYMBOL_sort = 88,                      /* sort  */
  YYSYMBOL_sort_list = 89,                 /* sort_list  */
  YYSYMBOL_s_expr = 90,                    /* s_expr  */
  YYSYMBOL_s_expr_list = 91,               /* s_expr_list  */
  YYSYMBOL_spec_const = 92,                /* spec_const  */
  YYSYMBOL_const_val = 93,                 /* const_val  */
  YYSYMBOL_numeral_list = 94,              /* numeral_list  */
  YYSYMBOL_qual_identifier = 95,           /* qual_identifier  */
  YYSYMBOL_var_binding_list = 96,          /* var_binding_list  */
  YYSYMBOL_var_binding = 97,               /* var_binding  */
  YYSYMBOL_sorted_var_list = 98,           /* sorted_var_list  */
  YYSYMBOL_sorted_var = 99,                /* sorted_var  */
  YYSYMBOL_term_list = 100,                /* term_list  */
  YYSYMBOL_term = 101,                     /* term  */
  YYSYMBOL_symbol_list = 102,              /* symbol_list  */
  YYSYMBOL_b_value = 103,                  /* b_value  */
  YYSYMBOL_option = 104,                   /* option  */
  YYSYMBOL_predef_key = 105,               /* predef_key  */
  YYSYMBOL_info_flag = 106                 /* info_flag  */
};
typedef enum yysymbol_kind_t yysymbol_kind_t;




#ifdef short
# undef short
#endif

/* On compilers that do not define __PTRDIFF_MAX__ etc., make sure
   <limits.h> and (if available) <stdint.h> are included
   so that the code can choose integer types of a good width.  */

#ifndef __PTRDIFF_MAX__
# include <limits.h> /* INFRINGES ON USER NAME SPACE */
# if defined __STDC_VERSION__ && 199901 <= __STDC_VERSION__
#  include <stdint.h> /* INFRINGES ON USER NAME SPACE */
#  define YY_STDINT_H
# endif
#endif

/* Narrow types that promote to a signed type and that can represent a
   signed or unsigned integer of at least N bits.  In tables they can
   save space and decrease cache pressure.  Promoting to a signed type
   helps avoid bugs in integer arithmetic.  */

#ifdef __INT_LEAST8_MAX__
typedef __INT_LEAST8_TYPE__ yytype_int8;
#elif defined YY_STDINT_H
typedef int_least8_t yytype_int8;
#else
typedef signed char yytype_int8;
#endif

#ifdef __INT_LEAST16_MAX__
typedef __INT_LEAST16_TYPE__ yytype_int16;
#elif defined YY_STDINT_H
typedef int_least16_t yytype_int16;
#else
typedef short yytype_int16;
#endif

/* Work around bug in HP-UX 11.23, which defines these macros
   incorrectly for preprocessor constants.  This workaround can likely
   be removed in 2023, as HPE has promised support for HP-UX 11.23
   (aka HP-UX 11i v2) only through the end of 2022; see Table 2 of
   <https://h20195.www2.hpe.com/V2/getpdf.aspx/4AA4-7673ENW.pdf>.  */
#ifdef __hpux
# undef UINT_LEAST8_MAX
# undef UINT_LEAST16_MAX
# define UINT_LEAST8_MAX 255
# define UINT_LEAST16_MAX 65535
#endif

#if defined __UINT_LEAST8_MAX__ && __UINT_LEAST8_MAX__ <= __INT_MAX__
typedef __UINT_LEAST8_TYPE__ yytype_uint8;
#elif (!defined __UINT_LEAST8_MAX__ && defined YY_STDINT_H \
       && UINT_LEAST8_MAX <= INT_MAX)
typedef uint_least8_t yytype_uint8;
#elif !defined __UINT_LEAST8_MAX__ && UCHAR_MAX <= INT_MAX
typedef unsigned char yytype_uint8;
#else
typedef short yytype_uint8;
#endif

#if defined __UINT_LEAST16_MAX__ && __UINT_LEAST16_MAX__ <= __INT_MAX__
typedef __UINT_LEAST16_TYPE__ yytype_uint16;
#elif (!defined __UINT_LEAST16_MAX__ && defined YY_STDINT_H \
       && UINT_LEAST16_MAX <= INT_MAX)
typedef uint_least16_t yytype_uint16;
#elif !defined __UINT_LEAST16_MAX__ && USHRT_MAX <= INT_MAX
typedef unsigned short yytype_uint16;
#else
typedef int yytype_uint16;
#endif

#ifndef YYPTRDIFF_T
# if defined __PTRDIFF_TYPE__ && defined __PTRDIFF_MAX__
#  define YYPTRDIFF_T __PTRDIFF_TYPE__
#  define YYPTRDIFF_MAXIMUM __PTRDIFF_MAX__
# elif defined PTRDIFF_MAX
#  ifndef ptrdiff_t
#   include <stddef.h> /* INFRINGES ON USER NAME SPACE */
#  endif
#  define YYPTRDIFF_T ptrdiff_t
#  define YYPTRDIFF_MAXIMUM PTRDIFF_MAX
# else
#  define YYPTRDIFF_T long
#  define YYPTRDIFF_MAXIMUM LONG_MAX
# endif
#endif

#ifndef YYSIZE_T
# ifdef __SIZE_TYPE__
#  define YYSIZE_T __SIZE_TYPE__
# elif defined size_t
#  define YYSIZE_T size_t
# elif defined __STDC_VERSION__ && 199901 <= __STDC_VERSION__
#  include <stddef.h> /* INFRINGES ON USER NAME SPACE */
#  define YYSIZE_T size_t
# else
#  define YYSIZE_T unsigned
# endif
#endif

#define YYSIZE_MAXIMUM                                  \
  YY_CAST (YYPTRDIFF_T,                                 \
           (YYPTRDIFF_MAXIMUM < YY_CAST (YYSIZE_T, -1)  \
            ? YYPTRDIFF_MAXIMUM                         \
            : YY_CAST (YYSIZE_T, -1)))

#define YYSIZEOF(X) YY_CAST (YYPTRDIFF_T, sizeof (X))


/* Stored state numbers (used for stacks). */
typedef yytype_uint8 yy_state_t;

/* State numbers in computations.  */
typedef int yy_state_fast_t;

#ifndef YY_
# if defined YYENABLE_NLS && YYENABLE_NLS
#  if ENABLE_NLS
#   include <libintl.h> /* INFRINGES ON USER NAME SPACE */
#   define YY_(Msgid) dgettext ("bison-runtime", Msgid)
#  endif
# endif
# ifndef YY_
#  define YY_(Msgid) Msgid
# endif
#endif


#ifndef YY_ATTRIBUTE_PURE
# if defined __GNUC__ && 2 < __GNUC__ + (96 <= __GNUC_MINOR__)
#  define YY_ATTRIBUTE_PURE __attribute__ ((__pure__))
# else
#  define YY_ATTRIBUTE_PURE
# endif
#endif

#ifndef YY_ATTRIBUTE_UNUSED
# if defined __GNUC__ && 2 < __GNUC__ + (7 <= __GNUC_MINOR__)
#  define YY_ATTRIBUTE_UNUSED __attribute__ ((__unused__))
# else
#  define YY_ATTRIBUTE_UNUSED
# endif
#endif

/* Suppress unused-variable warnings by "using" E.  */
#if ! defined lint || defined __GNUC__
# define YY_USE(E) ((void) (E))
#else
# define YY_USE(E) /* empty */
#endif

/* Suppress an incorrect diagnostic about yylval being uninitialized.  */
#if defined __GNUC__ && ! defined __ICC && 406 <= __GNUC__ * 100 + __GNUC_MINOR__
# if __GNUC__ * 100 + __GNUC_MINOR__ < 407
#  define YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN                           \
    _Pragma ("GCC diagnostic push")                                     \
    _Pragma ("GCC diagnostic ignored \"-Wuninitialized\"")
# else
#  define YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN                           \
    _Pragma ("GCC diagnostic push")                                     \
    _Pragma ("GCC diagnostic ignored \"-Wuninitialized\"")              \
    _Pragma ("GCC diagnostic ignored \"-Wmaybe-uninitialized\"")
# endif
# define YY_IGNORE_MAYBE_UNINITIALIZED_END      \
    _Pragma ("GCC diagnostic pop")
#else
# define YY_INITIAL_VALUE(Value) Value
#endif
#ifndef YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
# define YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
# define YY_IGNORE_MAYBE_UNINITIALIZED_END
#endif
#ifndef YY_INITIAL_VALUE
# define YY_INITIAL_VALUE(Value) /* Nothing. */
#endif

#if defined __cplusplus && defined __GNUC__ && ! defined __ICC && 6 <= __GNUC__
# define YY_IGNORE_USELESS_CAST_BEGIN                          \
    _Pragma ("GCC diagnostic push")                            \
    _Pragma ("GCC diagnostic ignored \"-Wuseless-cast\"")
# define YY_IGNORE_USELESS_CAST_END            \
    _Pragma ("GCC diagnostic pop")
#endif
#ifndef YY_IGNORE_USELESS_CAST_BEGIN
# define YY_IGNORE_USELESS_CAST_BEGIN
# define YY_IGNORE_USELESS_CAST_END
#endif


#define YY_ASSERT(E) ((void) (0 && (E)))

#if 1

/* The parser invokes alloca or malloc; define the necessary symbols.  */

# ifdef YYSTACK_USE_ALLOCA
#  if YYSTACK_USE_ALLOCA
#   ifdef __GNUC__
#    define YYSTACK_ALLOC __builtin_alloca
#   elif defined __BUILTIN_VA_ARG_INCR
#    include <alloca.h> /* INFRINGES ON USER NAME SPACE */
#   elif defined _AIX
#    define YYSTACK_ALLOC __alloca
#   elif defined _MSC_VER
#    include <malloc.h> /* INFRINGES ON USER NAME SPACE */
#    define alloca _alloca
#   else
#    define YYSTACK_ALLOC alloca
#    if ! defined _ALLOCA_H && ! defined EXIT_SUCCESS
#     include <stdlib.h> /* INFRINGES ON USER NAME SPACE */
      /* Use EXIT_SUCCESS as a witness for stdlib.h.  */
#     ifndef EXIT_SUCCESS
#      define EXIT_SUCCESS 0
#     endif
#    endif
#   endif
#  endif
# endif

# ifdef YYSTACK_ALLOC
   /* Pacify GCC's 'empty if-body' warning.  */
#  define YYSTACK_FREE(Ptr) do { /* empty */; } while (0)
#  ifndef YYSTACK_ALLOC_MAXIMUM
    /* The OS might guarantee only one guard page at the bottom of the stack,
       and a page size can be as small as 4096 bytes.  So we cannot safely
       invoke alloca (N) if N exceeds 4096.  Use a slightly smaller number
       to allow for a few compiler-allocated temporary stack slots.  */
#   define YYSTACK_ALLOC_MAXIMUM 4032 /* reasonable circa 2006 */
#  endif
# else
#  define YYSTACK_ALLOC YYMALLOC
#  define YYSTACK_FREE YYFREE
#  ifndef YYSTACK_ALLOC_MAXIMUM
#   define YYSTACK_ALLOC_MAXIMUM YYSIZE_MAXIMUM
#  endif
#  if (defined __cplusplus && ! defined EXIT_SUCCESS \
       && ! ((defined YYMALLOC || defined malloc) \
             && (defined YYFREE || defined free)))
#   include <stdlib.h> /* INFRINGES ON USER NAME SPACE */
#   ifndef EXIT_SUCCESS
#    define EXIT_SUCCESS 0
#   endif
#  endif
#  ifndef YYMALLOC
#   define YYMALLOC malloc
#   if ! defined malloc && ! defined EXIT_SUCCESS
void *malloc (YYSIZE_T); /* INFRINGES ON USER NAME SPACE */
#   endif
#  endif
#  ifndef YYFREE
#   define YYFREE free
#   if ! defined free && ! defined EXIT_SUCCESS
void free (void *); /* INFRINGES ON USER NAME SPACE */
#   endif
#  endif
# endif
#endif /* 1 */

#if (! defined yyoverflow \
     && (! defined __cplusplus \
         || (defined YYLTYPE_IS_TRIVIAL && YYLTYPE_IS_TRIVIAL \
             && defined YYSTYPE_IS_TRIVIAL && YYSTYPE_IS_TRIVIAL)))

/* A type that is properly aligned for any stack member.  */
union yyalloc
{
  yy_state_t yyss_alloc;
  YYSTYPE yyvs_alloc;
  YYLTYPE yyls_alloc;
};

/* The size of the maximum gap between one aligned stack and the next.  */
# define YYSTACK_GAP_MAXIMUM (YYSIZEOF (union yyalloc) - 1)

/* The size of an array large to enough to hold all stacks, each with
   N elements.  */
# define YYSTACK_BYTES(N) \
     ((N) * (YYSIZEOF (yy_state_t) + YYSIZEOF (YYSTYPE) \
             + YYSIZEOF (YYLTYPE)) \
      + 2 * YYSTACK_GAP_MAXIMUM)

# define YYCOPY_NEEDED 1

/* Relocate STACK from its old location to the new one.  The
   local variables YYSIZE and YYSTACKSIZE give the old and new number of
   elements in the stack, and YYPTR gives the new location of the
   stack.  Advance YYPTR to a properly aligned location for the next
   stack.  */
# define YYSTACK_RELOCATE(Stack_alloc, Stack)                           \
    do                                                                  \
      {                                                                 \
        YYPTRDIFF_T yynewbytes;                                         \
        YYCOPY (&yyptr->Stack_alloc, Stack, yysize);                    \
        Stack = &yyptr->Stack_alloc;                                    \
        yynewbytes = yystacksize * YYSIZEOF (*Stack) + YYSTACK_GAP_MAXIMUM; \
        yyptr += yynewbytes / YYSIZEOF (*yyptr);                        \
      }                                                                 \
    while (0)

#endif

#if defined YYCOPY_NEEDED && YYCOPY_NEEDED
/* Copy COUNT objects from SRC to DST.  The source and destination do
   not overlap.  */
# ifndef YYCOPY
#  if defined __GNUC__ && 1 < __GNUC__
#   define YYCOPY(Dst, Src, Count) \
      __builtin_memcpy (Dst, Src, YY_CAST (YYSIZE_T, (Count)) * sizeof (*(Src)))
#  else
#   define YYCOPY(Dst, Src, Count)              \
      do                                        \
        {                                       \
          YYPTRDIFF_T yyi;                      \
          for (yyi = 0; yyi < (Count); yyi++)   \
            (Dst)[yyi] = (Src)[yyi];            \
        }                                       \
      while (0)
#  endif
# endif
#endif /* !YYCOPY_NEEDED */

/* YYFINAL -- State number of the termination state.  */
#define YYFINAL  3
/* YYLAST -- Last index in YYTABLE.  */
#define YYLAST   396

/* YYNTOKENS -- Number of terminals.  */
#define YYNTOKENS  79
/* YYNNTS -- Number of nonterminals.  */
#define YYNNTS  28
/* YYNRULES -- Number of rules.  */
#define YYNRULES  132
/* YYNSTATES -- Number of states.  */
#define YYNSTATES  251

/* YYMAXUTOK -- Last valid token kind.  */
#define YYMAXUTOK   329


/* YYTRANSLATE(TOKEN-NUM) -- Symbol number corresponding to TOKEN-NUM
   as returned by yylex, with out-of-bounds checking.  */
#define YYTRANSLATE(YYX)                                \
  (0 <= (YYX) && (YYX) <= YYMAXUTOK                     \
   ? YY_CAST (yysymbol_kind_t, yytranslate[YYX])        \
   : YYSYMBOL_YYUNDEF)

/* YYTRANSLATE[TOKEN-NUM] -- Symbol number corresponding to TOKEN-NUM
   as returned by yylex.  */
static const yytype_int8 yytranslate[] =
{
       0,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,    78,     2,     2,     2,     2,     2,     2,
      75,    76,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,    77,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     1,     2,     3,     4,
       5,     6,     7,     8,     9,    10,    11,    12,    13,    14,
      15,    16,    17,    18,    19,    20,    21,    22,    23,    24,
      25,    26,    27,    28,    29,    30,    31,    32,    33,    34,
      35,    36,    37,    38,    39,    40,    41,    42,    43,    44,
      45,    46,    47,    48,    49,    50,    51,    52,    53,    54,
      55,    56,    57,    58,    59,    60,    61,    62,    63,    64,
      65,    66,    67,    68,    69,    70,    71,    72,    73,    74
};

#if YYDEBUG
/* YYRLINE[YYN] -- Source line where rule number YYN was defined.  */
static const yytype_int16 yyrline[] =
{
       0,    96,    96,    98,   100,   105,   106,   110,   116,   122,
     128,   135,   148,   160,   172,   185,   191,   197,   203,   207,
     211,   215,   220,   226,   232,   238,   242,   248,   252,   256,
     262,   268,   274,   278,   280,   289,   290,   294,   296,   298,
     300,   304,   306,   310,   317,   319,   323,   325,   334,   337,
     340,   346,   350,   354,   362,   365,   373,   375,   377,   379,
     381,   385,   387,   391,   393,   397,   399,   409,   410,   414,
     419,   420,   424,   428,   429,   433,   435,   437,   444,   454,
     464,   474,   487,   488,   492,   506,   512,   518,   524,   530,
     536,   542,   548,   554,   560,   566,   572,   580,   582,   584,
     586,   588,   590,   592,   594,   596,   598,   600,   602,   604,
     606,   608,   610,   612,   614,   616,   618,   620,   622,   624,
     626,   628,   630,   632,   634,   638,   640,   642,   644,   646,
     648,   650,   652
};
#endif

/** Accessing symbol of state STATE.  */
#define YY_ACCESSING_SYMBOL(State) YY_CAST (yysymbol_kind_t, yystos[State])

#if 1
/* The user-facing name of the symbol whose (internal) number is
   YYSYMBOL.  No bounds checking.  */
static const char *yysymbol_name (yysymbol_kind_t yysymbol) YY_ATTRIBUTE_UNUSED;

/* YYTNAME[SYMBOL-NUM] -- String name of the symbol SYMBOL-NUM.
   First, the terminals, then, starting at YYNTOKENS, nonterminals.  */
static const char *const yytname[] =
{
  "\"end of file\"", "error", "\"invalid token\"", "TK_AS", "TK_DECIMAL",
  "TK_EXISTS", "TK_FORALL", "TK_LET", "TK_NUMERAL", "TK_PAR", "TK_STRING",
  "TK_ASSERT", "TK_CHECKSAT", "TK_DECLARESORT", "TK_DECLAREFUN",
  "TK_DECLARECONST", "TK_DEFINESORT", "TK_DEFINEFUN", "TK_EXIT",
  "TK_GETASSERTIONS", "TK_GETASSIGNMENT", "TK_GETINFO", "TK_GETOPTION",
  "TK_GETPROOF", "TK_GETUNSATCORE", "TK_GETVALUE", "TK_GETMODEL", "TK_POP",
  "TK_PUSH", "TK_SETLOGIC", "TK_SETINFO", "TK_SETOPTION", "TK_THEORY",
  "TK_GETITPS", "TK_WRSTATE", "TK_RDSTATE", "TK_SIMPLIFY", "TK_WRFUNS",
  "TK_ECHO", "TK_NUM", "TK_SYM", "TK_QSYM", "TK_KEY", "TK_STR", "TK_DEC",
  "TK_HEX", "TK_BIN", "KW_SORTS", "KW_FUNS", "KW_SORTSDESCRIPTION",
  "KW_FUNSDESCRIPTION", "KW_DEFINITION", "KW_NOTES", "KW_THEORIES",
  "KW_EXTENSIONS", "KW_VALUES", "KW_PRINTSUCCESS", "KW_EXPANDDEFINITIONS",
  "KW_INTERACTIVEMODE", "KW_PRODUCEPROOFS", "KW_PRODUCEUNSATCORES",
  "KW_PRODUCEMODELS", "KW_PRODUCEASSIGNMENTS", "KW_REGULAROUTPUTCHANNEL",
  "KW_DIAGNOSTICOUTPUTCHANNEL", "KW_RANDOMSEED", "KW_VERBOSITY",
  "KW_ERRORBEHAVIOR", "KW_NAME", "KW_NAMED", "KW_AUTHORS", "KW_VERSION",
  "KW_STATUS", "KW_REASONUNKNOWN", "KW_ALLSTATISTICS", "'('", "')'", "'_'",
  "'!'", "$accept", "script", "symbol", "command_list", "command",
  "attribute_list", "attribute", "attribute_value", "identifier", "sort",
  "sort_list", "s_expr", "s_expr_list", "spec_const", "const_val",
  "numeral_list", "qual_identifier", "var_binding_list", "var_binding",
  "sorted_var_list", "sorted_var", "term_list", "term", "symbol_list",
  "b_value", "option", "predef_key", "info_flag", YY_NULLPTR
};

static const char *
yysymbol_name (yysymbol_kind_t yysymbol)
{
  return yytname[yysymbol];
}
#endif

#define YYPACT_NINF (-93)

#define yypact_value_is_default(Yyn) \
  ((Yyn) == YYPACT_NINF)

#define YYTABLE_NINF (-1)

#define yytable_value_is_error(Yyn) \
  0

/* YYPACT[STATE-NUM] -- Index in YYTABLE of the portion describing
   STATE-NUM.  */
static const yytype_int16 yypact[] =
{
     -93,    11,   -38,   -93,   349,   -93,   110,   -32,     2,     2,
     149,     2,     2,   -28,   -25,   -23,   145,   219,    -4,     0,
      10,    21,    68,    75,     2,   252,   285,   -93,    88,    91,
      61,    95,    96,   -93,   -93,   -93,   -93,   -93,   -93,   -93,
       9,   -93,   -93,   -93,   -93,    67,   -93,   107,    77,   -93,
     -93,    20,    92,   101,   -93,   -93,   -93,   -93,   -93,   -93,
     -93,   -93,   -93,   -93,   -93,   108,   120,   -93,   -93,   -93,
     -93,   -93,   -93,   -93,   -93,   -93,   -93,   -93,   -93,   -93,
     -93,   -93,   -93,   -93,   -93,   -93,   -93,   -93,   -93,   -93,
     -93,   -93,   -93,   -93,   -93,   121,   -93,   -93,   110,   -93,
     122,   123,   126,   125,   127,   125,     2,     2,     2,     2,
       2,     2,     2,   161,   162,   138,   167,   -93,   131,    -5,
     132,   146,   -93,   147,   150,    49,   139,   154,   155,     4,
       2,   110,   110,   -93,   156,   -93,    16,   -93,   187,   -93,
     -93,   -93,   -93,   -93,   -93,   -93,   -93,   -93,   -93,   -93,
     -93,   -93,   -93,   -93,   -93,   -93,   -93,   -93,   -93,   -93,
     -93,   -93,   -93,   -93,   -93,   -93,   -93,   -93,   -93,   -93,
     -93,   -93,   -93,   188,    20,   189,   189,   220,   257,   252,
     -93,   -93,   104,    20,   -93,     6,   -17,    34,   -21,   221,
       2,   -93,   -93,     2,   -93,   -93,   -31,   -93,    72,    20,
     -93,   -93,    20,   -93,    20,   -93,   222,   -93,   -93,   -93,
     -93,   -93,   -93,   -93,    20,    44,    46,   110,    52,   -93,
     -93,   186,   -93,   253,   134,   254,   110,   -93,   -13,   255,
     110,   110,   305,   110,   -93,   -93,   -93,   -93,   -93,   -93,
     312,   -93,   -93,   313,   314,   -93,   315,   -93,   -93,   -93,
     -93
};

/* YYDEFACT[STATE-NUM] -- Default reduction number in state STATE-NUM.
   Performed when YYTABLE does not specify something else to do.  Zero
   means the default is an error.  */
static const yytype_uint8 yydefact[] =
{
       5,     0,     2,     1,     0,     6,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,    73,     0,     0,
       0,     0,     0,    56,     3,     4,    60,    57,    58,    59,
       0,    44,    65,    75,    76,     0,    18,     0,     0,    61,
      62,     0,     0,     0,    33,    19,    28,   132,   125,   126,
     127,   128,   129,   130,   131,     0,     0,    97,    98,    99,
     100,   101,   103,   104,   105,   102,   106,   107,   108,   109,
     110,   111,   112,   113,   114,   115,   116,   117,   118,   119,
     120,   121,   122,   123,   124,     0,    20,    25,     0,    27,
       0,     0,     0,    37,     0,    39,   106,   107,   108,   109,
     110,   111,   112,   113,   114,   115,   116,    96,     0,     0,
       0,     0,    32,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,    17,     0,    49,     0,    46,     0,    82,
      70,    31,    29,    30,    73,    16,    15,     7,    54,    42,
      38,    41,     9,    40,    84,    85,    86,    87,    88,    89,
      90,    91,    92,    93,    94,    95,     8,    21,    74,    22,
      23,    24,    34,     0,     0,     0,     0,     0,     0,     0,
      73,    10,     0,     0,    13,     0,     0,     0,     0,     0,
       0,    70,    70,     0,    67,    64,     0,    35,     0,     0,
      48,    49,     0,    83,     0,    71,     0,    52,    54,    43,
      51,    55,    50,    66,     0,     0,     0,     0,     0,    63,
      45,     0,    77,     0,     0,     0,     0,    26,     0,     0,
       0,     0,     0,     0,    68,    81,    36,    12,    47,    11,
       0,    53,    72,     0,     0,    69,     0,    14,    80,    79,
      78
};

/* YYPGOTO[NTERM-NUM].  */
static const yytype_int16 yypgoto[] =
{
     -93,   -93,    -7,   -93,   -93,   -93,   -20,   223,   -42,   -41,
     191,   -93,   185,     3,   -93,   -93,   354,   -93,   177,   -62,
     -40,   -92,    -6,   -93,   -43,   -93,   379,   -93
};

/* YYDEFGOTO[NTERM-NUM].  */
static const yytype_uint8 yydefgoto[] =
{
       0,     1,    41,     2,     5,   221,   104,   150,    42,   200,
     182,   211,   188,    43,    51,   196,    44,   218,   194,   186,
     205,   119,   168,   185,   155,   118,   105,    65
};

/* YYTABLE[YYPACT[STATE-NUM]] -- What to do in state STATE-NUM.  If
   positive, shift that token.  If negative, reduce the rule whose
   number is the opposite.  If YYTABLE_NINF, syntax error.  */
static const yytype_uint8 yytable[] =
{
      45,    47,    48,    49,    52,    53,   117,   125,   219,   137,
     138,     3,   125,    50,   126,   127,   128,   102,    33,    34,
      35,   207,    36,    37,    38,    39,    33,    34,    35,   207,
      36,    37,    38,    39,    33,    34,    35,     4,    36,    37,
      38,    39,    34,    35,    46,   220,    34,    35,    54,    34,
      35,    55,   187,    56,   208,   209,    34,    35,   190,   204,
      34,    35,   208,   241,   156,   157,   158,   159,   160,   161,
      40,   167,    96,    33,    34,    35,    97,    36,    37,    38,
      39,   130,   202,   174,   129,    98,   130,   131,   198,    34,
      35,   173,   144,   130,   183,   136,   149,    99,   149,   154,
     154,   154,   154,   154,   154,   154,   151,   100,   151,    40,
     206,    33,    34,    35,   101,    36,    37,    38,    39,   190,
     230,   190,   231,   178,   173,   179,   180,   193,   233,   215,
     216,   120,   137,   189,   121,   191,   192,   122,   123,   124,
     137,   137,   201,   133,    34,    35,   134,    40,   222,    33,
      34,    35,   135,    36,    37,    38,    39,   137,   223,   197,
     137,   225,   137,   226,    33,    34,    35,   139,    36,    37,
      38,    39,   137,   229,    34,    35,   140,   164,   203,   136,
     199,   210,   137,   214,   141,    40,   217,    57,    33,    34,
      35,   212,    36,    37,    38,    39,   142,   143,   145,   146,
     148,   236,   147,   152,   162,   163,   165,   166,   169,   136,
     238,   232,    58,    59,   175,    60,    61,    62,    63,    64,
     240,   210,   170,   171,   243,   244,   172,   246,   103,   176,
     177,   212,   181,    67,    68,    69,    70,    71,    72,    73,
      74,    75,    76,    77,    78,    79,    80,    81,    82,    83,
      84,    85,    86,    87,    88,    89,    90,    91,    92,    93,
      94,    66,   235,   184,   190,   130,    67,    68,    69,    70,
      71,    72,    73,    74,    75,    76,    77,    78,    79,    80,
      81,    82,    83,    84,    85,    86,    87,    88,    89,    90,
      91,    92,    93,    94,   103,   193,   195,   213,   227,    67,
      68,    69,    70,    71,    72,    73,    74,    75,    76,    77,
      78,    79,    80,    81,    82,    83,    84,    85,    86,    87,
      88,    89,    90,    91,    92,    93,    94,   103,   153,   237,
     239,   242,    67,    68,    69,    70,    71,    72,    73,    74,
      75,   106,   107,   108,   109,   110,   111,   112,   113,   114,
     115,   116,    87,    88,    89,    90,    91,    92,    93,    94,
       6,     7,     8,     9,    10,    11,    12,    13,    14,    15,
      16,    17,    18,    19,    20,    21,    22,    23,    24,    25,
      26,   245,    27,    28,    29,    30,    31,    32,   247,   248,
     249,   250,   224,   228,   132,   234,    95
};

static const yytype_uint8 yycheck[] =
{
       6,     8,     9,    10,    11,    12,    26,     3,    39,    51,
      51,     0,     3,    10,     5,     6,     7,    24,    39,    40,
      41,    42,    43,    44,    45,    46,    39,    40,    41,    42,
      43,    44,    45,    46,    39,    40,    41,    75,    43,    44,
      45,    46,    40,    41,    76,    76,    40,    41,    76,    40,
      41,    76,   144,    76,    75,    76,    40,    41,    75,    76,
      40,    41,    75,    76,   107,   108,   109,   110,   111,   112,
      75,    76,    76,    39,    40,    41,    76,    43,    44,    45,
      46,    77,    76,   125,    75,    75,    77,    78,   180,    40,
      41,    75,    98,    77,   136,    75,   103,    76,   105,   106,
     107,   108,   109,   110,   111,   112,   103,    39,   105,    75,
      76,    39,    40,    41,    39,    43,    44,    45,    46,    75,
      76,    75,    76,   130,    75,   131,   132,    75,    76,   191,
     192,    43,   174,   174,    43,   175,   176,    76,    43,    43,
     182,   183,   183,    76,    40,    41,    39,    75,    76,    39,
      40,    41,    75,    43,    44,    45,    46,   199,   199,   179,
     202,   202,   204,   204,    39,    40,    41,    75,    43,    44,
      45,    46,   214,   214,    40,    41,    75,    39,   185,    75,
      76,   188,   224,   190,    76,    75,   193,    42,    39,    40,
      41,   188,    43,    44,    45,    46,    76,    76,    76,    76,
      75,   221,    76,    76,    43,    43,    39,    76,    76,    75,
      76,   217,    67,    68,    75,    70,    71,    72,    73,    74,
     226,   228,    76,    76,   230,   231,    76,   233,    42,    75,
      75,   228,    76,    47,    48,    49,    50,    51,    52,    53,
      54,    55,    56,    57,    58,    59,    60,    61,    62,    63,
      64,    65,    66,    67,    68,    69,    70,    71,    72,    73,
      74,    42,    76,    76,    75,    77,    47,    48,    49,    50,
      51,    52,    53,    54,    55,    56,    57,    58,    59,    60,
      61,    62,    63,    64,    65,    66,    67,    68,    69,    70,
      71,    72,    73,    74,    42,    75,    39,    76,    76,    47,
      48,    49,    50,    51,    52,    53,    54,    55,    56,    57,
      58,    59,    60,    61,    62,    63,    64,    65,    66,    67,
      68,    69,    70,    71,    72,    73,    74,    42,   105,    76,
      76,    76,    47,    48,    49,    50,    51,    52,    53,    54,
      55,    56,    57,    58,    59,    60,    61,    62,    63,    64,
      65,    66,    67,    68,    69,    70,    71,    72,    73,    74,
      11,    12,    13,    14,    15,    16,    17,    18,    19,    20,
      21,    22,    23,    24,    25,    26,    27,    28,    29,    30,
      31,    76,    33,    34,    35,    36,    37,    38,    76,    76,
      76,    76,   201,   208,    40,   218,    17
};

/* YYSTOS[STATE-NUM] -- The symbol kind of the accessing symbol of
   state STATE-NUM.  */
static const yytype_int8 yystos[] =
{
       0,    80,    82,     0,    75,    83,    11,    12,    13,    14,
      15,    16,    17,    18,    19,    20,    21,    22,    23,    24,
      25,    26,    27,    28,    29,    30,    31,    33,    34,    35,
      36,    37,    38,    39,    40,    41,    43,    44,    45,    46,
      75,    81,    87,    92,    95,   101,    76,    81,    81,    81,
      92,    93,    81,    81,    76,    76,    76,    42,    67,    68,
      70,    71,    72,    73,    74,   106,    42,    47,    48,    49,
      50,    51,    52,    53,    54,    55,    56,    57,    58,    59,
      60,    61,    62,    63,    64,    65,    66,    67,    68,    69,
      70,    71,    72,    73,    74,   105,    76,    76,    75,    76,
      39,    39,    81,    42,    85,   105,    56,    57,    58,    59,
      60,    61,    62,    63,    64,    65,    66,    85,   104,   100,
      43,    43,    76,    43,    43,     3,     5,     6,     7,    75,
      77,    78,    95,    76,    39,    75,    75,    87,    88,    75,
      75,    76,    76,    76,   101,    76,    76,    76,    75,    81,
      86,    92,    76,    86,    81,   103,   103,   103,   103,   103,
     103,   103,    43,    43,    39,    39,    76,    76,   101,    76,
      76,    76,    76,    75,    87,    75,    75,    75,    81,   101,
     101,    76,    89,    87,    76,   102,    98,   100,    91,    88,
      75,    99,    99,    75,    97,    39,    94,    85,   100,    76,
      88,    88,    76,    81,    76,    99,    76,    42,    75,    76,
      81,    90,    92,    76,    81,    98,    98,    81,    96,    39,
      76,    84,    76,    88,    89,    88,    88,    76,    91,    88,
      76,    76,   101,    76,    97,    76,    85,    76,    76,    76,
     101,    76,    76,   101,   101,    76,   101,    76,    76,    76,
      76
};

/* YYR1[RULE-NUM] -- Symbol kind of the left-hand side of rule RULE-NUM.  */
static const yytype_int8 yyr1[] =
{
       0,    79,    80,    81,    81,    82,    82,    83,    83,    83,
      83,    83,    83,    83,    83,    83,    83,    83,    83,    83,
      83,    83,    83,    83,    83,    83,    83,    83,    83,    83,
      83,    83,    83,    83,    83,    84,    84,    85,    85,    85,
      85,    86,    86,    86,    87,    87,    88,    88,    89,    89,
      90,    90,    90,    90,    91,    91,    92,    92,    92,    92,
      92,    93,    93,    94,    94,    95,    95,    96,    96,    97,
      98,    98,    99,   100,   100,   101,   101,   101,   101,   101,
     101,   101,   102,   102,   103,   104,   104,   104,   104,   104,
     104,   104,   104,   104,   104,   104,   104,   105,   105,   105,
     105,   105,   105,   105,   105,   105,   105,   105,   105,   105,
     105,   105,   105,   105,   105,   105,   105,   105,   105,   105,
     105,   105,   105,   105,   105,   106,   106,   106,   106,   106,
     106,   106,   106
};

/* YYR2[RULE-NUM] -- Number of symbols on the right-hand side of rule RULE-NUM.  */
static const yytype_int8 yyr2[] =
{
       0,     2,     1,     1,     1,     0,     2,     4,     4,     4,
       5,     8,     8,     5,     9,     4,     4,     4,     3,     3,
       3,     4,     4,     4,     4,     3,     7,     3,     3,     4,
       4,     4,     3,     3,     4,     0,     2,     1,     2,     1,
       2,     1,     1,     3,     1,     5,     1,     5,     2,     0,
       1,     1,     1,     3,     0,     2,     1,     1,     1,     1,
       1,     1,     1,     2,     1,     1,     5,     0,     2,     4,
       0,     2,     4,     0,     2,     1,     1,     5,     8,     8,
       8,     6,     0,     2,     1,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     1,     1,     1,     1,
       1,     1,     1,     1,     1,     1,     1,     1,     1,     1,
       1,     1,     1,     1,     1,     1,     1,     1,     1,     1,
       1,     1,     1,     1,     1,     1,     1,     1,     1,     1,
       1,     1,     1
};


enum { YYENOMEM = -2 };

#define yyerrok         (yyerrstatus = 0)
#define yyclearin       (yychar = YYEMPTY)

#define YYACCEPT        goto yyacceptlab
#define YYABORT         goto yyabortlab
#define YYERROR         goto yyerrorlab
#define YYNOMEM         goto yyexhaustedlab


#define YYRECOVERING()  (!!yyerrstatus)

#define YYBACKUP(Token, Value)                                    \
  do                                                              \
    if (yychar == YYEMPTY)                                        \
      {                                                           \
        yychar = (Token);                                         \
        yylval = (Value);                                         \
        YYPOPSTACK (yylen);                                       \
        yystate = *yyssp;                                         \
        goto yybackup;                                            \
      }                                                           \
    else                                                          \
      {                                                           \
        yyerror (&yylloc, context, YY_("syntax error: cannot back up")); \
        YYERROR;                                                  \
      }                                                           \
  while (0)

/* Backward compatibility with an undocumented macro.
   Use YYerror or YYUNDEF. */
#define YYERRCODE YYUNDEF

/* YYLLOC_DEFAULT -- Set CURRENT to span from RHS[1] to RHS[N].
   If N is 0, then set CURRENT to the empty location which ends
   the previous symbol: RHS[0] (always defined).  */

#ifndef YYLLOC_DEFAULT
# define YYLLOC_DEFAULT(Current, Rhs, N)                                \
    do                                                                  \
      if (N)                                                            \
        {                                                               \
          (Current).first_line   = YYRHSLOC (Rhs, 1).first_line;        \
          (Current).first_column = YYRHSLOC (Rhs, 1).first_column;      \
          (Current).last_line    = YYRHSLOC (Rhs, N).last_line;         \
          (Current).last_column  = YYRHSLOC (Rhs, N).last_column;       \
        }                                                               \
      else                                                              \
        {                                                               \
          (Current).first_line   = (Current).last_line   =              \
            YYRHSLOC (Rhs, 0).last_line;                                \
          (Current).first_column = (Current).last_column =              \
            YYRHSLOC (Rhs, 0).last_column;                              \
        }                                                               \
    while (0)
#endif

#define YYRHSLOC(Rhs, K) ((Rhs)[K])


/* Enable debugging if requested.  */
#if YYDEBUG

# ifndef YYFPRINTF
#  include <stdio.h> /* INFRINGES ON USER NAME SPACE */
#  define YYFPRINTF fprintf
# endif

# define YYDPRINTF(Args)                        \
do {                                            \
  if (yydebug)                                  \
    YYFPRINTF Args;                             \
} while (0)


/* YYLOCATION_PRINT -- Print the location on the stream.
   This macro was not mandated originally: define only if we know
   we won't break user code: when these are the locations we know.  */

# ifndef YYLOCATION_PRINT

#  if defined YY_LOCATION_PRINT

   /* Temporary convenience wrapper in case some people defined the
      undocumented and private YY_LOCATION_PRINT macros.  */
#   define YYLOCATION_PRINT(File, Loc)  YY_LOCATION_PRINT(File, *(Loc))

#  elif defined YYLTYPE_IS_TRIVIAL && YYLTYPE_IS_TRIVIAL

/* Print *YYLOCP on YYO.  Private, do not rely on its existence. */

YY_ATTRIBUTE_UNUSED
static int
yy_location_print_ (FILE *yyo, YYLTYPE const * const yylocp)
{
  int res = 0;
  int end_col = 0 != yylocp->last_column ? yylocp->last_column - 1 : 0;
  if (0 <= yylocp->first_line)
    {
      res += YYFPRINTF (yyo, "%d", yylocp->first_line);
      if (0 <= yylocp->first_column)
        res += YYFPRINTF (yyo, ".%d", yylocp->first_column);
    }
  if (0 <= yylocp->last_line)
    {
      if (yylocp->first_line < yylocp->last_line)
        {
          res += YYFPRINTF (yyo, "-%d", yylocp->last_line);
          if (0 <= end_col)
            res += YYFPRINTF (yyo, ".%d", end_col);
        }
      else if (0 <= end_col && yylocp->first_column < end_col)
        res += YYFPRINTF (yyo, "-%d", end_col);
    }
  return res;
}

#   define YYLOCATION_PRINT  yy_location_print_

    /* Temporary convenience wrapper in case some people defined the
       undocumented and private YY_LOCATION_PRINT macros.  */
#   define YY_LOCATION_PRINT(File, Loc)  YYLOCATION_PRINT(File, &(Loc))

#  else

#   define YYLOCATION_PRINT(File, Loc) ((void) 0)
    /* Temporary convenience wrapper in case some people defined the
       undocumented and private YY_LOCATION_PRINT macros.  */
#   define YY_LOCATION_PRINT  YYLOCATION_PRINT

#  endif
# endif /* !defined YYLOCATION_PRINT */


# define YY_SYMBOL_PRINT(Title, Kind, Value, Location)                    \
do {                                                                      \
  if (yydebug)                                                            \
    {                                                                     \
      YYFPRINTF (stderr, "%s ", Title);                                   \
      yy_symbol_print (stderr,                                            \
                  Kind, Value, Location, context); \
      YYFPRINTF (stderr, "\n");                                           \
    }                                                                     \
} while (0)


/*-----------------------------------.
| Print this symbol's value on YYO.  |
`-----------------------------------*/

static void
yy_symbol_value_print (FILE *yyo,
                       yysymbol_kind_t yykind, YYSTYPE const * const yyvaluep, YYLTYPE const * const yylocationp, Smt2newContext* context)
{
  FILE *yyoutput = yyo;
  YY_USE (yyoutput);
  YY_USE (yylocationp);
  YY_USE (context);
  if (!yyvaluep)
    return;
  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  YY_USE (yykind);
  YY_IGNORE_MAYBE_UNINITIALIZED_END
}


/*---------------------------.
| Print this symbol on YYO.  |
`---------------------------*/

static void
yy_symbol_print (FILE *yyo,
                 yysymbol_kind_t yykind, YYSTYPE const * const yyvaluep, YYLTYPE const * const yylocationp, Smt2newContext* context)
{
  YYFPRINTF (yyo, "%s %s (",
             yykind < YYNTOKENS ? "token" : "nterm", yysymbol_name (yykind));

  YYLOCATION_PRINT (yyo, yylocationp);
  YYFPRINTF (yyo, ": ");
  yy_symbol_value_print (yyo, yykind, yyvaluep, yylocationp, context);
  YYFPRINTF (yyo, ")");
}

/*------------------------------------------------------------------.
| yy_stack_print -- Print the state stack from its BOTTOM up to its |
| TOP (included).                                                   |
`------------------------------------------------------------------*/

static void
yy_stack_print (yy_state_t *yybottom, yy_state_t *yytop)
{
  YYFPRINTF (stderr, "Stack now");
  for (; yybottom <= yytop; yybottom++)
    {
      int yybot = *yybottom;
      YYFPRINTF (stderr, " %d", yybot);
    }
  YYFPRINTF (stderr, "\n");
}

# define YY_STACK_PRINT(Bottom, Top)                            \
do {                                                            \
  if (yydebug)                                                  \
    yy_stack_print ((Bottom), (Top));                           \
} while (0)


/*------------------------------------------------.
| Report that the YYRULE is going to be reduced.  |
`------------------------------------------------*/

static void
yy_reduce_print (yy_state_t *yyssp, YYSTYPE *yyvsp, YYLTYPE *yylsp,
                 int yyrule, Smt2newContext* context)
{
  int yylno = yyrline[yyrule];
  int yynrhs = yyr2[yyrule];
  int yyi;
  YYFPRINTF (stderr, "Reducing stack by rule %d (line %d):\n",
             yyrule - 1, yylno);
  /* The symbols being reduced.  */
  for (yyi = 0; yyi < yynrhs; yyi++)
    {
      YYFPRINTF (stderr, "   $%d = ", yyi + 1);
      yy_symbol_print (stderr,
                       YY_ACCESSING_SYMBOL (+yyssp[yyi + 1 - yynrhs]),
                       &yyvsp[(yyi + 1) - (yynrhs)],
                       &(yylsp[(yyi + 1) - (yynrhs)]), context);
      YYFPRINTF (stderr, "\n");
    }
}

# define YY_REDUCE_PRINT(Rule)          \
do {                                    \
  if (yydebug)                          \
    yy_reduce_print (yyssp, yyvsp, yylsp, Rule, context); \
} while (0)

/* Nonzero means print parse trace.  It is left uninitialized so that
   multiple parsers can coexist.  */
int yydebug;
#else /* !YYDEBUG */
# define YYDPRINTF(Args) ((void) 0)
# define YY_SYMBOL_PRINT(Title, Kind, Value, Location)
# define YY_STACK_PRINT(Bottom, Top)
# define YY_REDUCE_PRINT(Rule)
#endif /* !YYDEBUG */


/* YYINITDEPTH -- initial size of the parser's stacks.  */
#ifndef YYINITDEPTH
# define YYINITDEPTH 200
#endif

/* YYMAXDEPTH -- maximum size the stacks can grow to (effective only
   if the built-in stack extension method is used).

   Do not make this value too large; the results are undefined if
   YYSTACK_ALLOC_MAXIMUM < YYSTACK_BYTES (YYMAXDEPTH)
   evaluated with infinite-precision integer arithmetic.  */

#ifndef YYMAXDEPTH
# define YYMAXDEPTH 10000
#endif


/* Context of a parse error.  */
typedef struct
{
  yy_state_t *yyssp;
  yysymbol_kind_t yytoken;
  YYLTYPE *yylloc;
} yypcontext_t;

/* Put in YYARG at most YYARGN of the expected tokens given the
   current YYCTX, and return the number of tokens stored in YYARG.  If
   YYARG is null, return the number of expected tokens (guaranteed to
   be less than YYNTOKENS).  Return YYENOMEM on memory exhaustion.
   Return 0 if there are more than YYARGN expected tokens, yet fill
   YYARG up to YYARGN. */
static int
yypcontext_expected_tokens (const yypcontext_t *yyctx,
                            yysymbol_kind_t yyarg[], int yyargn)
{
  /* Actual size of YYARG. */
  int yycount = 0;
  int yyn = yypact[+*yyctx->yyssp];
  if (!yypact_value_is_default (yyn))
    {
      /* Start YYX at -YYN if negative to avoid negative indexes in
         YYCHECK.  In other words, skip the first -YYN actions for
         this state because they are default actions.  */
      int yyxbegin = yyn < 0 ? -yyn : 0;
      /* Stay within bounds of both yycheck and yytname.  */
      int yychecklim = YYLAST - yyn + 1;
      int yyxend = yychecklim < YYNTOKENS ? yychecklim : YYNTOKENS;
      int yyx;
      for (yyx = yyxbegin; yyx < yyxend; ++yyx)
        if (yycheck[yyx + yyn] == yyx && yyx != YYSYMBOL_YYerror
            && !yytable_value_is_error (yytable[yyx + yyn]))
          {
            if (!yyarg)
              ++yycount;
            else if (yycount == yyargn)
              return 0;
            else
              yyarg[yycount++] = YY_CAST (yysymbol_kind_t, yyx);
          }
    }
  if (yyarg && yycount == 0 && 0 < yyargn)
    yyarg[0] = YYSYMBOL_YYEMPTY;
  return yycount;
}




#ifndef yystrlen
# if defined __GLIBC__ && defined _STRING_H
#  define yystrlen(S) (YY_CAST (YYPTRDIFF_T, strlen (S)))
# else
/* Return the length of YYSTR.  */
static YYPTRDIFF_T
yystrlen (const char *yystr)
{
  YYPTRDIFF_T yylen;
  for (yylen = 0; yystr[yylen]; yylen++)
    continue;
  return yylen;
}
# endif
#endif

#ifndef yystpcpy
# if defined __GLIBC__ && defined _STRING_H && defined _GNU_SOURCE
#  define yystpcpy stpcpy
# else
/* Copy YYSRC to YYDEST, returning the address of the terminating '\0' in
   YYDEST.  */
static char *
yystpcpy (char *yydest, const char *yysrc)
{
  char *yyd = yydest;
  const char *yys = yysrc;

  while ((*yyd++ = *yys++) != '\0')
    continue;

  return yyd - 1;
}
# endif
#endif

#ifndef yytnamerr
/* Copy to YYRES the contents of YYSTR after stripping away unnecessary
   quotes and backslashes, so that it's suitable for yyerror.  The
   heuristic is that double-quoting is unnecessary unless the string
   contains an apostrophe, a comma, or backslash (other than
   backslash-backslash).  YYSTR is taken from yytname.  If YYRES is
   null, do not copy; instead, return the length of what the result
   would have been.  */
static YYPTRDIFF_T
yytnamerr (char *yyres, const char *yystr)
{
  if (*yystr == '"')
    {
      YYPTRDIFF_T yyn = 0;
      char const *yyp = yystr;
      for (;;)
        switch (*++yyp)
          {
          case '\'':
          case ',':
            goto do_not_strip_quotes;

          case '\\':
            if (*++yyp != '\\')
              goto do_not_strip_quotes;
            else
              goto append;

          append:
          default:
            if (yyres)
              yyres[yyn] = *yyp;
            yyn++;
            break;

          case '"':
            if (yyres)
              yyres[yyn] = '\0';
            return yyn;
          }
    do_not_strip_quotes: ;
    }

  if (yyres)
    return yystpcpy (yyres, yystr) - yyres;
  else
    return yystrlen (yystr);
}
#endif


static int
yy_syntax_error_arguments (const yypcontext_t *yyctx,
                           yysymbol_kind_t yyarg[], int yyargn)
{
  /* Actual size of YYARG. */
  int yycount = 0;
  /* There are many possibilities here to consider:
     - If this state is a consistent state with a default action, then
       the only way this function was invoked is if the default action
       is an error action.  In that case, don't check for expected
       tokens because there are none.
     - The only way there can be no lookahead present (in yychar) is if
       this state is a consistent state with a default action.  Thus,
       detecting the absence of a lookahead is sufficient to determine
       that there is no unexpected or expected token to report.  In that
       case, just report a simple "syntax error".
     - Don't assume there isn't a lookahead just because this state is a
       consistent state with a default action.  There might have been a
       previous inconsistent state, consistent state with a non-default
       action, or user semantic action that manipulated yychar.
     - Of course, the expected token list depends on states to have
       correct lookahead information, and it depends on the parser not
       to perform extra reductions after fetching a lookahead from the
       scanner and before detecting a syntax error.  Thus, state merging
       (from LALR or IELR) and default reductions corrupt the expected
       token list.  However, the list is correct for canonical LR with
       one exception: it will still contain any token that will not be
       accepted due to an error action in a later state.
  */
  if (yyctx->yytoken != YYSYMBOL_YYEMPTY)
    {
      int yyn;
      if (yyarg)
        yyarg[yycount] = yyctx->yytoken;
      ++yycount;
      yyn = yypcontext_expected_tokens (yyctx,
                                        yyarg ? yyarg + 1 : yyarg, yyargn - 1);
      if (yyn == YYENOMEM)
        return YYENOMEM;
      else
        yycount += yyn;
    }
  return yycount;
}

/* Copy into *YYMSG, which is of size *YYMSG_ALLOC, an error message
   about the unexpected token YYTOKEN for the state stack whose top is
   YYSSP.

   Return 0 if *YYMSG was successfully written.  Return -1 if *YYMSG is
   not large enough to hold the message.  In that case, also set
   *YYMSG_ALLOC to the required number of bytes.  Return YYENOMEM if the
   required number of bytes is too large to store.  */
static int
yysyntax_error (YYPTRDIFF_T *yymsg_alloc, char **yymsg,
                const yypcontext_t *yyctx)
{
  enum { YYARGS_MAX = 5 };
  /* Internationalized format string. */
  const char *yyformat = YY_NULLPTR;
  /* Arguments of yyformat: reported tokens (one for the "unexpected",
     one per "expected"). */
  yysymbol_kind_t yyarg[YYARGS_MAX];
  /* Cumulated lengths of YYARG.  */
  YYPTRDIFF_T yysize = 0;

  /* Actual size of YYARG. */
  int yycount = yy_syntax_error_arguments (yyctx, yyarg, YYARGS_MAX);
  if (yycount == YYENOMEM)
    return YYENOMEM;

  switch (yycount)
    {
#define YYCASE_(N, S)                       \
      case N:                               \
        yyformat = S;                       \
        break
    default: /* Avoid compiler warnings. */
      YYCASE_(0, YY_("syntax error"));
      YYCASE_(1, YY_("syntax error, unexpected %s"));
      YYCASE_(2, YY_("syntax error, unexpected %s, expecting %s"));
      YYCASE_(3, YY_("syntax error, unexpected %s, expecting %s or %s"));
      YYCASE_(4, YY_("syntax error, unexpected %s, expecting %s or %s or %s"));
      YYCASE_(5, YY_("syntax error, unexpected %s, expecting %s or %s or %s or %s"));
#undef YYCASE_
    }

  /* Compute error message size.  Don't count the "%s"s, but reserve
     room for the terminator.  */
  yysize = yystrlen (yyformat) - 2 * yycount + 1;
  {
    int yyi;
    for (yyi = 0; yyi < yycount; ++yyi)
      {
        YYPTRDIFF_T yysize1
          = yysize + yytnamerr (YY_NULLPTR, yytname[yyarg[yyi]]);
        if (yysize <= yysize1 && yysize1 <= YYSTACK_ALLOC_MAXIMUM)
          yysize = yysize1;
        else
          return YYENOMEM;
      }
  }

  if (*yymsg_alloc < yysize)
    {
      *yymsg_alloc = 2 * yysize;
      if (! (yysize <= *yymsg_alloc
             && *yymsg_alloc <= YYSTACK_ALLOC_MAXIMUM))
        *yymsg_alloc = YYSTACK_ALLOC_MAXIMUM;
      return -1;
    }

  /* Avoid sprintf, as that infringes on the user's name space.
     Don't have undefined behavior even if the translation
     produced a string with the wrong number of "%s"s.  */
  {
    char *yyp = *yymsg;
    int yyi = 0;
    while ((*yyp = *yyformat) != '\0')
      if (*yyp == '%' && yyformat[1] == 's' && yyi < yycount)
        {
          yyp += yytnamerr (yyp, yytname[yyarg[yyi++]]);
          yyformat += 2;
        }
      else
        {
          ++yyp;
          ++yyformat;
        }
  }
  return 0;
}


/*-----------------------------------------------.
| Release the memory associated to this symbol.  |
`-----------------------------------------------*/

static void
yydestruct (const char *yymsg,
            yysymbol_kind_t yykind, YYSTYPE *yyvaluep, YYLTYPE *yylocationp, Smt2newContext* context)
{
  YY_USE (yyvaluep);
  YY_USE (yylocationp);
  YY_USE (context);
  if (!yymsg)
    yymsg = "Deleting";
  YY_SYMBOL_PRINT (yymsg, yykind, yyvaluep, yylocationp);

  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  switch (yykind)
    {
    case YYSYMBOL_TK_NUM: /* TK_NUM  */
#line 73 "smt2newparser.yy"
            { free(((*yyvaluep).str)); }
#line 1510 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
        break;

    case YYSYMBOL_TK_SYM: /* TK_SYM  */
#line 73 "smt2newparser.yy"
            { free(((*yyvaluep).str)); }
#line 1516 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
        break;

    case YYSYMBOL_TK_QSYM: /* TK_QSYM  */
#line 73 "smt2newparser.yy"
            { free(((*yyvaluep).str)); }
#line 1522 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
        break;

    case YYSYMBOL_TK_KEY: /* TK_KEY  */
#line 73 "smt2newparser.yy"
            { free(((*yyvaluep).str)); }
#line 1528 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
        break;

    case YYSYMBOL_TK_STR: /* TK_STR  */
#line 73 "smt2newparser.yy"
            { free(((*yyvaluep).str)); }
#line 1534 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
        break;

    case YYSYMBOL_TK_DEC: /* TK_DEC  */
#line 73 "smt2newparser.yy"
            { free(((*yyvaluep).str)); }
#line 1540 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
        break;

    case YYSYMBOL_TK_HEX: /* TK_HEX  */
#line 73 "smt2newparser.yy"
            { free(((*yyvaluep).str)); }
#line 1546 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
        break;

    case YYSYMBOL_TK_BIN: /* TK_BIN  */
#line 73 "smt2newparser.yy"
            { free(((*yyvaluep).str)); }
#line 1552 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
        break;

    case YYSYMBOL_KW_SORTS: /* KW_SORTS  */
#line 73 "smt2newparser.yy"
            { free(((*yyvaluep).str)); }
#line 1558 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
        break;

    case YYSYMBOL_KW_FUNS: /* KW_FUNS  */
#line 73 "smt2newparser.yy"
            { free(((*yyvaluep).str)); }
#line 1564 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
        break;

    case YYSYMBOL_KW_SORTSDESCRIPTION: /* KW_SORTSDESCRIPTION  */
#line 73 "smt2newparser.yy"
            { free(((*yyvaluep).str)); }
#line 1570 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
        break;

    case YYSYMBOL_KW_FUNSDESCRIPTION: /* KW_FUNSDESCRIPTION  */
#line 73 "smt2newparser.yy"
            { free(((*yyvaluep).str)); }
#line 1576 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
        break;

    case YYSYMBOL_KW_DEFINITION: /* KW_DEFINITION  */
#line 73 "smt2newparser.yy"
            { free(((*yyvaluep).str)); }
#line 1582 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
        break;

    case YYSYMBOL_KW_NOTES: /* KW_NOTES  */
#line 73 "smt2newparser.yy"
            { free(((*yyvaluep).str)); }
#line 1588 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
        break;

    case YYSYMBOL_KW_THEORIES: /* KW_THEORIES  */
#line 73 "smt2newparser.yy"
            { free(((*yyvaluep).str)); }
#line 1594 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
        break;

    case YYSYMBOL_KW_EXTENSIONS: /* KW_EXTENSIONS  */
#line 73 "smt2newparser.yy"
            { free(((*yyvaluep).str)); }
#line 1600 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
        break;

    case YYSYMBOL_KW_VALUES: /* KW_VALUES  */
#line 73 "smt2newparser.yy"
            { free(((*yyvaluep).str)); }
#line 1606 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
        break;

    case YYSYMBOL_KW_PRINTSUCCESS: /* KW_PRINTSUCCESS  */
#line 73 "smt2newparser.yy"
            { free(((*yyvaluep).str)); }
#line 1612 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
        break;

    case YYSYMBOL_KW_EXPANDDEFINITIONS: /* KW_EXPANDDEFINITIONS  */
#line 73 "smt2newparser.yy"
            { free(((*yyvaluep).str)); }
#line 1618 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
        break;

    case YYSYMBOL_KW_INTERACTIVEMODE: /* KW_INTERACTIVEMODE  */
#line 73 "smt2newparser.yy"
            { free(((*yyvaluep).str)); }
#line 1624 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
        break;

    case YYSYMBOL_KW_PRODUCEPROOFS: /* KW_PRODUCEPROOFS  */
#line 73 "smt2newparser.yy"
            { free(((*yyvaluep).str)); }
#line 1630 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
        break;

    case YYSYMBOL_KW_PRODUCEUNSATCORES: /* KW_PRODUCEUNSATCORES  */
#line 73 "smt2newparser.yy"
            { free(((*yyvaluep).str)); }
#line 1636 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
        break;

    case YYSYMBOL_KW_PRODUCEMODELS: /* KW_PRODUCEMODELS  */
#line 73 "smt2newparser.yy"
            { free(((*yyvaluep).str)); }
#line 1642 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
        break;

    case YYSYMBOL_KW_PRODUCEASSIGNMENTS: /* KW_PRODUCEASSIGNMENTS  */
#line 73 "smt2newparser.yy"
            { free(((*yyvaluep).str)); }
#line 1648 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
        break;

    case YYSYMBOL_KW_REGULAROUTPUTCHANNEL: /* KW_REGULAROUTPUTCHANNEL  */
#line 73 "smt2newparser.yy"
            { free(((*yyvaluep).str)); }
#line 1654 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
        break;

    case YYSYMBOL_KW_DIAGNOSTICOUTPUTCHANNEL: /* KW_DIAGNOSTICOUTPUTCHANNEL  */
#line 73 "smt2newparser.yy"
            { free(((*yyvaluep).str)); }
#line 1660 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
        break;

    case YYSYMBOL_KW_RANDOMSEED: /* KW_RANDOMSEED  */
#line 73 "smt2newparser.yy"
            { free(((*yyvaluep).str)); }
#line 1666 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
        break;

    case YYSYMBOL_KW_VERBOSITY: /* KW_VERBOSITY  */
#line 73 "smt2newparser.yy"
            { free(((*yyvaluep).str)); }
#line 1672 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
        break;

    case YYSYMBOL_KW_ERRORBEHAVIOR: /* KW_ERRORBEHAVIOR  */
#line 73 "smt2newparser.yy"
            { free(((*yyvaluep).str)); }
#line 1678 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
        break;

    case YYSYMBOL_KW_NAME: /* KW_NAME  */
#line 73 "smt2newparser.yy"
            { free(((*yyvaluep).str)); }
#line 1684 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
        break;

    case YYSYMBOL_KW_NAMED: /* KW_NAMED  */
#line 73 "smt2newparser.yy"
            { free(((*yyvaluep).str)); }
#line 1690 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
        break;

    case YYSYMBOL_KW_AUTHORS: /* KW_AUTHORS  */
#line 73 "smt2newparser.yy"
            { free(((*yyvaluep).str)); }
#line 1696 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
        break;

    case YYSYMBOL_KW_VERSION: /* KW_VERSION  */
#line 73 "smt2newparser.yy"
            { free(((*yyvaluep).str)); }
#line 1702 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
        break;

    case YYSYMBOL_KW_STATUS: /* KW_STATUS  */
#line 73 "smt2newparser.yy"
            { free(((*yyvaluep).str)); }
#line 1708 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
        break;

    case YYSYMBOL_KW_REASONUNKNOWN: /* KW_REASONUNKNOWN  */
#line 73 "smt2newparser.yy"
            { free(((*yyvaluep).str)); }
#line 1714 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
        break;

    case YYSYMBOL_KW_ALLSTATISTICS: /* KW_ALLSTATISTICS  */
#line 73 "smt2newparser.yy"
            { free(((*yyvaluep).str)); }
#line 1720 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
        break;

    case YYSYMBOL_symbol: /* symbol  */
#line 74 "smt2newparser.yy"
            { delete ((*yyvaluep).snode); }
#line 1726 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
        break;

    case YYSYMBOL_command_list: /* command_list  */
#line 75 "smt2newparser.yy"
            { if (((*yyvaluep).snode_list)) { for (auto node : *((*yyvaluep).snode_list)) { delete node; } delete ((*yyvaluep).snode_list); }}
#line 1732 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
        break;

    case YYSYMBOL_command: /* command  */
#line 74 "smt2newparser.yy"
            { delete ((*yyvaluep).snode); }
#line 1738 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
        break;

    case YYSYMBOL_attribute_list: /* attribute_list  */
#line 75 "smt2newparser.yy"
            { if (((*yyvaluep).snode_list)) { for (auto node : *((*yyvaluep).snode_list)) { delete node; } delete ((*yyvaluep).snode_list); }}
#line 1744 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
        break;

    case YYSYMBOL_attribute: /* attribute  */
#line 74 "smt2newparser.yy"
            { delete ((*yyvaluep).snode); }
#line 1750 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
        break;

    case YYSYMBOL_attribute_value: /* attribute_value  */
#line 74 "smt2newparser.yy"
            { delete ((*yyvaluep).snode); }
#line 1756 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
        break;

    case YYSYMBOL_identifier: /* identifier  */
#line 74 "smt2newparser.yy"
            { delete ((*yyvaluep).snode); }
#line 1762 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
        break;

    case YYSYMBOL_sort: /* sort  */
#line 74 "smt2newparser.yy"
            { delete ((*yyvaluep).snode); }
#line 1768 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
        break;

    case YYSYMBOL_sort_list: /* sort_list  */
#line 75 "smt2newparser.yy"
            { if (((*yyvaluep).snode_list)) { for (auto node : *((*yyvaluep).snode_list)) { delete node; } delete ((*yyvaluep).snode_list); }}
#line 1774 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
        break;

    case YYSYMBOL_s_expr: /* s_expr  */
#line 74 "smt2newparser.yy"
            { delete ((*yyvaluep).snode); }
#line 1780 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
        break;

    case YYSYMBOL_s_expr_list: /* s_expr_list  */
#line 75 "smt2newparser.yy"
            { if (((*yyvaluep).snode_list)) { for (auto node : *((*yyvaluep).snode_list)) { delete node; } delete ((*yyvaluep).snode_list); }}
#line 1786 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
        break;

    case YYSYMBOL_spec_const: /* spec_const  */
#line 74 "smt2newparser.yy"
            { delete ((*yyvaluep).snode); }
#line 1792 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
        break;

    case YYSYMBOL_const_val: /* const_val  */
#line 74 "smt2newparser.yy"
            { delete ((*yyvaluep).snode); }
#line 1798 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
        break;

    case YYSYMBOL_numeral_list: /* numeral_list  */
#line 75 "smt2newparser.yy"
            { if (((*yyvaluep).snode_list)) { for (auto node : *((*yyvaluep).snode_list)) { delete node; } delete ((*yyvaluep).snode_list); }}
#line 1804 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
        break;

    case YYSYMBOL_qual_identifier: /* qual_identifier  */
#line 74 "smt2newparser.yy"
            { delete ((*yyvaluep).snode); }
#line 1810 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
        break;

    case YYSYMBOL_var_binding_list: /* var_binding_list  */
#line 75 "smt2newparser.yy"
            { if (((*yyvaluep).snode_list)) { for (auto node : *((*yyvaluep).snode_list)) { delete node; } delete ((*yyvaluep).snode_list); }}
#line 1816 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
        break;

    case YYSYMBOL_var_binding: /* var_binding  */
#line 74 "smt2newparser.yy"
            { delete ((*yyvaluep).snode); }
#line 1822 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
        break;

    case YYSYMBOL_sorted_var_list: /* sorted_var_list  */
#line 75 "smt2newparser.yy"
            { if (((*yyvaluep).snode_list)) { for (auto node : *((*yyvaluep).snode_list)) { delete node; } delete ((*yyvaluep).snode_list); }}
#line 1828 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
        break;

    case YYSYMBOL_sorted_var: /* sorted_var  */
#line 74 "smt2newparser.yy"
            { delete ((*yyvaluep).snode); }
#line 1834 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
        break;

    case YYSYMBOL_term_list: /* term_list  */
#line 75 "smt2newparser.yy"
            { if (((*yyvaluep).snode_list)) { for (auto node : *((*yyvaluep).snode_list)) { delete node; } delete ((*yyvaluep).snode_list); }}
#line 1840 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
        break;

    case YYSYMBOL_term: /* term  */
#line 74 "smt2newparser.yy"
            { delete ((*yyvaluep).snode); }
#line 1846 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
        break;

    case YYSYMBOL_symbol_list: /* symbol_list  */
#line 75 "smt2newparser.yy"
            { if (((*yyvaluep).snode_list)) { for (auto node : *((*yyvaluep).snode_list)) { delete node; } delete ((*yyvaluep).snode_list); }}
#line 1852 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
        break;

    case YYSYMBOL_b_value: /* b_value  */
#line 74 "smt2newparser.yy"
            { delete ((*yyvaluep).snode); }
#line 1858 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
        break;

    case YYSYMBOL_option: /* option  */
#line 74 "smt2newparser.yy"
            { delete ((*yyvaluep).snode); }
#line 1864 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
        break;

    case YYSYMBOL_predef_key: /* predef_key  */
#line 73 "smt2newparser.yy"
            { free(((*yyvaluep).str)); }
#line 1870 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
        break;

    case YYSYMBOL_info_flag: /* info_flag  */
#line 74 "smt2newparser.yy"
            { delete ((*yyvaluep).snode); }
#line 1876 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
        break;

      default:
        break;
    }
  YY_IGNORE_MAYBE_UNINITIALIZED_END
}






/*----------.
| yyparse.  |
`----------*/

int
yyparse (Smt2newContext* context)
{
/* Lookahead token kind.  */
int yychar;


/* The semantic value of the lookahead symbol.  */
/* Default value used for initialization, for pacifying older GCCs
   or non-GCC compilers.  */
YY_INITIAL_VALUE (static YYSTYPE yyval_default;)
YYSTYPE yylval YY_INITIAL_VALUE (= yyval_default);

/* Location data for the lookahead symbol.  */
static YYLTYPE yyloc_default
# if defined YYLTYPE_IS_TRIVIAL && YYLTYPE_IS_TRIVIAL
  = { 1, 1, 1, 1 }
# endif
;
YYLTYPE yylloc = yyloc_default;

    /* Number of syntax errors so far.  */
    int yynerrs = 0;

    yy_state_fast_t yystate = 0;
    /* Number of tokens to shift before error messages enabled.  */
    int yyerrstatus = 0;

    /* Refer to the stacks through separate pointers, to allow yyoverflow
       to reallocate them elsewhere.  */

    /* Their size.  */
    YYPTRDIFF_T yystacksize = YYINITDEPTH;

    /* The state stack: array, bottom, top.  */
    yy_state_t yyssa[YYINITDEPTH];
    yy_state_t *yyss = yyssa;
    yy_state_t *yyssp = yyss;

    /* The semantic value stack: array, bottom, top.  */
    YYSTYPE yyvsa[YYINITDEPTH];
    YYSTYPE *yyvs = yyvsa;
    YYSTYPE *yyvsp = yyvs;

    /* The location stack: array, bottom, top.  */
    YYLTYPE yylsa[YYINITDEPTH];
    YYLTYPE *yyls = yylsa;
    YYLTYPE *yylsp = yyls;

  int yyn;
  /* The return value of yyparse.  */
  int yyresult;
  /* Lookahead symbol kind.  */
  yysymbol_kind_t yytoken = YYSYMBOL_YYEMPTY;
  /* The variables used to return semantic value and location from the
     action routines.  */
  YYSTYPE yyval;
  YYLTYPE yyloc;

  /* The locations where the error started and ended.  */
  YYLTYPE yyerror_range[3];

  /* Buffer for error messages, and its allocated size.  */
  char yymsgbuf[128];
  char *yymsg = yymsgbuf;
  YYPTRDIFF_T yymsg_alloc = sizeof yymsgbuf;

#define YYPOPSTACK(N)   (yyvsp -= (N), yyssp -= (N), yylsp -= (N))

  /* The number of symbols on the RHS of the reduced rule.
     Keep to zero when no symbol should be popped.  */
  int yylen = 0;

  YYDPRINTF ((stderr, "Starting parse\n"));

  yychar = YYEMPTY; /* Cause a token to be read.  */

  yylsp[0] = yylloc;
  goto yysetstate;


/*------------------------------------------------------------.
| yynewstate -- push a new state, which is found in yystate.  |
`------------------------------------------------------------*/
yynewstate:
  /* In all cases, when you get here, the value and location stacks
     have just been pushed.  So pushing a state here evens the stacks.  */
  yyssp++;


/*--------------------------------------------------------------------.
| yysetstate -- set current state (the top of the stack) to yystate.  |
`--------------------------------------------------------------------*/
yysetstate:
  YYDPRINTF ((stderr, "Entering state %d\n", yystate));
  YY_ASSERT (0 <= yystate && yystate < YYNSTATES);
  YY_IGNORE_USELESS_CAST_BEGIN
  *yyssp = YY_CAST (yy_state_t, yystate);
  YY_IGNORE_USELESS_CAST_END
  YY_STACK_PRINT (yyss, yyssp);

  if (yyss + yystacksize - 1 <= yyssp)
#if !defined yyoverflow && !defined YYSTACK_RELOCATE
    YYNOMEM;
#else
    {
      /* Get the current used size of the three stacks, in elements.  */
      YYPTRDIFF_T yysize = yyssp - yyss + 1;

# if defined yyoverflow
      {
        /* Give user a chance to reallocate the stack.  Use copies of
           these so that the &'s don't force the real ones into
           memory.  */
        yy_state_t *yyss1 = yyss;
        YYSTYPE *yyvs1 = yyvs;
        YYLTYPE *yyls1 = yyls;

        /* Each stack pointer address is followed by the size of the
           data in use in that stack, in bytes.  This used to be a
           conditional around just the two extra args, but that might
           be undefined if yyoverflow is a macro.  */
        yyoverflow (YY_("memory exhausted"),
                    &yyss1, yysize * YYSIZEOF (*yyssp),
                    &yyvs1, yysize * YYSIZEOF (*yyvsp),
                    &yyls1, yysize * YYSIZEOF (*yylsp),
                    &yystacksize);
        yyss = yyss1;
        yyvs = yyvs1;
        yyls = yyls1;
      }
# else /* defined YYSTACK_RELOCATE */
      /* Extend the stack our own way.  */
      if (YYMAXDEPTH <= yystacksize)
        YYNOMEM;
      yystacksize *= 2;
      if (YYMAXDEPTH < yystacksize)
        yystacksize = YYMAXDEPTH;

      {
        yy_state_t *yyss1 = yyss;
        union yyalloc *yyptr =
          YY_CAST (union yyalloc *,
                   YYSTACK_ALLOC (YY_CAST (YYSIZE_T, YYSTACK_BYTES (yystacksize))));
        if (! yyptr)
          YYNOMEM;
        YYSTACK_RELOCATE (yyss_alloc, yyss);
        YYSTACK_RELOCATE (yyvs_alloc, yyvs);
        YYSTACK_RELOCATE (yyls_alloc, yyls);
#  undef YYSTACK_RELOCATE
        if (yyss1 != yyssa)
          YYSTACK_FREE (yyss1);
      }
# endif

      yyssp = yyss + yysize - 1;
      yyvsp = yyvs + yysize - 1;
      yylsp = yyls + yysize - 1;

      YY_IGNORE_USELESS_CAST_BEGIN
      YYDPRINTF ((stderr, "Stack size increased to %ld\n",
                  YY_CAST (long, yystacksize)));
      YY_IGNORE_USELESS_CAST_END

      if (yyss + yystacksize - 1 <= yyssp)
        YYABORT;
    }
#endif /* !defined yyoverflow && !defined YYSTACK_RELOCATE */


  if (yystate == YYFINAL)
    YYACCEPT;

  goto yybackup;


/*-----------.
| yybackup.  |
`-----------*/
yybackup:
  /* Do appropriate processing given the current state.  Read a
     lookahead token if we need one and don't already have one.  */

  /* First try to decide what to do without reference to lookahead token.  */
  yyn = yypact[yystate];
  if (yypact_value_is_default (yyn))
    goto yydefault;

  /* Not known => get a lookahead token if don't already have one.  */

  /* YYCHAR is either empty, or end-of-input, or a valid lookahead.  */
  if (yychar == YYEMPTY)
    {
      YYDPRINTF ((stderr, "Reading a token\n"));
      yychar = yylex (&yylval, &yylloc, scanner);
    }

  if (yychar <= YYEOF)
    {
      yychar = YYEOF;
      yytoken = YYSYMBOL_YYEOF;
      YYDPRINTF ((stderr, "Now at end of input.\n"));
    }
  else if (yychar == YYerror)
    {
      /* The scanner already issued an error message, process directly
         to error recovery.  But do not keep the error token as
         lookahead, it is too special and may lead us to an endless
         loop in error recovery. */
      yychar = YYUNDEF;
      yytoken = YYSYMBOL_YYerror;
      yyerror_range[1] = yylloc;
      goto yyerrlab1;
    }
  else
    {
      yytoken = YYTRANSLATE (yychar);
      YY_SYMBOL_PRINT ("Next token is", yytoken, &yylval, &yylloc);
    }

  /* If the proper action on seeing token YYTOKEN is to reduce or to
     detect an error, take that action.  */
  yyn += yytoken;
  if (yyn < 0 || YYLAST < yyn || yycheck[yyn] != yytoken)
    goto yydefault;
  yyn = yytable[yyn];
  if (yyn <= 0)
    {
      if (yytable_value_is_error (yyn))
        goto yyerrlab;
      yyn = -yyn;
      goto yyreduce;
    }

  /* Count tokens shifted since error; after three, turn off error
     status.  */
  if (yyerrstatus)
    yyerrstatus--;

  /* Shift the lookahead token.  */
  YY_SYMBOL_PRINT ("Shifting", yytoken, &yylval, &yylloc);
  yystate = yyn;
  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  *++yyvsp = yylval;
  YY_IGNORE_MAYBE_UNINITIALIZED_END
  *++yylsp = yylloc;

  /* Discard the shifted token.  */
  yychar = YYEMPTY;
  goto yynewstate;


/*-----------------------------------------------------------.
| yydefault -- do the default action for the current state.  |
`-----------------------------------------------------------*/
yydefault:
  yyn = yydefact[yystate];
  if (yyn == 0)
    goto yyerrlab;
  goto yyreduce;


/*-----------------------------.
| yyreduce -- do a reduction.  |
`-----------------------------*/
yyreduce:
  /* yyn is the number of a rule to reduce with.  */
  yylen = yyr2[yyn];

  /* If YYLEN is nonzero, implement the default value of the action:
     '$$ = $1'.

     Otherwise, the following line sets YYVAL to garbage.
     This behavior is undocumented and Bison
     users should not rely upon it.  Assigning to YYVAL
     unconditionally makes the parser a bit smaller, and it avoids a
     GCC warning that YYVAL may be used uninitialized.  */
  yyval = yyvsp[1-yylen];

  /* Default location. */
  YYLLOC_DEFAULT (yyloc, (yylsp - yylen), yylen);
  yyerror_range[1] = yyloc;
  YY_REDUCE_PRINT (yyn);
  switch (yyn)
    {
  case 2: /* script: command_list  */
#line 96 "smt2newparser.yy"
                     { ASTNode *n = new ASTNode(CMDL_T, strdup("main-script")); n->children = (yyvsp[0].snode_list); context->insertRoot(n); }
#line 2182 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 3: /* symbol: TK_SYM  */
#line 99 "smt2newparser.yy"
        { (yyval.snode) = new ASTNode(SYM_T, (yyvsp[0].str)); }
#line 2188 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 4: /* symbol: TK_QSYM  */
#line 101 "smt2newparser.yy"
        { (yyval.snode) = new ASTNode(QSYM_T, (yyvsp[0].str)); }
#line 2194 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 5: /* command_list: %empty  */
#line 105 "smt2newparser.yy"
        { (yyval.snode_list) = new std::vector<ASTNode*>(); }
#line 2200 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 6: /* command_list: command_list command  */
#line 107 "smt2newparser.yy"
        { (*(yyvsp[-1].snode_list)).push_back((yyvsp[0].snode)); (yyval.snode_list) = (yyvsp[-1].snode_list); }
#line 2206 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 7: /* command: '(' TK_SETLOGIC symbol ')'  */
#line 111 "smt2newparser.yy"
        {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[-2].tok));
            (yyval.snode)->children = new std::vector<ASTNode*>();
            (yyval.snode)->children->push_back((yyvsp[-1].snode));
        }
#line 2216 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 8: /* command: '(' TK_SETOPTION option ')'  */
#line 117 "smt2newparser.yy"
        {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[-2].tok));
            (yyval.snode)->children = new std::vector<ASTNode*>();
            (yyval.snode)->children->push_back((yyvsp[-1].snode));
        }
#line 2226 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 9: /* command: '(' TK_SETINFO attribute ')'  */
#line 123 "smt2newparser.yy"
        {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[-2].tok));
            (yyval.snode)->children = new std::vector<ASTNode*>();
            (yyval.snode)->children->push_back((yyvsp[-1].snode));
        }
#line 2236 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 10: /* command: '(' TK_DECLARESORT symbol TK_NUM ')'  */
#line 129 "smt2newparser.yy"
        {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[-3].tok));
            (yyval.snode)->children = new std::vector<ASTNode*>();
            (yyval.snode)->children->push_back((yyvsp[-2].snode));
            (yyval.snode)->children->push_back(new ASTNode(NUM_T, (yyvsp[-1].str)));
        }
#line 2247 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 11: /* command: '(' TK_DEFINESORT symbol '(' symbol_list ')' sort ')'  */
#line 136 "smt2newparser.yy"
        {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[-6].tok));
            (yyval.snode)->children = new std::vector<ASTNode*>();
            (yyval.snode)->children->push_back((yyvsp[-5].snode));

            ASTNode* syml = new ASTNode(SYML_T, NULL);
            syml->children = (yyvsp[-3].snode_list);
            (yyval.snode)->children->push_back(syml);

            (yyval.snode)->children->push_back((yyvsp[-1].snode));
        }
#line 2263 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 12: /* command: '(' TK_DECLAREFUN symbol '(' sort_list ')' sort ')'  */
#line 149 "smt2newparser.yy"
        {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[-6].tok));
            (yyval.snode)->children = new std::vector<ASTNode*>();
            (yyval.snode)->children->push_back((yyvsp[-5].snode));

            ASTNode* sortl = new ASTNode(SORTL_T, NULL);
            sortl->children = (yyvsp[-3].snode_list);
            (yyval.snode)->children->push_back(sortl);

            (yyval.snode)->children->push_back((yyvsp[-1].snode));
        }
#line 2279 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 13: /* command: '(' TK_DECLARECONST const_val sort ')'  */
#line 161 "smt2newparser.yy"
        {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[-3].tok));
            (yyval.snode)->children = new std::vector<ASTNode*>();
            (yyval.snode)->children->push_back((yyvsp[-2].snode));

            ASTNode* sortl = new ASTNode(SORTL_T, NULL);
            sortl->children = new std::vector<ASTNode*>();
            (yyval.snode)->children->push_back(sortl);

            (yyval.snode)->children->push_back((yyvsp[-1].snode));
        }
#line 2295 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 14: /* command: '(' TK_DEFINEFUN symbol '(' sorted_var_list ')' sort term ')'  */
#line 173 "smt2newparser.yy"
        {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[-7].tok));
            (yyval.snode)->children = new std::vector<ASTNode*>();
            (yyval.snode)->children->push_back((yyvsp[-6].snode));

            ASTNode* svl = new ASTNode(SVL_T, NULL);
            svl->children = (yyvsp[-4].snode_list);
            (yyval.snode)->children->push_back(svl);

            (yyval.snode)->children->push_back((yyvsp[-2].snode));
            (yyval.snode)->children->push_back((yyvsp[-1].snode));
        }
#line 2312 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 15: /* command: '(' TK_PUSH TK_NUM ')'  */
#line 186 "smt2newparser.yy"
        {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[-2].tok));
            (yyval.snode)->children = new std::vector<ASTNode*>();
            (yyval.snode)->children->push_back(new ASTNode(NUM_T, (yyvsp[-1].str)));
        }
#line 2322 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 16: /* command: '(' TK_POP TK_NUM ')'  */
#line 192 "smt2newparser.yy"
        {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[-2].tok));
            (yyval.snode)->children = new std::vector<ASTNode*>();
            (yyval.snode)->children->push_back(new ASTNode(NUM_T, (yyvsp[-1].str)));
        }
#line 2332 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 17: /* command: '(' TK_ASSERT term ')'  */
#line 198 "smt2newparser.yy"
        {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[-2].tok));
            (yyval.snode)->children = new std::vector<ASTNode*>();
            (yyval.snode)->children->push_back((yyvsp[-1].snode));
        }
#line 2342 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 18: /* command: '(' TK_CHECKSAT ')'  */
#line 204 "smt2newparser.yy"
        {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[-1].tok));
        }
#line 2350 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 19: /* command: '(' TK_GETASSERTIONS ')'  */
#line 208 "smt2newparser.yy"
        {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[-1].tok));
        }
#line 2358 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 20: /* command: '(' TK_GETPROOF ')'  */
#line 212 "smt2newparser.yy"
        {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[-1].tok));
        }
#line 2366 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 21: /* command: '(' TK_GETITPS term_list ')'  */
#line 216 "smt2newparser.yy"
        {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[-2].tok));
            (yyval.snode)->children = (yyvsp[-1].snode_list);
        }
#line 2375 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 22: /* command: '(' TK_WRSTATE TK_STR ')'  */
#line 221 "smt2newparser.yy"
        {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[-2].tok));
            (yyval.snode)->children = new std::vector<ASTNode*>();
            (yyval.snode)->children->push_back(new ASTNode(UATTR_T, (yyvsp[-1].str)));
        }
#line 2385 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 23: /* command: '(' TK_RDSTATE TK_STR ')'  */
#line 227 "smt2newparser.yy"
        {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[-2].tok));
            (yyval.snode)->children = new std::vector<ASTNode*>();
            (yyval.snode)->children->push_back(new ASTNode(UATTR_T, (yyvsp[-1].str)));
        }
#line 2395 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 24: /* command: '(' TK_WRFUNS TK_STR ')'  */
#line 233 "smt2newparser.yy"
        {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[-2].tok));
            (yyval.snode)->children = new std::vector<ASTNode*>();
            (yyval.snode)->children->push_back(new ASTNode(UATTR_T, (yyvsp[-1].str)));
        }
#line 2405 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 25: /* command: '(' TK_GETUNSATCORE ')'  */
#line 239 "smt2newparser.yy"
        {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[-1].tok));
        }
#line 2413 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 26: /* command: '(' TK_GETVALUE '(' term term_list ')' ')'  */
#line 243 "smt2newparser.yy"
        {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[-5].tok));
            (yyval.snode)->children = (yyvsp[-2].snode_list);
            (yyval.snode)->children->insert((yyval.snode)->children->begin(), (yyvsp[-3].snode));
        }
#line 2423 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 27: /* command: '(' TK_GETMODEL ')'  */
#line 249 "smt2newparser.yy"
            {
                (yyval.snode) = new ASTNode(CMD_T, (yyvsp[-1].tok));
            }
#line 2431 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 28: /* command: '(' TK_GETASSIGNMENT ')'  */
#line 253 "smt2newparser.yy"
        {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[-1].tok));
        }
#line 2439 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 29: /* command: '(' TK_GETOPTION TK_KEY ')'  */
#line 257 "smt2newparser.yy"
        {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[-2].tok));
            (yyval.snode)->children = new std::vector<ASTNode*>();
            (yyval.snode)->children->push_back(new ASTNode(UATTR_T, (yyvsp[-1].str)));
        }
#line 2449 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 30: /* command: '(' TK_GETOPTION predef_key ')'  */
#line 263 "smt2newparser.yy"
        {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[-2].tok));
            (yyval.snode)->children = new std::vector<ASTNode*>();
            (yyval.snode)->children->push_back(new ASTNode(PATTR_T, (yyvsp[-1].str)));
        }
#line 2459 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 31: /* command: '(' TK_GETINFO info_flag ')'  */
#line 269 "smt2newparser.yy"
        {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[-2].tok));
            (yyval.snode)->children = new std::vector<ASTNode*>();
            (yyval.snode)->children->push_back((yyvsp[-1].snode));
        }
#line 2469 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 32: /* command: '(' TK_SIMPLIFY ')'  */
#line 275 "smt2newparser.yy"
        {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[-1].tok));
        }
#line 2477 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 33: /* command: '(' TK_EXIT ')'  */
#line 279 "smt2newparser.yy"
        { (yyval.snode) = new ASTNode(CMD_T, (yyvsp[-1].tok)); }
#line 2483 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 34: /* command: '(' TK_ECHO TK_STR ')'  */
#line 281 "smt2newparser.yy"
        {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[-2].tok));
            (yyval.snode)->children = new std::vector<ASTNode*>();
            (yyval.snode)->children->push_back(new ASTNode(UATTR_T, (yyvsp[-1].str)));
        }
#line 2493 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 35: /* attribute_list: %empty  */
#line 289 "smt2newparser.yy"
        { (yyval.snode_list) = new std::vector<ASTNode*>(); }
#line 2499 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 36: /* attribute_list: attribute_list attribute  */
#line 291 "smt2newparser.yy"
        { (yyvsp[-1].snode_list)->push_back((yyvsp[0].snode)); (yyval.snode_list) = (yyvsp[-1].snode_list); }
#line 2505 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 37: /* attribute: TK_KEY  */
#line 295 "smt2newparser.yy"
        { (yyval.snode) = new ASTNode(UATTR_T, (yyvsp[0].str)); }
#line 2511 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 38: /* attribute: TK_KEY attribute_value  */
#line 297 "smt2newparser.yy"
        { (yyval.snode) = new ASTNode(UATTR_T, (yyvsp[-1].str)); (yyval.snode)->children = new std::vector<ASTNode*>(); (yyval.snode)->children->push_back((yyvsp[0].snode)); }
#line 2517 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 39: /* attribute: predef_key  */
#line 299 "smt2newparser.yy"
        { (yyval.snode) = new ASTNode(PATTR_T, (yyvsp[0].str)); }
#line 2523 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 40: /* attribute: predef_key attribute_value  */
#line 301 "smt2newparser.yy"
        { (yyval.snode) = new ASTNode(PATTR_T, (yyvsp[-1].str)); (yyval.snode)->children = new std::vector<ASTNode*>(); (yyval.snode)->children->push_back((yyvsp[0].snode)); }
#line 2529 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 41: /* attribute_value: spec_const  */
#line 305 "smt2newparser.yy"
        { (yyval.snode) = new ASTNode(SPECC_T, NULL); (yyval.snode)->children = new std::vector<ASTNode*>(); (yyval.snode)->children->push_back((yyvsp[0].snode)); }
#line 2535 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 42: /* attribute_value: symbol  */
#line 307 "smt2newparser.yy"
        {
            (yyval.snode) = (yyvsp[0].snode);
        }
#line 2543 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 43: /* attribute_value: '(' s_expr_list ')'  */
#line 311 "smt2newparser.yy"
        {
            (yyval.snode) = new ASTNode(SEXPRL_T, NULL);
            (yyval.snode)->children = (yyvsp[-1].snode_list);
        }
#line 2552 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 44: /* identifier: symbol  */
#line 318 "smt2newparser.yy"
        { (yyval.snode) = (yyvsp[0].snode); }
#line 2558 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 45: /* identifier: '(' '_' symbol numeral_list ')'  */
#line 320 "smt2newparser.yy"
        { (yyval.snode) = (yyvsp[-2].snode); (yyval.snode)->children = (yyvsp[-1].snode_list); }
#line 2564 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 46: /* sort: identifier  */
#line 324 "smt2newparser.yy"
      { (yyval.snode) = (yyvsp[0].snode); }
#line 2570 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 47: /* sort: '(' identifier sort sort_list ')'  */
#line 326 "smt2newparser.yy"
      {
        (yyval.snode) = new ASTNode(LID_T, NULL);
        (yyval.snode)->children = (yyvsp[-1].snode_list);
        (yyval.snode)->children->insert((yyval.snode)->children->begin(), (yyvsp[-2].snode));
        (yyval.snode)->children->insert((yyval.snode)->children->begin(), (yyvsp[-3].snode));
      }
#line 2581 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 48: /* sort_list: sort_list sort  */
#line 335 "smt2newparser.yy"
        { (yyvsp[-1].snode_list)->push_back((yyvsp[0].snode)); (yyval.snode_list) = (yyvsp[-1].snode_list); }
#line 2587 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 49: /* sort_list: %empty  */
#line 337 "smt2newparser.yy"
        { (yyval.snode_list) = new std::vector<ASTNode*>(); }
#line 2593 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 50: /* s_expr: spec_const  */
#line 341 "smt2newparser.yy"
        {
            (yyval.snode) = new ASTNode(SPECC_T, NULL);
            (yyval.snode)->children = new std::vector<ASTNode*>();
            (yyval.snode)->children->push_back((yyvsp[0].snode));
        }
#line 2603 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 51: /* s_expr: symbol  */
#line 347 "smt2newparser.yy"
        {
            (yyval.snode) = (yyvsp[0].snode);
        }
#line 2611 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 52: /* s_expr: TK_KEY  */
#line 351 "smt2newparser.yy"
        {
            (yyval.snode) = new ASTNode(UATTR_T, (yyvsp[0].str));
        }
#line 2619 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 53: /* s_expr: '(' s_expr_list ')'  */
#line 355 "smt2newparser.yy"
        {
            (yyval.snode) = new ASTNode(SEXPRL_T, NULL);
            (yyval.snode)->children = (yyvsp[-1].snode_list);
        }
#line 2628 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 54: /* s_expr_list: %empty  */
#line 362 "smt2newparser.yy"
        {
            (yyval.snode_list) = new std::vector<ASTNode*>();
        }
#line 2636 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 55: /* s_expr_list: s_expr_list s_expr  */
#line 366 "smt2newparser.yy"
        {
            (yyvsp[-1].snode_list)->push_back((yyvsp[0].snode));
            (yyval.snode_list) = (yyvsp[-1].snode_list);
        }
#line 2645 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 56: /* spec_const: TK_NUM  */
#line 374 "smt2newparser.yy"
        { (yyval.snode) = new ASTNode(NUM_T, (yyvsp[0].str)); }
#line 2651 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 57: /* spec_const: TK_DEC  */
#line 376 "smt2newparser.yy"
        { (yyval.snode) = new ASTNode(DEC_T, (yyvsp[0].str)); }
#line 2657 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 58: /* spec_const: TK_HEX  */
#line 378 "smt2newparser.yy"
        { (yyval.snode) = new ASTNode(HEX_T, (yyvsp[0].str)); }
#line 2663 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 59: /* spec_const: TK_BIN  */
#line 380 "smt2newparser.yy"
        { (yyval.snode) = new ASTNode(BIN_T, (yyvsp[0].str)); }
#line 2669 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 60: /* spec_const: TK_STR  */
#line 382 "smt2newparser.yy"
        { (yyval.snode) = new ASTNode(STR_T, (yyvsp[0].str)); }
#line 2675 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 61: /* const_val: symbol  */
#line 386 "smt2newparser.yy"
        { (yyval.snode) = (yyvsp[0].snode); }
#line 2681 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 62: /* const_val: spec_const  */
#line 388 "smt2newparser.yy"
        { (yyval.snode) = (yyvsp[0].snode); }
#line 2687 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 63: /* numeral_list: numeral_list TK_NUM  */
#line 392 "smt2newparser.yy"
        { (yyvsp[-1].snode_list)->push_back(new ASTNode(NUM_T, (yyvsp[0].str))); (yyval.snode_list) = (yyvsp[-1].snode_list); }
#line 2693 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 64: /* numeral_list: TK_NUM  */
#line 394 "smt2newparser.yy"
        { (yyval.snode_list) = new std::vector<ASTNode*>(); (yyval.snode_list)->push_back(new ASTNode(NUM_T, (yyvsp[0].str))); }
#line 2699 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 65: /* qual_identifier: identifier  */
#line 398 "smt2newparser.yy"
        { (yyval.snode) = (yyvsp[0].snode); }
#line 2705 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 66: /* qual_identifier: '(' TK_AS identifier sort ')'  */
#line 400 "smt2newparser.yy"
        {
            (yyval.snode) = new ASTNode(AS_T, NULL);
            (yyval.snode)->children = new std::vector<ASTNode*>();
            (yyval.snode)->children->push_back((yyvsp[-2].snode));
            (yyval.snode)->children->push_back((yyvsp[-1].snode));
        }
#line 2716 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 67: /* var_binding_list: %empty  */
#line 409 "smt2newparser.yy"
        { (yyval.snode_list) = new std::vector<ASTNode*>(); }
#line 2722 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 68: /* var_binding_list: var_binding_list var_binding  */
#line 411 "smt2newparser.yy"
        { (yyvsp[-1].snode_list)->push_back((yyvsp[0].snode)); (yyval.snode_list) = (yyvsp[-1].snode_list); }
#line 2728 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 69: /* var_binding: '(' symbol term ')'  */
#line 415 "smt2newparser.yy"
        { (yyval.snode) = new ASTNode(VARB_T, strdup((yyvsp[-2].snode)->getValue())); delete (yyvsp[-2].snode); (yyval.snode)->children = new std::vector<ASTNode*>(); (yyval.snode)->children->push_back((yyvsp[-1].snode)); }
#line 2734 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 70: /* sorted_var_list: %empty  */
#line 419 "smt2newparser.yy"
        { (yyval.snode_list) = new std::vector<ASTNode*>(); }
#line 2740 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 71: /* sorted_var_list: sorted_var_list sorted_var  */
#line 421 "smt2newparser.yy"
        { (yyvsp[-1].snode_list)->push_back((yyvsp[0].snode)); (yyval.snode_list) = (yyvsp[-1].snode_list); }
#line 2746 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 72: /* sorted_var: '(' symbol sort ')'  */
#line 425 "smt2newparser.yy"
        { (yyval.snode) = new ASTNode(SV_T, strdup((yyvsp[-2].snode)->getValue())); delete (yyvsp[-2].snode); (yyval.snode)->children = new std::vector<ASTNode*>(); (yyval.snode)->children->push_back((yyvsp[-1].snode)); }
#line 2752 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 73: /* term_list: %empty  */
#line 428 "smt2newparser.yy"
        { (yyval.snode_list) = new std::vector<ASTNode*>(); }
#line 2758 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 74: /* term_list: term_list term  */
#line 430 "smt2newparser.yy"
        { (yyvsp[-1].snode_list)->push_back((yyvsp[0].snode)); (yyval.snode_list) = (yyvsp[-1].snode_list); }
#line 2764 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 75: /* term: spec_const  */
#line 434 "smt2newparser.yy"
        { (yyval.snode) = new ASTNode(TERM_T, NULL); (yyval.snode)->children = new std::vector<ASTNode*>(); (yyval.snode)->children->push_back((yyvsp[0].snode)); }
#line 2770 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 76: /* term: qual_identifier  */
#line 436 "smt2newparser.yy"
        { (yyval.snode) = new ASTNode(QID_T, NULL); (yyval.snode)->children = new std::vector<ASTNode*>(); (yyval.snode)->children->push_back((yyvsp[0].snode)); }
#line 2776 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 77: /* term: '(' qual_identifier term term_list ')'  */
#line 438 "smt2newparser.yy"
        {
            (yyval.snode) = new ASTNode(LQID_T, NULL);
            (yyval.snode)->children = (yyvsp[-1].snode_list);
            (yyval.snode)->children->insert((yyval.snode)->children->begin(), (yyvsp[-2].snode));
            (yyval.snode)->children->insert((yyval.snode)->children->begin(), (yyvsp[-3].snode));
        }
#line 2787 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 78: /* term: '(' TK_LET '(' var_binding var_binding_list ')' term ')'  */
#line 445 "smt2newparser.yy"
        {
            (yyval.snode) = new ASTNode(LET_T, NULL);
            (yyval.snode)->children = new std::vector<ASTNode*>();
            (yyvsp[-3].snode_list)->insert((yyvsp[-3].snode_list)->begin(), (yyvsp[-4].snode));
            ASTNode* vbl = new ASTNode(VARBL_T, NULL);
            vbl->children = (yyvsp[-3].snode_list);
            (yyval.snode)->children->push_back(vbl);
            (yyval.snode)->children->push_back((yyvsp[-1].snode));
        }
#line 2801 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 79: /* term: '(' TK_FORALL '(' sorted_var sorted_var_list ')' term ')'  */
#line 455 "smt2newparser.yy"
        {
            (yyval.snode) = new ASTNode(FORALL_T, NULL);
            (yyval.snode)->children = new std::vector<ASTNode*>();
            (yyvsp[-3].snode_list)->insert((yyvsp[-3].snode_list)->begin(), (yyvsp[-4].snode));
            ASTNode* svl = new ASTNode(SVL_T, NULL);
            svl->children = (yyvsp[-3].snode_list);
            (yyval.snode)->children->push_back(svl);
            (yyval.snode)->children->push_back((yyvsp[-1].snode));
        }
#line 2815 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 80: /* term: '(' TK_EXISTS '(' sorted_var sorted_var_list ')' term ')'  */
#line 465 "smt2newparser.yy"
        {
            (yyval.snode) = new ASTNode(EXISTS_T, NULL);
            (yyval.snode)->children = new std::vector<ASTNode*>();
            (yyvsp[-3].snode_list)->insert((yyvsp[-3].snode_list)->begin(), (yyvsp[-4].snode));
            ASTNode* svl = new ASTNode(SVL_T, NULL);
            svl->children = (yyvsp[-3].snode_list);
            (yyval.snode)->children->push_back(svl);
            (yyval.snode)->children->push_back((yyvsp[-1].snode));
        }
#line 2829 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 81: /* term: '(' '!' term attribute attribute_list ')'  */
#line 475 "smt2newparser.yy"
        {
            (yyval.snode) = new ASTNode(BANG_T, NULL);
            (yyval.snode)->children = new std::vector<ASTNode*>();
            (yyval.snode)->children->push_back((yyvsp[-3].snode));
            ASTNode *atrs = new ASTNode(GATTRL_T, NULL);
            (yyvsp[-1].snode_list)->insert((yyvsp[-1].snode_list)->begin(), (yyvsp[-2].snode));
            atrs->children = (yyvsp[-1].snode_list);
            (yyval.snode)->children->push_back(atrs);
        }
#line 2843 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 82: /* symbol_list: %empty  */
#line 487 "smt2newparser.yy"
        { (yyval.snode_list) = new std::vector<ASTNode*>(); }
#line 2849 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 83: /* symbol_list: symbol_list symbol  */
#line 489 "smt2newparser.yy"
        { (yyvsp[-1].snode_list)->push_back((yyvsp[0].snode)); (yyval.snode_list) = (yyvsp[-1].snode_list); }
#line 2855 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 84: /* b_value: symbol  */
#line 493 "smt2newparser.yy"
        {
            const char * str = (yyvsp[0].snode)->getValue();
            if (strcmp(str, "true") == 0 or strcmp(str, "false") == 0) {
                (yyval.snode) = new ASTNode(BOOL_T, strdup((yyvsp[0].snode)->getValue())); delete (yyvsp[0].snode);
            }
            else {
                printf("Syntax error: expecting either 'true' or 'false', got '%s'\n", str);
                delete (yyvsp[0].snode);
                YYERROR;
            }
        }
#line 2871 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 85: /* option: KW_PRINTSUCCESS b_value  */
#line 507 "smt2newparser.yy"
        {
            (yyval.snode) = new ASTNode(OPTION_T, (yyvsp[-1].str));
            (yyval.snode)->children = new std::vector<ASTNode*>();
            (yyval.snode)->children->push_back((yyvsp[0].snode));
        }
#line 2881 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 86: /* option: KW_EXPANDDEFINITIONS b_value  */
#line 513 "smt2newparser.yy"
        {
            (yyval.snode) = new ASTNode(OPTION_T, (yyvsp[-1].str));
            (yyval.snode)->children = new std::vector<ASTNode*>();
            (yyval.snode)->children->push_back((yyvsp[0].snode));
        }
#line 2891 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 87: /* option: KW_INTERACTIVEMODE b_value  */
#line 519 "smt2newparser.yy"
        {
            (yyval.snode) = new ASTNode(OPTION_T, (yyvsp[-1].str));
            (yyval.snode)->children = new std::vector<ASTNode*>();
            (yyval.snode)->children->push_back((yyvsp[0].snode));
        }
#line 2901 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 88: /* option: KW_PRODUCEPROOFS b_value  */
#line 525 "smt2newparser.yy"
        {
            (yyval.snode) = new ASTNode(OPTION_T, (yyvsp[-1].str));
            (yyval.snode)->children = new std::vector<ASTNode*>();
            (yyval.snode)->children->push_back((yyvsp[0].snode));
        }
#line 2911 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 89: /* option: KW_PRODUCEUNSATCORES b_value  */
#line 531 "smt2newparser.yy"
        {
            (yyval.snode) = new ASTNode(OPTION_T, (yyvsp[-1].str));
            (yyval.snode)->children = new std::vector<ASTNode*>();
            (yyval.snode)->children->push_back((yyvsp[0].snode));
        }
#line 2921 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 90: /* option: KW_PRODUCEMODELS b_value  */
#line 537 "smt2newparser.yy"
        {
            (yyval.snode) = new ASTNode(OPTION_T, (yyvsp[-1].str));
            (yyval.snode)->children = new std::vector<ASTNode*>();
            (yyval.snode)->children->push_back((yyvsp[0].snode));
        }
#line 2931 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 91: /* option: KW_PRODUCEASSIGNMENTS b_value  */
#line 543 "smt2newparser.yy"
        {
            (yyval.snode) = new ASTNode(OPTION_T, (yyvsp[-1].str));
            (yyval.snode)->children = new std::vector<ASTNode*>();
            (yyval.snode)->children->push_back((yyvsp[0].snode));
        }
#line 2941 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 92: /* option: KW_REGULAROUTPUTCHANNEL TK_STR  */
#line 549 "smt2newparser.yy"
        {
            (yyval.snode) = new ASTNode(OPTION_T, (yyvsp[-1].str));
            (yyval.snode)->children = new std::vector<ASTNode*>();
            (yyval.snode)->children->push_back(new ASTNode(STR_T, (yyvsp[0].str)));
        }
#line 2951 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 93: /* option: KW_DIAGNOSTICOUTPUTCHANNEL TK_STR  */
#line 555 "smt2newparser.yy"
        {
            (yyval.snode) = new ASTNode(OPTION_T, (yyvsp[-1].str));
            (yyval.snode)->children = new std::vector<ASTNode*>();
            (yyval.snode)->children->push_back(new ASTNode(STR_T, (yyvsp[0].str)));
        }
#line 2961 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 94: /* option: KW_RANDOMSEED TK_NUM  */
#line 561 "smt2newparser.yy"
        {
            (yyval.snode) = new ASTNode(OPTION_T, (yyvsp[-1].str));
            (yyval.snode)->children = new std::vector<ASTNode*>();
            (yyval.snode)->children->push_back(new ASTNode(NUM_T, (yyvsp[0].str)));
        }
#line 2971 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 95: /* option: KW_VERBOSITY TK_NUM  */
#line 567 "smt2newparser.yy"
        {
            (yyval.snode) = new ASTNode(OPTION_T, (yyvsp[-1].str));
            (yyval.snode)->children = new std::vector<ASTNode*>();
            (yyval.snode)->children->push_back(new ASTNode(NUM_T, (yyvsp[0].str)));
        }
#line 2981 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 96: /* option: attribute  */
#line 573 "smt2newparser.yy"
        {
            (yyval.snode) = new ASTNode(OPTION_T, NULL);
            (yyval.snode)->children = new std::vector<ASTNode*>();
            (yyval.snode)->children->push_back((yyvsp[0].snode));
        }
#line 2991 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 97: /* predef_key: KW_SORTS  */
#line 581 "smt2newparser.yy"
        { (yyval.str) = (yyvsp[0].str); }
#line 2997 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 98: /* predef_key: KW_FUNS  */
#line 583 "smt2newparser.yy"
        { (yyval.str) = (yyvsp[0].str); }
#line 3003 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 99: /* predef_key: KW_SORTSDESCRIPTION  */
#line 585 "smt2newparser.yy"
        { (yyval.str) = (yyvsp[0].str); }
#line 3009 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 100: /* predef_key: KW_FUNSDESCRIPTION  */
#line 587 "smt2newparser.yy"
        { (yyval.str) = (yyvsp[0].str); }
#line 3015 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 101: /* predef_key: KW_DEFINITION  */
#line 589 "smt2newparser.yy"
        { (yyval.str) = (yyvsp[0].str); }
#line 3021 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 102: /* predef_key: KW_VALUES  */
#line 591 "smt2newparser.yy"
        { (yyval.str) = (yyvsp[0].str); }
#line 3027 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 103: /* predef_key: KW_NOTES  */
#line 593 "smt2newparser.yy"
        { (yyval.str) = (yyvsp[0].str); }
#line 3033 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 104: /* predef_key: KW_THEORIES  */
#line 595 "smt2newparser.yy"
        { (yyval.str) = (yyvsp[0].str); }
#line 3039 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 105: /* predef_key: KW_EXTENSIONS  */
#line 597 "smt2newparser.yy"
        { (yyval.str) = (yyvsp[0].str); }
#line 3045 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 106: /* predef_key: KW_PRINTSUCCESS  */
#line 599 "smt2newparser.yy"
        { (yyval.str) = (yyvsp[0].str); }
#line 3051 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 107: /* predef_key: KW_EXPANDDEFINITIONS  */
#line 601 "smt2newparser.yy"
        { (yyval.str) = (yyvsp[0].str); }
#line 3057 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 108: /* predef_key: KW_INTERACTIVEMODE  */
#line 603 "smt2newparser.yy"
        { (yyval.str) = (yyvsp[0].str); }
#line 3063 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 109: /* predef_key: KW_PRODUCEPROOFS  */
#line 605 "smt2newparser.yy"
        { (yyval.str) = (yyvsp[0].str); }
#line 3069 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 110: /* predef_key: KW_PRODUCEUNSATCORES  */
#line 607 "smt2newparser.yy"
        { (yyval.str) = (yyvsp[0].str); }
#line 3075 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 111: /* predef_key: KW_PRODUCEMODELS  */
#line 609 "smt2newparser.yy"
        { (yyval.str) = (yyvsp[0].str); }
#line 3081 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 112: /* predef_key: KW_PRODUCEASSIGNMENTS  */
#line 611 "smt2newparser.yy"
        { (yyval.str) = (yyvsp[0].str); }
#line 3087 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 113: /* predef_key: KW_REGULAROUTPUTCHANNEL  */
#line 613 "smt2newparser.yy"
        { (yyval.str) = (yyvsp[0].str); }
#line 3093 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 114: /* predef_key: KW_DIAGNOSTICOUTPUTCHANNEL  */
#line 615 "smt2newparser.yy"
        { (yyval.str) = (yyvsp[0].str); }
#line 3099 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 115: /* predef_key: KW_RANDOMSEED  */
#line 617 "smt2newparser.yy"
        { (yyval.str) = (yyvsp[0].str); }
#line 3105 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 116: /* predef_key: KW_VERBOSITY  */
#line 619 "smt2newparser.yy"
        { (yyval.str) = (yyvsp[0].str); }
#line 3111 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 117: /* predef_key: KW_ERRORBEHAVIOR  */
#line 621 "smt2newparser.yy"
        { (yyval.str) = (yyvsp[0].str); }
#line 3117 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 118: /* predef_key: KW_NAME  */
#line 623 "smt2newparser.yy"
        { (yyval.str) = (yyvsp[0].str); }
#line 3123 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 119: /* predef_key: KW_NAMED  */
#line 625 "smt2newparser.yy"
        { (yyval.str) = (yyvsp[0].str); }
#line 3129 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 120: /* predef_key: KW_AUTHORS  */
#line 627 "smt2newparser.yy"
        { (yyval.str) = (yyvsp[0].str); }
#line 3135 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 121: /* predef_key: KW_VERSION  */
#line 629 "smt2newparser.yy"
        { (yyval.str) = (yyvsp[0].str); }
#line 3141 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 122: /* predef_key: KW_STATUS  */
#line 631 "smt2newparser.yy"
        { (yyval.str) = (yyvsp[0].str); }
#line 3147 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 123: /* predef_key: KW_REASONUNKNOWN  */
#line 633 "smt2newparser.yy"
        { (yyval.str) = (yyvsp[0].str); }
#line 3153 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 124: /* predef_key: KW_ALLSTATISTICS  */
#line 635 "smt2newparser.yy"
        { (yyval.str) = (yyvsp[0].str); }
#line 3159 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 125: /* info_flag: KW_ERRORBEHAVIOR  */
#line 639 "smt2newparser.yy"
        { (yyval.snode) = new ASTNode(INFO_T, (yyvsp[0].str)); }
#line 3165 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 126: /* info_flag: KW_NAME  */
#line 641 "smt2newparser.yy"
        { (yyval.snode) = new ASTNode(INFO_T, (yyvsp[0].str)); }
#line 3171 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 127: /* info_flag: KW_AUTHORS  */
#line 643 "smt2newparser.yy"
        { (yyval.snode) = new ASTNode(INFO_T, (yyvsp[0].str)); }
#line 3177 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 128: /* info_flag: KW_VERSION  */
#line 645 "smt2newparser.yy"
        { (yyval.snode) = new ASTNode(INFO_T, (yyvsp[0].str)); }
#line 3183 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 129: /* info_flag: KW_STATUS  */
#line 647 "smt2newparser.yy"
        { (yyval.snode) = new ASTNode(INFO_T, (yyvsp[0].str)); }
#line 3189 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 130: /* info_flag: KW_REASONUNKNOWN  */
#line 649 "smt2newparser.yy"
        { (yyval.snode) = new ASTNode(INFO_T, (yyvsp[0].str)); }
#line 3195 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 131: /* info_flag: KW_ALLSTATISTICS  */
#line 651 "smt2newparser.yy"
        { (yyval.snode) = new ASTNode(INFO_T, (yyvsp[0].str)); }
#line 3201 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;

  case 132: /* info_flag: TK_KEY  */
#line 653 "smt2newparser.yy"
        {
            (yyval.snode) = new ASTNode(INFO_T, NULL);
            (yyval.snode)->children = new std::vector<ASTNode*>();
            (yyval.snode)->children->push_back(new ASTNode(GATTR_T, (yyvsp[0].str)));
        }
#line 3211 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"
    break;


#line 3215 "/home/mambo/golem/cmake-build-release/_deps/opensmt-build/src/parsers/smt2new/smt2newparser.cc"

      default: break;
    }
  /* User semantic actions sometimes alter yychar, and that requires
     that yytoken be updated with the new translation.  We take the
     approach of translating immediately before every use of yytoken.
     One alternative is translating here after every semantic action,
     but that translation would be missed if the semantic action invokes
     YYABORT, YYACCEPT, or YYERROR immediately after altering yychar or
     if it invokes YYBACKUP.  In the case of YYABORT or YYACCEPT, an
     incorrect destructor might then be invoked immediately.  In the
     case of YYERROR or YYBACKUP, subsequent parser actions might lead
     to an incorrect destructor call or verbose syntax error message
     before the lookahead is translated.  */
  YY_SYMBOL_PRINT ("-> $$ =", YY_CAST (yysymbol_kind_t, yyr1[yyn]), &yyval, &yyloc);

  YYPOPSTACK (yylen);
  yylen = 0;

  *++yyvsp = yyval;
  *++yylsp = yyloc;

  /* Now 'shift' the result of the reduction.  Determine what state
     that goes to, based on the state we popped back to and the rule
     number reduced by.  */
  {
    const int yylhs = yyr1[yyn] - YYNTOKENS;
    const int yyi = yypgoto[yylhs] + *yyssp;
    yystate = (0 <= yyi && yyi <= YYLAST && yycheck[yyi] == *yyssp
               ? yytable[yyi]
               : yydefgoto[yylhs]);
  }

  goto yynewstate;


/*--------------------------------------.
| yyerrlab -- here on detecting error.  |
`--------------------------------------*/
yyerrlab:
  /* Make sure we have latest lookahead translation.  See comments at
     user semantic actions for why this is necessary.  */
  yytoken = yychar == YYEMPTY ? YYSYMBOL_YYEMPTY : YYTRANSLATE (yychar);
  /* If not already recovering from an error, report this error.  */
  if (!yyerrstatus)
    {
      ++yynerrs;
      {
        yypcontext_t yyctx
          = {yyssp, yytoken, &yylloc};
        char const *yymsgp = YY_("syntax error");
        int yysyntax_error_status;
        yysyntax_error_status = yysyntax_error (&yymsg_alloc, &yymsg, &yyctx);
        if (yysyntax_error_status == 0)
          yymsgp = yymsg;
        else if (yysyntax_error_status == -1)
          {
            if (yymsg != yymsgbuf)
              YYSTACK_FREE (yymsg);
            yymsg = YY_CAST (char *,
                             YYSTACK_ALLOC (YY_CAST (YYSIZE_T, yymsg_alloc)));
            if (yymsg)
              {
                yysyntax_error_status
                  = yysyntax_error (&yymsg_alloc, &yymsg, &yyctx);
                yymsgp = yymsg;
              }
            else
              {
                yymsg = yymsgbuf;
                yymsg_alloc = sizeof yymsgbuf;
                yysyntax_error_status = YYENOMEM;
              }
          }
        yyerror (&yylloc, context, yymsgp);
        if (yysyntax_error_status == YYENOMEM)
          YYNOMEM;
      }
    }

  yyerror_range[1] = yylloc;
  if (yyerrstatus == 3)
    {
      /* If just tried and failed to reuse lookahead token after an
         error, discard it.  */

      if (yychar <= YYEOF)
        {
          /* Return failure if at end of input.  */
          if (yychar == YYEOF)
            YYABORT;
        }
      else
        {
          yydestruct ("Error: discarding",
                      yytoken, &yylval, &yylloc, context);
          yychar = YYEMPTY;
        }
    }

  /* Else will try to reuse lookahead token after shifting the error
     token.  */
  goto yyerrlab1;


/*---------------------------------------------------.
| yyerrorlab -- error raised explicitly by YYERROR.  |
`---------------------------------------------------*/
yyerrorlab:
  /* Pacify compilers when the user code never invokes YYERROR and the
     label yyerrorlab therefore never appears in user code.  */
  if (0)
    YYERROR;
  ++yynerrs;

  /* Do not reclaim the symbols of the rule whose action triggered
     this YYERROR.  */
  YYPOPSTACK (yylen);
  yylen = 0;
  YY_STACK_PRINT (yyss, yyssp);
  yystate = *yyssp;
  goto yyerrlab1;


/*-------------------------------------------------------------.
| yyerrlab1 -- common code for both syntax error and YYERROR.  |
`-------------------------------------------------------------*/
yyerrlab1:
  yyerrstatus = 3;      /* Each real token shifted decrements this.  */

  /* Pop stack until we find a state that shifts the error token.  */
  for (;;)
    {
      yyn = yypact[yystate];
      if (!yypact_value_is_default (yyn))
        {
          yyn += YYSYMBOL_YYerror;
          if (0 <= yyn && yyn <= YYLAST && yycheck[yyn] == YYSYMBOL_YYerror)
            {
              yyn = yytable[yyn];
              if (0 < yyn)
                break;
            }
        }

      /* Pop the current state because it cannot handle the error token.  */
      if (yyssp == yyss)
        YYABORT;

      yyerror_range[1] = *yylsp;
      yydestruct ("Error: popping",
                  YY_ACCESSING_SYMBOL (yystate), yyvsp, yylsp, context);
      YYPOPSTACK (1);
      yystate = *yyssp;
      YY_STACK_PRINT (yyss, yyssp);
    }

  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  *++yyvsp = yylval;
  YY_IGNORE_MAYBE_UNINITIALIZED_END

  yyerror_range[2] = yylloc;
  ++yylsp;
  YYLLOC_DEFAULT (*yylsp, yyerror_range, 2);

  /* Shift the error token.  */
  YY_SYMBOL_PRINT ("Shifting", YY_ACCESSING_SYMBOL (yyn), yyvsp, yylsp);

  yystate = yyn;
  goto yynewstate;


/*-------------------------------------.
| yyacceptlab -- YYACCEPT comes here.  |
`-------------------------------------*/
yyacceptlab:
  yyresult = 0;
  goto yyreturnlab;


/*-----------------------------------.
| yyabortlab -- YYABORT comes here.  |
`-----------------------------------*/
yyabortlab:
  yyresult = 1;
  goto yyreturnlab;


/*-----------------------------------------------------------.
| yyexhaustedlab -- YYNOMEM (memory exhaustion) comes here.  |
`-----------------------------------------------------------*/
yyexhaustedlab:
  yyerror (&yylloc, context, YY_("memory exhausted"));
  yyresult = 2;
  goto yyreturnlab;


/*----------------------------------------------------------.
| yyreturnlab -- parsing is finished, clean up and return.  |
`----------------------------------------------------------*/
yyreturnlab:
  if (yychar != YYEMPTY)
    {
      /* Make sure we have latest lookahead translation.  See comments at
         user semantic actions for why this is necessary.  */
      yytoken = YYTRANSLATE (yychar);
      yydestruct ("Cleanup: discarding lookahead",
                  yytoken, &yylval, &yylloc, context);
    }
  /* Do not reclaim the symbols of the rule whose action triggered
     this YYABORT or YYACCEPT.  */
  YYPOPSTACK (yylen);
  YY_STACK_PRINT (yyss, yyssp);
  while (yyssp != yyss)
    {
      yydestruct ("Cleanup: popping",
                  YY_ACCESSING_SYMBOL (+*yyssp), yyvsp, yylsp, context);
      YYPOPSTACK (1);
    }
#ifndef yyoverflow
  if (yyss != yyssa)
    YYSTACK_FREE (yyss);
#endif
  if (yymsg != yymsgbuf)
    YYSTACK_FREE (yymsg);
  return yyresult;
}

#line 660 "smt2newparser.yy"


//=======================================================================================
// Auxiliary Routines

