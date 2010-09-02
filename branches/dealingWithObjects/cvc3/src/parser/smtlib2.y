%{
/*****************************************************************************/
/*!
 * \file smtlib2.y
 * 
 * Author: Clark Barrett
 * 
 * Created: Apr 30 2005
 *
 * <hr>
 *
 * License to use, copy, modify, sell and/or distribute this software
 * and its documentation for any purpose is hereby granted without
 * royalty, subject to the terms and conditions defined in the \ref
 * LICENSE file provided with this distribution.
 * 
 * <hr>
 * 
 */
/*****************************************************************************/
/* 
   This file contains the bison code for the parser that reads in CVC
   commands in SMT-LIB language.
*/

#include "vc.h"
#include "parser_exception.h"
#include "parser_temp.h"
#include "translator.h"

// Exported shared data
namespace CVC3 {
  extern ParserTemp* parserTemp;
}
// Define shortcuts for various things
#define TMP CVC3::parserTemp
#define EXPR CVC3::parserTemp->expr
#define VC (CVC3::parserTemp->vc)
#define ARRAYSENABLED (CVC3::parserTemp->arrFlag)
#define BVENABLED (CVC3::parserTemp->bvFlag)
#define BVSIZE (CVC3::parserTemp->bvSize)
#define RAT(args) CVC3::newRational args
#define QUERYPARSED CVC3::parserTemp->queryParsed
#define TRANSLATOR CVC3::parserTemp->translator

// Suppress the bogus warning suppression in bison (it generates
// compile error)
#undef __GNUC_MINOR__

/* stuff that lives in smtlib2.lex */
extern int smtlib2lex(void);

int smtlib2error(const char *s)
{
  std::ostringstream ss;
  ss << CVC3::parserTemp->fileName << ":" << CVC3::parserTemp->lineNum
     << ": " << s;
  return CVC3::parserTemp->error(ss.str());
}

#define YYLTYPE_IS_TRIVIAL 1
#define YYMAXDEPTH 10485760

// static hash_map<std::string,std::string> *operators;

%}

%union {
  std::string *str;
  std::vector<std::string> *strvec;
  CVC3::Expr *node;
  std::vector<CVC3::Expr> *vec;
  std::pair<std::vector<CVC3::Expr>, std::vector<CVC3::Expr> > *pat_ann;
};


%start command

/* strings are for better error messages.  
   "_TOK" is so macros don't conflict with kind names */

%type <node> command command_aux non_keyword_sexpr sexpr term sort_symbol identifier binding sorted_var attribute
%type <vec> sexprs sort_symbols sort_symbols_nonempty terms bindings sorted_vars attributes numerals
%type <str> quantifier

%token <str> DECIMAL_TOK
%token <str> INTEGER_TOK
%token <str> HEX_TOK
%token <str> BINARY_TOK
%token <str> SYM_TOK
%token <str> KEYWORD_TOK
%token <str> STRING_TOK

%token ASSERT_TOK
%token CHECKSAT_TOK
%token DECLARE_FUN_TOK
%token DECLARE_SORT_TOK
%token EXCLAMATION_TOK
%token EXIT_TOK
%token ITE_TOK
%token LET_TOK
%token LPAREN_TOK
%token RPAREN_TOK
%token SET_LOGIC_TOK
%token SET_INFO_TOK
%token UNDERSCORE_TOK
%token EOF_TOK

// Logic symbols
/* %token AND_TOK */
/* %token AT_TOK */
/* %token DISTINCT_TOK */
/* %token DIV_TOK */
/* %token EQUAL_TOK */
%token EXISTS_TOK
/* %token FALSE_TOK */
%token FORALL_TOK
/* %token GREATER_THAN_TOK */
/* %token GREATER_THAN_EQ_TOK */
/* %token IFF_TOK */
/* %token IMPLIES_TOK */
/* %token LESS_THAN_TOK */
/* %token LESS_THAN_EQ_TOK */
/* %token MINUS_TOK */
/* %token NOT_TOK */
/* %token OR_TOK */
/* %token PERCENT_TOK */
/* %token PLUS_TOK */
/* %token POUND_TOK */
/* %token STAR_TOK */
/* %token TRUE_TOK */
/* %token XOR_TOK */

%%

command:
    LPAREN_TOK command_aux RPAREN_TOK
    {
      EXPR = *$2;
      delete $2;
      YYACCEPT;
    }
  | EOF_TOK
    { 
      TMP->done = true;
      EXPR = CVC3::Expr();
      YYACCEPT;
    }
;

command_aux:
    SET_LOGIC_TOK SYM_TOK
    {
      ARRAYSENABLED = false;
      BVENABLED = false;
      std::vector<CVC3::Expr> subCommands;

      /* Add the symbols of the core theory */
      subCommands.push_back( VC->listExpr("_TYPEDEF", VC->idExpr("Bool"),
                                          VC->idExpr("_BOOLEAN")) );
      subCommands.push_back( VC->listExpr("_CONST", VC->idExpr("true"),
                                          VC->idExpr("Bool"),
                                          VC->idExpr("_TRUE_EXPR")) );
      subCommands.push_back( VC->listExpr("_CONST", VC->idExpr("false"),
                                          VC->idExpr("Bool"),
                                          VC->idExpr("_FALSE_EXPR")) );

      if (*$2 == "QF_AX" ||
          *$2 == "QF_AUFLIA" ||
          *$2 == "AUFLIA" ||
          *$2 == "QF_AUFLIRA" ||
          *$2 == "AUFLIRA" ||
          *$2 == "QF_AUFNIRA" ||
          *$2 == "AUFNIRA" ||
          *$2 == "QF_AUFBV" ||
          *$2 == "QF_ABV") {
        ARRAYSENABLED = true;
      }

      if (*$2 == "QF_AUFBV" ||
          *$2 == "QF_ABV" ||
          *$2 == "QF_BV" ||
          *$2 == "QF_UFBV") {
        BVENABLED = true;
      }

      /* Add the Int type for logics that include it */
      if (*$2 == "AUFLIA" ||
          *$2 == "AUFLIRA" ||
          *$2 == "AUFNIRA" ||
          *$2 == "QF_AUFLIA" ||
          *$2 == "QF_IDL" ||
          *$2 == "QF_LIA" ||
          *$2 == "QF_NIA" ||
          *$2 == "QF_UFIDL" ||
          *$2 == "QF_UFLIA" ||
          *$2 == "UFNIA" ) {
        subCommands.push_back( VC->listExpr("_TYPEDEF", VC->idExpr("Int"),
                                            VC->idExpr("_INT")) );
      }

      /* Add the Real type for logics that include it */
      if (*$2 == "AUFLIRA" ||
          *$2 == "AUFNIRA" ||
          *$2 == "LRA" ||
          *$2 == "QF_RDL" ||
          *$2 == "QF_LRA" ||
          *$2 == "QF_NRA" ||
          *$2 == "QF_UFLRA" ||
          *$2 == "QF_UFNRA" ||
          *$2 == "UFLRA" ||
          *$2 == "QF_UFRDL" ) {
        subCommands.push_back( VC->listExpr("_TYPEDEF", VC->idExpr("Real"),
                                            VC->idExpr("_REAL")) );
      }

      /* Enable complete instantiation heuristics */
      if (*$2 == "AUFLIA" ||
          *$2 == "AUFLIRA" ||
          *$2 == "AUFNIRA" ||
          *$2 == "LRA" ||
          *$2 == "UFLRA" ||
          *$2 == "UFNIA") {
        subCommands.push_back( VC->listExpr("_OPTION", 
                                            VC->stringExpr("quant-complete-inst"), 
                                            VC->ratExpr(1)) );
      }

      $$ = new CVC3::Expr(VC->listExpr("_SEQ", subCommands));
      delete $2;
    }

  | SET_INFO_TOK KEYWORD_TOK sexpr
    {
      if(*$2 == ":status") {
        TRANSLATOR->setStatus((*$3)[0].getString());
      } else if(*$2 == ":source") {
        TRANSLATOR->setSource((*$3)[0].getString());
      } else if(*$2 == ":category") {
        TRANSLATOR->setCategory($3->getString());
      }
      // TRANSLATOR->setBenchName(*$3);
      delete $2;
      delete $3;
      $$ = new CVC3::Expr();
    }

  | DECLARE_SORT_TOK SYM_TOK INTEGER_TOK
    {
      $$ = new CVC3::Expr(VC->listExpr("_TYPE", VC->idExpr(*$2)));
      delete $2;
    }

  | DECLARE_FUN_TOK SYM_TOK LPAREN_TOK sort_symbols RPAREN_TOK sort_symbol
    {
      if ($4->size() == 0) {
        $$ = new CVC3::Expr(VC->listExpr("_CONST", VC->idExpr(*$2), (*$6)));
      }
      else {
        $4->push_back( *$6 );
        CVC3::Expr tmp(VC->listExpr("_ARROW", *$4));
        $$ = new CVC3::Expr(VC->listExpr("_CONST", VC->idExpr(*$2), tmp));
      }
      delete $2;
      delete $4;
      delete $6;
    }

  | ASSERT_TOK term
    {
      $$ = new CVC3::Expr(VC->listExpr("_ASSERT", *$2));
      delete $2;
    }

  | CHECKSAT_TOK
    {
      $$ = new CVC3::Expr(VC->listExpr("_CHECKSAT", 
                                       CVC3::Expr(VC->idExpr("_TRUE_EXPR"))));
    }

  | EXIT_TOK
    {
      TMP->done = true;
      $$ = new CVC3::Expr();
    }
;

sexprs:
    sexpr
    {
      $$ = new std::vector<CVC3::Expr>;
      $$->push_back(*$1);
      delete $1;
    }
  | sexprs sexpr
    { 
      $1->push_back(*$2);
      $$ = $1;
      delete $2;
    }
;


/* An S-expression that is not a keyword (NOTE: it may contain keywords
   in sub-expressions; it's just not *only* a keyword). */
non_keyword_sexpr:
    INTEGER_TOK
    { $$ = new CVC3::Expr(VC->ratExpr(*$1)); 
      delete $1; }
  | DECIMAL_TOK
    { $$ = new CVC3::Expr(VC->ratExpr(*$1)); 
      delete $1; }
  | STRING_TOK
    { $$ = new CVC3::Expr(VC->stringExpr(*$1)); 
      delete $1;}
  | SYM_TOK
    { $$ = new CVC3::Expr(VC->idExpr(*$1)); 
      delete $1;}
  | LPAREN_TOK sexprs RPAREN_TOK
    { $$ = new CVC3::Expr(VC->listExpr(*$2)); 
      delete $2; }
  ;

sexpr:
    non_keyword_sexpr
    {
      $$ = $1;
    }
  | KEYWORD_TOK
    { $$ = new CVC3::Expr(VC->idExpr(*$1)); 
      delete $1;}

/* Possibly empty list of sort symbols */
sort_symbols:
    /* empty */
    {
      $$ = new std::vector<CVC3::Expr>;
    }
  | sort_symbols_nonempty
    { 
      $$ = $1;
    }
;

sort_symbols_nonempty:
    sort_symbol
    {
      $$ = new std::vector<CVC3::Expr>;
      $$->push_back(*$1);
      delete $1;
    }
  | sort_symbols sort_symbol
    { 
      $1->push_back(*$2);
      $$ = $1;
      delete $2;
    }
;

sort_symbol:
    identifier
    { 
      CVC3::Expr id = *$1;
      if( BVENABLED &&
          id.isRawList() &&
          id[0].getKind() == CVC3::ID &&
          id[0][0].getString() == "BitVec" &&
          id.arity() == 2 &&
          id[1].isRational() ) {
        $$ = new CVC3::Expr( VC->listExpr("_BITVECTOR", id[1]) );
        delete $1;
      } else {
        $$ = $1;
      }
    }
  | LPAREN_TOK identifier sort_symbols_nonempty RPAREN_TOK
    {
      CVC3::Expr id = *$2;
      if (ARRAYSENABLED && 
          id.getKind() == CVC3::ID &&
          id[0].getString() == "Array" 
          && $3->size() == 2) {
        $$ = new CVC3::Expr( VC->listExpr("_ARRAY", *$3) );
      } else {
        // FIXME: How to handle non-array parameterized types?
        $3->insert( $3->begin(), *$2 );
        $$ = new CVC3::Expr( VC->listExpr(*$3) );
      }
      delete $2;
      delete $3;
    }
;

identifier:
    SYM_TOK
    {
      std::string id = *$1;
      /* If the id is a built-in operator, replace the text with the 
         internal name. 

         NOTE: the right way to do this would be would be with a 
         hash_map or trie.
      */
      if (id == "and") {
        id = "_AND";
      } else if (id == "distinct") {
        id = "_DISTINCT";
      } else if (id == "ite") {
        id = "_IF";
      } else if (id == "/") {
        id = "_DIVIDE";
      } else if (id == "=") {
        id = "_EQ";
      } else if (id == ">") {
        id = "_GT";
      } else if (id == ">=") {
        id = "_GE";
      } else if (id == "=>") {
        id = "_IMPLIES";
      } else if (id == "<") {
        id = "_LT";
      } else if (id == "<=") {
        id = "_LE";
      } else if (id == "-") {
        id = "_MINUS";
      } else if (id == "not") {
        id = "_NOT";
      } else if (id == "or") {
        id = "_OR";
      } else if (id == "+") {
        id = "_PLUS";
      } else if (id == "*") {
        id = "_MULT";
      } else if (id == "xor") {
        id = "_XOR";
      } else if (ARRAYSENABLED && id == "select") {
          id = "_READ";
      } else if (ARRAYSENABLED && id == "store") {
        id = "_WRITE";
      } else if (BVENABLED && id == "concat") {
        id = "_CONCAT";
      } else if (BVENABLED && id == "bvadd") {
        id = "_BVPLUS";
      } else if (BVENABLED && id == "bvand") {
        id = "_BVAND";
      } else if (BVENABLED && id == "bvashr") {
        id = "_BVASHR";
      } else if (BVENABLED && id == "bvcomp") {
        id = "_BVCOMP";
      } else if (BVENABLED && id == "bvlshr") {
        id = "_BVLSHR";
      } else if (BVENABLED && id == "bvmul") {
        id = "_BVMULT";
      } else if (BVENABLED && id == "bvneg") {
        id = "_BVUMINUS";
      } else if (BVENABLED && id == "bvnand") {
        id = "_BVNAND";
      } else if (BVENABLED && id == "bvnot") {
        id = "_BVNEG";
      } else if (BVENABLED && id == "bvnor") {
        id = "_BVNOR";
      } else if (BVENABLED && id == "bvor") {
        id = "_BVOR";
      } else if (BVENABLED && id == "bvshl") {
        id = "_BVSHL";
      } else if (BVENABLED && id == "bvsdiv") {
        id = "_BVSDIV";
      } else if (BVENABLED && id == "bvsge") {
        id = "_BVSGE";
      } else if (BVENABLED && id == "bvsgt") {
        id = "_BVSGT";
      } else if (BVENABLED && id == "bvsle") {
        id = "_BVSLE";
      } else if (BVENABLED && id == "bvslt") {
        id = "_BVSLT";
      } else if (BVENABLED && id == "bvsmod") {
        id = "_BVSMOD";
      } else if (BVENABLED && id == "bvsrem") {
        id = "_BVSREM";
      } else if (BVENABLED && id == "bvsub") {
        id = "_BVSUB";
      } else if (BVENABLED && id == "bvudiv") {
        id = "_BVUDIV";
      } else if (BVENABLED && id == "bvuge") {
        id = "_BVGE";
      } else if (BVENABLED && id == "bvugt") {
        id = "_BVGT";
      } else if (BVENABLED && id == "bvule") {
        id = "_BVLE";
      } else if (BVENABLED && id == "bvult") {
        id = "_BVLT";
      } else if (BVENABLED && id == "bvurem") {
        id = "_BVUREM";
      } else if (BVENABLED && id == "bvxnor") {
        id = "_BVXNOR";
      } else if (BVENABLED && id == "bvxor") {
        id = "_BVXOR";
      } 
      $$ = new CVC3::Expr( VC->idExpr( id ) );
      delete $1;
    }
  | LPAREN_TOK UNDERSCORE_TOK SYM_TOK numerals RPAREN_TOK
    {
      std::string id = *$3;
      std::vector<CVC3::Expr> numerals = *$4;
      if (BVENABLED &&
          id.size() > 2 &&
          id[0] == 'b' &&
          id[1] == 'v' &&
          numerals.size() == 1) {
        DebugAssert( numerals[0].isRational() &&
                     numerals[0].getRational().isInteger(),
                     "Illegal size argument to bit-vector constant." );
        $$ = new CVC3::Expr( VC->listExpr("_BVCONST",
                                          VC->ratExpr(id.substr(2), 10),
                                          (*$4)[0]) );
      } else {
        if (BVENABLED && id == "extract") {
          id = "_EXTRACT";
        } else if (BVENABLED && id == "repeat") {
          id = "_BVREPEAT";
        } else if (BVENABLED && id == "zero_extend") {
          id = "_BVZEROEXTEND";
        } else if (BVENABLED && id == "sign_extend") {
          id = "_SX";
        } else if (BVENABLED && id == "rotate_left") {
          id = "_BVROTL";
        } else if (BVENABLED && id == "rotate_right") {
          id = "_BVROTR";
        }
        $$ = new CVC3::Expr( VC->listExpr( id, *$4 ) );
      }
      delete $3;
      delete $4;
    }
;

/* a non-empty sequence of integers */
numerals:
    INTEGER_TOK
    {
      $$ = new std::vector<CVC3::Expr>;
      $$->push_back( VC->ratExpr(*$1) );
      delete $1;
    }
  | numerals INTEGER_TOK
    {
      $1->push_back( VC->ratExpr(*$2) );
      $$ = $1;
      delete $2;
    }
;

/* A non-empty sequence of terms. */
terms:
    term
    {
      $$ = new std::vector<CVC3::Expr>;
      $$->push_back(*$1);
      delete $1;
    }
  |
    terms term
    {
      $1->push_back(*$2);
      $$ = $1;
      delete $2;
    }
;

term:
    LPAREN_TOK identifier terms RPAREN_TOK
    {
      CVC3::Expr op = *$2;
      std::vector<CVC3::Expr> args = *$3;

      std::vector<CVC3::Expr> resultList;

      bool isId = op.getKind() == CVC3::ID;
      std::string opStr;
      if( isId ) {
        opStr = op[0].getString();
      }
      
      if( isId && opStr == "_MINUS" && args.size() == 1 ) {
        resultList.push_back( VC->idExpr("_UMINUS") );
        resultList.push_back( args[0] );
      } else if( isId &&
                 ( opStr == "_AND" ||
                   opStr == "_OR" ||
                   opStr == "_XOR" ||
                   opStr == "_PLUS" ||
                   opStr == "_MULT" ) &&
                 args.size() == 1 ) {
        smtlib2error("[bin,N]-ary operator used in unary context");
      } else {
        const int arity = op.arity();
        isId = arity > 0 && op[0].getKind() == CVC3::ID;
        if( isId ) {
          opStr = op[0][0].getString();
        }

        if( BVENABLED && arity == 3 && isId &&
            opStr == "_EXTRACT" &&
            op[1].isRational() &&
            op[1].getRational().isInteger() && 
            op[2].isRational() &&
            op[2].getRational().isInteger() ) {
          resultList.push_back( op[0] );
          resultList.push_back(op[1]);
          resultList.push_back(op[2]);
        } else if( BVENABLED && arity == 2 && isId && 
                   ( opStr == "_BVREPEAT" ||
                     opStr == "_BVZEROEXTEND" ||
                     opStr == "_BVROTL" ||
                     opStr == "_BVROTR" ||
                     opStr == "_SX" ) &&
                   op[1].isRational() &&
                   op[1].getRational().isInteger() ) {
          resultList.push_back( op[0] );
          if( opStr == "_SX" ) {
            resultList.push_back(VC->idExpr("_smtlib"));
          }
          resultList.push_back(op[1]);
        } else {
          resultList.push_back(op);
        } 

        resultList.insert( resultList.end(), args.begin(), args.end() );
      } 

      $$ = new CVC3::Expr(VC->listExpr(resultList));
      delete $2;
      delete $3;
    }

  | LPAREN_TOK LET_TOK LPAREN_TOK bindings RPAREN_TOK term RPAREN_TOK
    {
      CVC3::Expr e(VC->listExpr(*$4));
      $$ = new CVC3::Expr(VC->listExpr("_LET", e, *$6));
      delete $4;
      delete $6;
    }

  | LPAREN_TOK quantifier LPAREN_TOK sorted_vars RPAREN_TOK term RPAREN_TOK
    {
      CVC3::Expr e(VC->listExpr(*$4));
      CVC3::Expr body(*$6);
      DebugAssert( body.arity() > 0, "Empty quantifier body." );
      if( body[0].isString() && 
          body[0].getString() == "_ANNOT" ) {
        CVC3::Expr annots = body[2];
        body = body[1]; // real body, stripping annot wrapper
        std::vector<CVC3::Expr> patterns;
        for( int i = 0; i < annots.arity(); ++i ) {
          DebugAssert( annots[i].arity() == 2 &&
                       annots[i][0].getKind() == CVC3::ID,
                       "Illegal annotation." );
          if( annots[i][0][0].getString() == ":pattern" ) {
            patterns.push_back( annots[i][1] );
          }
        }
        $$ = new CVC3::Expr(VC->listExpr(*$2, e, body, VC->listExpr(patterns)));
      } else {
        $$ = new CVC3::Expr(VC->listExpr(*$2, e, body));
      }
      delete $2;
      delete $4;
      delete $6;
    }

  | LPAREN_TOK EXCLAMATION_TOK term attributes RPAREN_TOK
    {
      $$ = new CVC3::Expr(VC->listExpr(VC->stringExpr("_ANNOT"), 
                                       *$3, 
                                       VC->listExpr(*$4)));
      delete $3;
      delete $4;
    }

  | identifier
    {
      $$ = $1;
    }

  | DECIMAL_TOK
    {
      $$ = new CVC3::Expr(VC->ratExpr(*$1));
      delete $1;
    }

  | INTEGER_TOK
    {
      $$ = new CVC3::Expr(VC->ratExpr(*$1));
      delete $1;
    }

  | HEX_TOK
    {
      std::vector<CVC3::Expr> args;
      args.push_back(VC->idExpr("_BVCONST"));
      args.push_back(VC->ratExpr(*$1, 16));
      args.push_back(VC->ratExpr($1->length()));
      $$ = new CVC3::Expr(VC->listExpr(args));
      delete $1;
    }

  | BINARY_TOK
    {
      std::vector<CVC3::Expr> args;
      args.push_back(VC->idExpr("_BVCONST"));
      args.push_back(VC->ratExpr(*$1, 2));
      args.push_back(VC->ratExpr($1->length()));
      $$ = new CVC3::Expr(VC->listExpr(args));
      delete $1;
    }

;

/* builtin: */
/*     AND_TOK { $$ = new std::string("_AND"); } */
/*   | DIV_TOK { $$ = new std::string("_DIVIDE"); } */
/*   | DISTINCT_TOK { $$ = new std::string("_DISTINCT"); } */
/*   | EQUAL_TOK { $$ = new std::string("_EQ"); } */
/*   | GREATER_THAN_TOK { $$ = new std::string("_GT"); } */
/*   | GREATER_THAN_EQ_TOK { $$ = new std::string("_GE"); } */
/*   | IFF_TOK { $$ = new std::string("_IFF"); } */
/*   | IMPLIES_TOK { $$ = new std::string("_IMPLIES"); } */
/*   | ITE_TOK { $$ = new std::string("_IF"); } */
/*   | LESS_THAN_TOK { $$ = new std::string("_LT"); } */
/*   | LESS_THAN_EQ_TOK { $$ = new std::string("_LE"); } */
/*   | MINUS_TOK { $$ = new std::string("_MINUS"); } */
/*   | NOT_TOK { $$ = new std::string("_NOT"); } */
/*   | OR_TOK { $$ = new std::string("_OR"); } */
/*   | PLUS_TOK { $$ = new std::string("_PLUS"); } */
/*   | STAR_TOK { $$ = new std::string("_MULT"); }  */
/*   | XOR_TOK { $$ = new std::string("_XOR"); } */
/* ; */

/* Returns a vector containing the operator and its arguments. 
   This is necessary because of the behavior of certain parameterized
   operators (e.g., extract). */
/* op: */
/*     builtin */
/*     { */
/*       $$ = new std::vector<CVC3::Expr>; */
/*       $$->push_back( VC->idExpr(*$1) ); */
/*       delete $1; */
/*     } */
/*   | identifier */
/*     { */
/*       $$ = new std::vector<CVC3::Expr>; */
/*       CVC3::Expr id = *$1; */
/*       if( id.getKind() == CVC3::ID ) { */
/*         std::string fname = id[0].getString(); */
/*         if (ARRAYSENABLED && fname == "select") { */
/*           $$->push_back( VC->idExpr("_READ") ); */
/*         } else if (ARRAYSENABLED && fname == "store") { */
/*           $$->push_back( VC->idExpr("_WRITE") ); */
/*         } else if (BVENABLED && fname == "concat") { */
/*           $$->push_back( VC->idExpr("_CONCAT") ); */
/*         } else if (BVENABLED && fname == "bvadd") { */
/*           $$->push_back( VC->idExpr("_BVPLUS") ); */
/*         } else if (BVENABLED && fname == "bvand") { */
/*           $$->push_back( VC->idExpr("_BVAND") ); */
/*         } else if (BVENABLED && fname == "bvashr") { */
/*           $$->push_back( VC->idExpr("_BVASHR") ); */
/*         } else if (BVENABLED && fname == "bvcomp") { */
/*           $$->push_back( VC->idExpr("_BVCOMP") ); */
/*         } else if (BVENABLED && fname == "bvlshr") { */
/*           $$->push_back( VC->idExpr("_BVLSHR") ); */
/*         } else if (BVENABLED && fname == "bvmul") { */
/*           $$->push_back( VC->idExpr("_BVMULT") ); */
/*         } else if (BVENABLED && fname == "bvneg") { */
/*           $$->push_back( VC->idExpr("_BVUMINUS") ); */
/*         } else if (BVENABLED && fname == "bvnand") { */
/*           $$->push_back( VC->idExpr("_BVNAND") ); */
/*         } else if (BVENABLED && fname == "bvnot") { */
/*           $$->push_back( VC->idExpr("_BVNEG") ); */
/*         } else if (BVENABLED && fname == "bvnor") { */
/*           $$->push_back( VC->idExpr("_BVNOR") ); */
/*         } else if (BVENABLED && fname == "bvor") { */
/*           $$->push_back( VC->idExpr("_BVOR") ); */
/*         } else if (BVENABLED && fname == "bvshl") { */
/*           $$->push_back( VC->idExpr("_BVSHL") ); */
/*         } else if (BVENABLED && fname == "bvsdiv") { */
/*           $$->push_back( VC->idExpr("_BVSDIV") ); */
/*         } else if (BVENABLED && fname == "bvsge") { */
/*           $$->push_back( VC->idExpr("_BVSGE") ); */
/*         } else if (BVENABLED && fname == "bvsgt") { */
/*           $$->push_back( VC->idExpr("_BVSGT") ); */
/*         } else if (BVENABLED && fname == "bvsle") { */
/*           $$->push_back( VC->idExpr("_BVSLE") ); */
/*         } else if (BVENABLED && fname == "bvslt") { */
/*           $$->push_back( VC->idExpr("_BVSLT") ); */
/*         } else if (BVENABLED && fname == "bvsrem") { */
/*           $$->push_back( VC->idExpr("_BVSREM") ); */
/*         } else if (BVENABLED && fname == "bvsub") { */
/*           $$->push_back( VC->idExpr("_BVSUB") ); */
/*         } else if (BVENABLED && fname == "bvudiv") { */
/*           $$->push_back( VC->idExpr("_BVUDIV") ); */
/*         } else if (BVENABLED && fname == "bvuge") { */
/*           $$->push_back( VC->idExpr("_BVUGE") ); */
/*         } else if (BVENABLED && fname == "bvugt") { */
/*           $$->push_back( VC->idExpr("_BVUGT") ); */
/*         } else if (BVENABLED && fname == "bvule") { */
/*           $$->push_back( VC->idExpr("_BVULE") ); */
/*         } else if (BVENABLED && fname == "bvult") { */
/*           $$->push_back( VC->idExpr("_BVLT") ); */
/*         } else if (BVENABLED && fname == "bvurem") { */
/*           $$->push_back( VC->idExpr("_BVUREM") ); */
/*         } else if (BVENABLED && fname == "bvxnor") { */
/*           $$->push_back( VC->idExpr("_BVXNOR") ); */
/*         } else if (BVENABLED && fname == "bvxor") { */
/*           $$->push_back( VC->idExpr("_BVXOR") ); */
/*         } else { */
/*           $$->push_back( id ); */
/*         } */
/*       } else if( BVENABLED &&  */
/*                  id.arity() > 0 && */
/*                  id[0].getKind() == CVC3::ID ) { */
/*         if( id.arity() == 3 && */
/*             id[0][0].getString() == "extract" && */
/*             id[1].isRational() && */
/*             id[1].getRational().isInteger() &&  */
/*             id[2].isRational() && */
/*             id[2].getRational().isInteger() ) { */
/*           $$->push_back( VC->idExpr("_EXTRACT") ); */
/*           $$->push_back(id[1]); */
/*           $$->push_back(id[2]); */
/*         } else if( id.arity() == 2 && */
/*                    id[0][0].getString() == "repeat" && */
/*                    id[1].isRational() && */
/*                    id[1].getRational().isInteger() ) { */
/*           $$->push_back( VC->idExpr("_BVREPEAT") ); */
/*           $$->push_back(id[1]); */
/*         } else if( id.arity() == 2 && */
/*                    id[0][0].getString() == "zero_extend" && */
/*                    id[1].isRational() && */
/*                    id[1].getRational().isInteger() ) { */
/*           $$->push_back( VC->idExpr("_BVZEROEXTEND") ); */
/*           $$->push_back(id[1]); */
/*         } else if( id.arity() == 2 && */
/*                    id[0][0].getString() == "sign_extend" && */
/*                    id[1].isRational() && */
/*                    id[1].getRational().isInteger() ) { */
/*           $$->push_back( VC->idExpr("_SX") ); */
/*           $$->push_back(VC->idExpr("_smtlib")); */
/*           $$->push_back(id[1]); */
/*         } else if( id.arity() == 2 && */
/*                    id[0].getKind() == CVC3::ID && */
/*                    id[0][0].getString() == "rotate_left" && */
/*                    id[1].isRational() && */
/*                    id[1].getRational().isInteger() ) { */
/*           $$->push_back( VC->idExpr("_BVROTL") ); */
/*           $$->push_back(id[1]); */
/*         } else if( id.arity() == 2 && */
/*                    id[0].getKind() == CVC3::ID && */
/*                    id[0][0].getString() == "rotate_right" && */
/*                    id[1].isRational() && */
/*                    id[1].getRational().isInteger() ) { */
/*           $$->push_back( VC->idExpr("_BVROTR") ); */
/*           $$->push_back(id[1]); */
/*         } else { */
/*           $$->push_back(id); */
/*         }  */
/*       } else { */
/*         $$->push_back(id); */
/*       } */
/*       delete $1; */
/*     } */
/* ; */

quantifier:
    EXISTS_TOK
    {
      $$ = new std::string("_EXISTS");
    }
  | FORALL_TOK
    {
      $$ = new std::string("_FORALL");
    }
;


/* A non-empty sequence of (var term) bindings */
bindings:
    binding
    { 
      $$ = new std::vector<CVC3::Expr>;
      $$->push_back(*$1);
      delete $1; 
    }
  | bindings binding 
    {
      $1->push_back(*$2);
      $$ = $1;
      delete $2;
    }
;      

binding:
    LPAREN_TOK SYM_TOK term RPAREN_TOK
    { $$ = new CVC3::Expr( VC->listExpr(*$2, *$3) );
      delete $2;
      delete $3; }
;

/* A non-empty sequence of (var sort) decls */
sorted_vars:
    sorted_var
    {
      $$ = new std::vector<CVC3::Expr>;
      $$->push_back(*$1);
      delete $1;
    }
  | sorted_vars sorted_var
    {
      $1->push_back(*$2);
      $$ = $1; 
      delete $2;
    }
;

sorted_var: 
    LPAREN_TOK SYM_TOK sort_symbol RPAREN_TOK
    {
      $$ = new CVC3::Expr(VC->listExpr(*$2, *$3));
      delete $2;
      delete $3;
    }
;

/* A non-empty sequence of attributes */
attributes:
    attribute
    {
      $$ = new std::vector<CVC3::Expr>;
      $$->push_back( *$1 );
      delete $1;
    }
  | attributes attribute
    {
      $1->push_back( *$2 );
      $$ = $1;
      delete $2;
    }
;

attribute:
    KEYWORD_TOK
    {
      $$ = new CVC3::Expr( VC->idExpr(*$1) );
      delete $1;
    }

  | KEYWORD_TOK non_keyword_sexpr
    {
      $$ = new CVC3::Expr( VC->listExpr( VC->idExpr(*$1), *$2 ) );
      delete $1;
      delete $2;
    }
;
%%
