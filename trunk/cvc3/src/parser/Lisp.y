%{
/*****************************************************************************/
/*!
 * \file PL.y
 * 
 * Author: Mehul Trivedi
 * 
 * Created: Aug 08 01:45:43 GMT 2004
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
/* PL.y
   Mehul Trivedi, 8/14/04

   This file contains the bison code for the parser that reads in CVC
   commands in lisp language.
*/

#include "vc.h"
#include "parser_exception.h"
#include "parser_temp.h"

// Exported shared data
namespace CVC3 {
  extern ParserTemp* parserTemp;
}
// Define shortcuts for various things
#define TMP CVC3::parserTemp
#define EXPR CVC3::parserTemp->expr
#define VC (CVC3::parserTemp->vc)
#define RAT(args) CVC3::newRational args

// Suppress the bogus warning suppression in bison (it generates
// compile error)
#undef __GNUC_MINOR__

/* stuff that lives in Lisp.lex */
extern int Lisplex(void);

int Lisperror(const char *s)
{
  std::ostringstream ss;
  ss << CVC3::parserTemp->fileName << ":" << CVC3::parserTemp->lineNum
     << ": " << s;
  return CVC3::parserTemp->error(ss.str());
}

#define YYLTYPE_IS_TRIVIAL 1
#define YYMAXDEPTH 10485760

%}

%union {
  std::string *str;
  CVC3::Expr *node;
  std::vector<CVC3::Expr> *vec;
  int kind;
};


%start cmd

/* strings are for better error messages.  
   "_TOK" is so macros don't conflict with kind names */

%token  BINARY_TOK              "0b"
%token  HEX_TOK                 "0x"  
%token  DONE_TOK

%type <vec> Exprs 
%type <node> Identifier StringLiteral Numeral Binary Hex
%type <node> Expr

%token <str> ID_TOK STRINGLIT_TOK NUMERAL_TOK

/*%token DONE*/

%%

cmd             :	Expr
			{
			 EXPR = *$1;
			 delete $1;
			 YYACCEPT;
			}
		;

Expr            :       Identifier 		{ }
		|	StringLiteral 		{ }
		|	Numeral 		{ }
		|	Binary			{ }
		|	Hex			{ }
		|	'(' Exprs ')'		
			{
		  	$$ = new CVC3::Expr(VC->listExpr(*$2));
		  	delete $2;
                        }
		|	DONE_TOK
			{ 
			 TMP->done = true;
			 EXPR = CVC3::Expr();
			 YYACCEPT;
			}
		;

Identifier      :       ID_TOK
                        {
			  $$ = new CVC3::Expr(VC->idExpr(*$1));
			  delete $1;
			}
                ;
		
StringLiteral   :       STRINGLIT_TOK
                        {
			  $$ = new CVC3::Expr(VC->stringExpr(*$1));
			  delete $1;
			}
                ;
Numeral         :       NUMERAL_TOK
                        {
  			  $$ = new CVC3::Expr(VC->ratExpr((*$1)));
  			  delete $1;
			}
                ;

Binary          :       BINARY_TOK NUMERAL_TOK
                        {
			  $$ = new CVC3::Expr(VC->stringExpr(*$2));
			  delete $2;
                        }
                ;

Hex             :       HEX_TOK NUMERAL_TOK
                        {
			  $$ = new CVC3::Expr(VC->ratExpr(*$2, 16));
			  delete $2;
                        }
                ;


Exprs		:	{
			$$ = new std::vector<CVC3::Expr>;
			}
		|	Exprs Expr
			{
			$1->push_back(*$2);
			delete $2;
			}
		;
		
%%
