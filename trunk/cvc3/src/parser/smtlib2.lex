%{
/*****************************************************************************/
/*!
 * \file smtlib2.lex
 * 
 * Author: Christopher Conway
 * 
 * Created: 2010
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

#include <iostream>
#include "parser_temp.h"
#include "expr_manager.h" /* for the benefit of parsesmtlib_defs.h */
#include "parsesmtlib2_defs.h"
#include "debug.h"

namespace CVC3 {
  extern ParserTemp* parserTemp;
}

extern int smtlib2_inputLine;
extern char *smtlib2text;

extern int smtlib2error (const char *msg);

static int smtlib2input(std::istream& is, char* buf, int size) {
  int res;
  if(is) {
    // If interactive, read line by line; otherwise read as much as we
    // can gobble
    if(CVC3::parserTemp->interactive) {
      // Print the current prompt
      std::cout << CVC3::parserTemp->getPrompt() << std::flush;
      // Set the prompt to "middle of the command" one
      CVC3::parserTemp->setPrompt2();
      // Read the line
      is.getline(buf, size-1);
    } else // Set the terminator char to 0
      is.getline(buf, size-1, 0);
    // If failbit is set, but eof is not, it means the line simply
    // didn't fit; so we clear the state and keep on reading.
    bool partialStr = is.fail() && !is.eof();
    if(partialStr)
      is.clear();

    for(res = 0; res<size && buf[res] != 0; res++);
    if(res == size) smtlib2error("Lexer bug: overfilled the buffer");
    if(!partialStr) { // Insert \n into the buffer
      buf[res++] = '\n';
      buf[res] = '\0';
    }
  } else {
    res = YY_NULL;
  }
  return res;
}

// Redefine the input buffer function to read from an istream
#define YY_INPUT(buf,result,max_size) \
  result = smtlib2input(*CVC3::parserTemp->is, buf, max_size);

int smtlib2_bufSize() { return YY_BUF_SIZE; }
YY_BUFFER_STATE smtlib2_buf_state() { return YY_CURRENT_BUFFER; }

/* some wrappers for methods that need to refer to a struct.
   These are used by CVC3::Parser. */
void *smtlib2_createBuffer(int sz) {
  return (void *)smtlib2_create_buffer(NULL, sz);
}
void smtlib2_deleteBuffer(void *buf_state) {
  smtlib2_delete_buffer((struct yy_buffer_state *)buf_state);
}
void smtlib2_switchToBuffer(void *buf_state) {
  smtlib2_switch_to_buffer((struct yy_buffer_state *)buf_state);
}
void *smtlib2_bufState() {
  return (void *)smtlib2_buf_state();
}

void smtlib2_setInteractive(bool is_interactive) {
  yy_set_interactive(is_interactive);
}

// File-static (local to this file) variables and functions
static std::string _string_lit;
static std::string _symbol_text;

 static char escapeChar(char c) {
   switch(c) {
   case 'n': return '\n';
   case 't': return '\t';
   default: return c;
   }
 }

// for now, we don't have subranges.  
//
// ".."		{ return DOTDOT_TOK; }
/*OPCHAR	(['!#?\_$&\|\\@])*/

%}

%option noyywrap
%option nounput
%option noreject
%option noyymore
%option yylineno

%x	COMMENT
%x	STRING_LITERAL
%x	SYMBOL
%x      USER_VALUE
%s      PAT_MODE

LETTER	([a-zA-Z])
DIGIT	([0-9])
HEX_DIGIT ({DIGIT}|[a-fA-F])
BIN_DIGIT ([01])
SYMBOL_CHAR ([+\-*/=%?!.$_~&^<>@])
SIMPLE_SYMBOL (({LETTER}|{SYMBOL_CHAR})({LETTER}|{DIGIT}|{SYMBOL_CHAR})*)

%%

[\n]            { CVC3::parserTemp->lineNum++; }
[ \t\r\f]	{ /* skip whitespace */ }

{DIGIT}+"\."{DIGIT}+ { smtlib2lval.str = new std::string(smtlib2text); return DECIMAL_TOK; }
{DIGIT}+ { smtlib2lval.str = new std::string(smtlib2text); return INTEGER_TOK; }
"#x"{HEX_DIGIT}+ { /* skip prefix in string value */ smtlib2lval.str = new std::string(smtlib2text+2); return HEX_TOK; }
"#b"{BIN_DIGIT}+ { /* skip prefix in string value */ smtlib2lval.str = new std::string(smtlib2text+2); return BINARY_TOK; }

";"		{ BEGIN COMMENT; }
<COMMENT>"\n"	{ BEGIN INITIAL; /* return to normal mode */ 
                  CVC3::parserTemp->lineNum++; }
<COMMENT>.	{ /* stay in comment mode */ }

<INITIAL>"\""		{ BEGIN STRING_LITERAL; 
                          _string_lit.erase(_string_lit.begin(),
                                            _string_lit.end()); }
<STRING_LITERAL>"\\".	{ /* escape characters (like \n or \") */
                          _string_lit.insert(_string_lit.end(),
                                             escapeChar(smtlib2text[1])); }
<STRING_LITERAL>"\""	{ BEGIN INITIAL; /* return to normal mode */ 
			  smtlib2lval.str = new std::string(_string_lit);
                          return STRING_TOK; }
<STRING_LITERAL>"\n"	{ // Include the \n and increment the line number
                          _string_lit.insert(_string_lit.end(),*smtlib2text); 
                          CVC3::parserTemp->lineNum++; }
<STRING_LITERAL>.	{ _string_lit.insert(_string_lit.end(),*smtlib2text); }

<INITIAL>"|"            { BEGIN SYMBOL;
                          _symbol_text.erase(_symbol_text.begin(),
                                            _symbol_text.end()); }
<SYMBOL>"|"     	{ BEGIN INITIAL; /* return to normal mode */ 
			  smtlib2lval.str = new std::string(_symbol_text);
                          return SYM_TOK; }
<SYMBOL>"\n"            { // Include the \n and increment the line number
                          _symbol_text.insert(_symbol_text.end(),*smtlib2text);
                          CVC3::parserTemp->lineNum++; }
<SYMBOL>.       	{ _symbol_text.insert(_symbol_text.end(),*smtlib2text); }


             /* Base SMT-LIB tokens */
"assert"        { return ASSERT_TOK; }
"check-sat"     { return CHECKSAT_TOK; }
"declare-fun"   { return DECLARE_FUN_TOK; }
"declare-sort"  { return DECLARE_SORT_TOK; }
"!"             { return EXCLAMATION_TOK; }
"exit"          { return EXIT_TOK; }
"let"           { return LET_TOK; }
"("             { return LPAREN_TOK; }
")"             { return RPAREN_TOK; }
"set-logic"     { return SET_LOGIC_TOK; }
"set-info"      { return SET_INFO_TOK; }
"_"             { return UNDERSCORE_TOK; }

             /* Logic symbols */
"exists"        { return EXISTS_TOK; }
"forall"        { return FORALL_TOK; }

{SIMPLE_SYMBOL} { smtlib2lval.str = new std::string(smtlib2text); return SYM_TOK; }

":"{SIMPLE_SYMBOL} { smtlib2lval.str = new std::string(smtlib2text); return KEYWORD_TOK; }

<<EOF>>         { return EOF_TOK; }

. { smtlib2error("Illegal input character."); }
%%

