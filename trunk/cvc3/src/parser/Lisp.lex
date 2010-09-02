%{
/*****************************************************************************/
/*!
 * \file Lisp.lex
 * 
 * Author: Sergey Berezin
 * 
 * Created: Feb 06 03:00:43 GMT 2003
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
#include "expr_manager.h" /* for the benefit of parseLisp_defs.h */
#include "parseLisp_defs.h"
#include "debug.h"
 
namespace CVC3 {
  extern ParserTemp* parserTemp;
}

extern int Lisp_inputLine;
extern char *Lisptext;

extern int Lisperror (const char *msg);

static int Lispinput(std::istream& is, char* buf, int size) {
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
    if(res == size) Lisperror("Lexer bug: overfilled the buffer");
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
  result = Lispinput(*CVC3::parserTemp->is, buf, max_size);

int Lisp_bufSize() { return YY_BUF_SIZE; }
YY_BUFFER_STATE Lisp_buf_state() { return YY_CURRENT_BUFFER; }

/* some wrappers for methods that need to refer to a struct.
   These are used by CVC3::Parser. */
void *Lisp_createBuffer(int sz) {
  return (void *)Lisp_create_buffer(NULL, sz);
}
void Lisp_deleteBuffer(void *buf_state) {
  Lisp_delete_buffer((struct yy_buffer_state *)buf_state);
}
void Lisp_switchToBuffer(void *buf_state) {
  Lisp_switch_to_buffer((struct yy_buffer_state *)buf_state);
}
void *Lisp_bufState() {
  return (void *)Lisp_buf_state();
}

void Lisp_setInteractive(bool is_interactive) {
  yy_set_interactive(is_interactive);
}

// File-static (local to this file) variables and functions
static std::string _string_lit;

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

LETTER	([a-zA-Z])
DIGIT	([0-9])
OPCHAR	(['!#?\_$\|])
ANYTHING ({LETTER}|{DIGIT}|{OPCHAR})

%%

[\n]            { CVC3::parserTemp->lineNum++; }
[ \t\r\f]	{ /* skip whitespace */ }

{DIGIT}+	{ Lisplval.str = new std::string(Lisptext); return NUMERAL_TOK; 
		}

";"		{ BEGIN COMMENT; }
<COMMENT>"\n"	{ BEGIN INITIAL; /* return to normal mode */ 
                  CVC3::parserTemp->lineNum++; }
<COMMENT>.	{ /* stay in comment mode */ }

<INITIAL>"\""		{ BEGIN STRING_LITERAL; 
                          _string_lit.erase(_string_lit.begin(),
                                            _string_lit.end()); }
<STRING_LITERAL>"\\".	{ /* escape characters (like \n or \") */
                          _string_lit.insert(_string_lit.end(),
                                             escapeChar(Lisptext[1])); }
<STRING_LITERAL>"\""	{ BEGIN INITIAL; /* return to normal mode */ 
			  Lisplval.str = new std::string(_string_lit);
                          return STRINGLIT_TOK; }
<STRING_LITERAL>.	{ _string_lit.insert(_string_lit.end(),*Lisptext); }

[().]	        { return Lisptext[0]; }

"0b"            { return BINARY_TOK;}
"0x"            { return HEX_TOK;}
".."            { Lisplval.str = new std::string("DOTDOT"); 	return ID_TOK; 	}
":="		{ Lisplval.str = new std::string("ASSIGN"); 	return ID_TOK; 	}
"=" 		{ Lisplval.str = new std::string("EQ"); 	return ID_TOK; 	}
"/="		{ Lisplval.str = new std::string("NEQ"); 	return ID_TOK; 	}
"=>"		{ Lisplval.str = new std::string("IMPLIES"); 	return ID_TOK; 	}	
"<=>"		{ Lisplval.str = new std::string("IFF"); 	return ID_TOK; 	}
"+"		{ Lisplval.str = new std::string("PLUS"); 	return ID_TOK; 	}
"-"		{ Lisplval.str = new std::string("MINUS"); 	return ID_TOK; 	}
"*"		{ Lisplval.str = new std::string("MULT"); 	return ID_TOK; 	}
"^"		{ Lisplval.str = new std::string("POW"); 	return ID_TOK; 	}
"/"		{ Lisplval.str = new std::string("DIV"); 	return ID_TOK; 	}
"MOD"		{ Lisplval.str = new std::string("MOD"); 	return ID_TOK; 	}
"<"		{ Lisplval.str = new std::string("LT"); 	return ID_TOK; 	}
"<="		{ Lisplval.str = new std::string("LE"); 	return ID_TOK; 	}
">="		{ Lisplval.str = new std::string("GE"); 	return ID_TOK; 	}
">"		{ Lisplval.str = new std::string("GT"); 	return ID_TOK; 	}

({ANYTHING})+	{ Lisplval.str = new std::string(Lisptext);	return ID_TOK;	}

<<EOF>>                                 { return DONE_TOK; }

. { Lisperror("Illegal input character."); }
%%

