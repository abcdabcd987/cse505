{

open Lexing
open Printf
open ZUtil
open ImpParser

(* originally adapted from:
 * https://github.com/ztatlock/pec
 *
 * but error handling and string literals from:
 * https://realworldocaml.org/v1/en/html/parsing-with-ocamllex-and-menhir.html
 *)

exception SyntaxError of string

let set_fname lexbuf path =
  lexbuf.lex_curr_p <-
    { lexbuf.lex_curr_p with pos_fname = path }

let next_line lexbuf =
  let pos = lexbuf.lex_curr_p in
  lexbuf.lex_curr_p <-
    { pos with pos_bol = lexbuf.lex_curr_pos
             ; pos_lnum = pos.pos_lnum + 1 }

let print_lexpos outx lexbuf =
  let pos = lexbuf.lex_curr_p in
  fprintf outx "%s:%d:%d"
    pos.pos_fname
    pos.pos_lnum
    (pos.pos_cnum - pos.pos_bol + 1)

}

let id =
  ['a'-'z''A'-'Z''_']['a'-'z''A'-'Z''0'-'9''_']*

let intlit =
  "0" | ['1'-'9']['0'-'9']*

let comment =
  "#"[^'\n']*

let white =
  [' ' '\t']+

let line =
  '\r' | '\n' | "\r\n"

rule token = parse
  (* literals *)
  | "True"  { TRUE  }
  | "False" { FALSE }
  | intlit as x { INTLIT (Big.of_string x) }
  | '"' { read_string (Buffer.create 17) lexbuf }

  (* operators *)
  | "len" { LEN  }
  | "not" { NOT  }
  | "+"   { ADD  }
  | "-"   { SUB  }
  | "*"   { MUL  }
  | "/"   { DIV  }
  | "%"   { MOD  }
  | "=="  { EQ   }
  | "<"   { LT   }
  | "<="  { LE   }
  | "and" { CONJ }
  | "or"  { DISJ }

  (* statements *)
  | "nop"    { NOP    }
  | "="      { ASSIGN }
  | "alloc"  { ALLOC  }
  | ";"      { SEMI   }
  | "if"     { IF     }
  | "else"   { ELSE   }
  | "while"  { WHILE  }
  | "def"    { DEF    }
  | "return" { RET    }

  (* misc *)
  | "," { COMMA   }
  | "(" { LPAREN  }
  | ")" { RPAREN  }
  | "{" { LCURL   }
  | "}" { RCURL   }
  | "[" { LSQUARE }
  | "]" { RSQUARE }
  | eof { EOF     }

  (* variables *)
  | id as x { ID x }

  (* ignore *)
  | comment { token lexbuf }
  | white   { token lexbuf }
  | line    { next_line lexbuf; token lexbuf }

  (* error *)
  | _ as c
    { raise (SyntaxError (mkstr "Unexpected char: %c" c)) }

and read_string buf = parse
  | '"'       { STRLIT (Buffer.contents buf) }
  | '\\' '"'  { Buffer.add_char buf '"'    ; read_string buf lexbuf }
  | '\\' '\\' { Buffer.add_char buf '\\'   ; read_string buf lexbuf }
  | '\\' 'b'  { Buffer.add_char buf '\b'   ; read_string buf lexbuf }
  | '\\' 'f'  { Buffer.add_char buf '\012' ; read_string buf lexbuf }
  | '\\' 'n'  { Buffer.add_char buf '\n'   ; read_string buf lexbuf }
  | '\\' 'r'  { Buffer.add_char buf '\r'   ; read_string buf lexbuf }
  | '\\' 't'  { Buffer.add_char buf '\t'   ; read_string buf lexbuf }
  | [^ '"' '\\']+
    { Buffer.add_string buf (Lexing.lexeme lexbuf);
      read_string buf lexbuf
    }
  | _ as c
    { raise (SyntaxError (mkstr "Illegal string character: %c" c)) }
  | eof
    { raise (SyntaxError ("Unterminated string literal")) }
