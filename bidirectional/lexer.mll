{
open Parser
}

let white = [' ' '\t' '\n']+
let letter = ['a'-'z' 'A'-'Z']
let id = letter ['a'-'z' 'A'-'Z' '0'-'9' '_']*

rule read =
  parse
  | white     { read lexbuf }
  | "("       { LPAREN }
  | ")"       { RPAREN }
  | ":"       { COLON }
  | "."       { DOT }
  | "lam"     { LAMBDA }
  | "true"    { TRUE }
  | "false"   { FALSE }
  | "if"      { IF }
  | "then"    { THEN }
  | "else"    { ELSE }
  | "bool"    { BOOLTYPE }
  | "->"      { ARROW }
  | id        { ID (Lexing.lexeme lexbuf) }
  | eof       { EOF }