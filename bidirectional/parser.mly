%{
    open Ast
%}

%token <string> ID
%token LPAREN
%token RPAREN
%token LAMBDA
%token TRUE
%token FALSE
%token IF
%token THEN
%token ELSE
%token DOT
%token COLON
%token BOOLTYPE
%token ARROW
%token EOF

%right ARROW

%start <Ast.term> main
%start <Ast.texpr> maintype

%%

main:
  | t = term; EOF { trans t }
  ;

maintype:
  | t = texpr; EOF { t }
  ;

term:
  | e = ID                                          { PVar(e)          }
  | TRUE                                            { PCstTrue         }
  | FALSE                                           { PCstFalse        }
  | LPAREN; t = term; COLON; ty = texpr; RPAREN     { PTDecl(t,ty)     }
  | IF; t1 = term; THEN; t2 = term; ELSE; t3 = term { PITE(t1, t2, t3) }
  | LAMBDA; x = ID; DOT; t = term                   { PAbs(x,t)        }
  | LPAREN; t1 = term; t2 = term; RPAREN            { PApp(t1,t2)      }
  | LPAREN; t = term; RPAREN                        { t                }
  ;

texpr:
  | BOOLTYPE                      { BoolType         }
  | t1 = texpr; ARROW; t2 = texpr { FuncType(t1, t2) }
  | LPAREN; t = texpr; RPAREN     { t                }
  ;
