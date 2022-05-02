%{
    open Lexing
    open Ast

    let get_pos_string p =
      string_of_int ( p.pos_lnum ) ^ ":"
      ^ string_of_int ( p.pos_cnum - p.pos_bol + 1 )

    let get_return_value p str =
      (get_pos_string p) ^ " " ^ str ^ "\n"
%}

%token TYPE

%token <string> ID

%token EQ

%token LEFT_PAREN RIGHT_PAREN

%token COLON
%token COMMA
%token EOF
%token SEMICOLON
%token PERIOD

%token LET IN
%token FUN ARROW

%token THEOREM PROOF FORALL

/* Precedence and Associativity */

%start lexer
%type <string option> lexer

%start startprog
%type <Ast.prog> startprog
%%

lexer:
  | tok = token { Some tok }
  | EOF { None }
;

token:
  | TYPE
    { get_return_value $startpos "Type" }
  | i = ID
    { get_return_value $startpos ("id " ^ i) }
  | EQ
    { get_return_value $startpos "=" }
  | LEFT_PAREN
    { get_return_value $startpos "(" }
  | RIGHT_PAREN
    { get_return_value $startpos ")" }
  | COLON
    { get_return_value $startpos ":" }
  | COMMA
    { get_return_value $startpos "," }
  | SEMICOLON
    { get_return_value $startpos ";" }
  | PERIOD
    { get_return_value $startpos "." }
  | LET
    { get_return_value $startpos "let" }
  | IN
    { get_return_value $startpos "in" }
  | FUN
    { get_return_value $startpos "lambda" }
  | ARROW
    { get_return_value $startpos "->" }
  | THEOREM
    { get_return_value $startpos "Theorem" }
  | PROOF
    { get_return_value $startpos "Proof" }  
  | FORALL
    { get_return_value $startpos "forall" }
;

startprog:
  | p = prog; EOF                           { p }
;

prog:
  | LET i=ID EQ t=term IN p = prog               { Let (i, t, p) }
  | THEOREM PERIOD i=ID COLON
    t1=term PERIOD PROOF PERIOD 
    t2=term PERIOD p=prog                        { Theorem ({id=i; theorem=t1; proof=t2}, p) }
  | t=term                                       { Expr t }

term:
  | LEFT_PAREN t=term RIGHT_PAREN                { t }
  | i=ID                                         { Id i }
  | FUN i=ID COLON t1=term ARROW t2=term            { Fun (i, t1, t2) }
  | t1=term t2=term                              { App (t1, t2) }
  | FORALL i=ID COLON t1=term COMMA t2=term      { Forall (i, t1, t2) }
  | TYPE                                         { Type }
