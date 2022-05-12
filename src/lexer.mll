{
  open Parser
  open Lexing 

  exception LexingError of Lexing.position * string

}

let new_line = '\n' | '\r''\n'

let var = ['a'-'z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' ''' '_']*
let str = ['"'] [^'"']* ['"']
let whitespace = [' ' '\t']

rule token = parse
|new_line         {Lexing.new_line lexbuf; token lexbuf}
|whitespace+      {token lexbuf}

|"Type"           {TYPE}

|"("              {LEFT_PAREN}
|")"              {RIGHT_PAREN}

|":"              {COLON}
|";"              {SEMICOLON}
|","              {COMMA}
|"."              {PERIOD}
|"="              {EQ}

|"let"            {LET}
|"in"             {IN}

|"Theorem"        {THEOREM}
|"Proof"          {PROOF}
|"forall"         {FORALL}

|"lambda"         {FUN}
|"->"             {ARROW}

|"(*"             { comment lexbuf }

|var              {ID (Lexing.lexeme lexbuf)}

|eof              {EOF}
| _               {raise (LexingError (lexbuf.lex_start_p, "unrecognized token"))}


and comment = parse
  | "*)" { token lexbuf }
  | eof
      { raise (LexingError (lexbuf.lex_start_p, "unclosed comment")) }
  | _ { comment lexbuf }
