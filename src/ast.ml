open Sexpr

type id = string

type t = 
  | Id of id
  | Fun of id * t * t
  | App of t * t
  | Forall of id * t * t
  | Type

and theorem =
{
  id: id;
  theorem: t;
  proof: t;
}

and stmnt = 
| Let of id * t
| Theorem of theorem
| Expr of t

type prog = stmnt list

let stmnt_to_sexpr = function 
| Let (id, t) -> failwith ""
| Theorem theorem -> failwith ""
| Expr t -> failwith ""

let prog_to_sexpr prog = SList (List.map stmnt_to_sexpr prog)