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

let rec t_to_sexpr = function
| Id id -> SNode id
| Fun (id, t1, t2) -> SList [SNode "Fun"; SNode id; t_to_sexpr t1; t_to_sexpr t2]
| App (t1, t2) -> SList [SNode "App"; t_to_sexpr t1; t_to_sexpr t2]
| Forall (id, t1, t2) -> SList [SNode "Forall"; SNode id; t_to_sexpr t1; t_to_sexpr t2]
| Type -> SNode "Type"

and theorem_to_sexpr theorem = 
  SList [SNode "Theorem"; SNode theorem.id; t_to_sexpr theorem.theorem; 
    SNode "Proof"; t_to_sexpr theorem.proof]

and stmnt_to_sexpr = function 
| Let (id, t) -> SList [SNode "Let"; SNode id; t_to_sexpr t]
| Theorem theorem -> theorem_to_sexpr theorem
| Expr t -> t_to_sexpr t

let prog_to_sexpr prog = SList (List.map stmnt_to_sexpr prog)