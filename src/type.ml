open Ast

type env = id * id


let typecheck_t = function 
| Id id -> failwith "unimplemented"
| Fun (id, t1, t2) -> failwith "unimplemented"
| App (t1, t2) -> failwith "unimplemented"
| Forall (id, t1, t2) -> failwith "unimplemented"
| Type -> failwith "unimplemented"

let typecheck_prog = function 
| Let (id, t, p) -> failwith "unimplemented"
| Theorem (theorem, p) -> failwith "unimplemented"
| Expr t -> failwith "unimplemented"
