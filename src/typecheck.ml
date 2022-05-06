open Ast
open Util

exception MalformedType

type env = (id * t) list

(* get a fresh type variable *)
(* let fresh : unit -> t =
  let source = Fresh.make (HashSet.make()) in
  fun() -> Id (Fresh.next source) *)

(* type t = 
  | Id of id
  | Fun of id * t * t
  | App of t * t
  | Forall of id * t * t
  | Type *)
let rec subst_t var term sub = 
  match term with
  | Id x when x = var -> sub
  | Id x -> term
  | Fun (x, a, t) -> if x = var then term else
    Fun (x, (subst_t var a sub), (subst_t var t sub))
  | App (t1, t2) -> App ((subst_t var t1 sub), (subst_t var t2 sub))
  | Forall (x, a, t) when x = var -> term
  | Forall (x, a, t) -> Forall (x, (subst_t var a sub), (subst_t var t sub))
  | Type -> Type

let rec subst_prog var prog sub =
  match prog with 
  | Let (id, t, p) -> Let(id, subst_t var t sub, subst_prog var p sub)
  | Theorem (theorem, p) -> 
      begin 
        let theorem' = {
          id = theorem.id;
          theorem = subst_t var theorem.theorem sub;
          proof = subst_t var theorem.proof sub;
        } in 
        Theorem (theorem', subst_prog var p sub)
      end
  | Expr t -> Expr (subst_t var t sub)

let rec typecheck_t gamma t =
  match t with
  |Id x -> List.assoc x gamma
  |Fun (x, a, t) -> 
    let gamma' = (x, a)::(List.remove_assoc x gamma) in
    let t_type = typecheck_t gamma' t in
    begin 
    match typecheck_t gamma (Forall (x, a, t_type)) with
    |Type -> (Forall (x, a, t_type))
    |_ -> raise MalformedType
    end
  |App (t1, t2) -> 
    begin
    match typecheck_t gamma t1 with
    |Forall (x, a, b) -> 
      let t2_type = typecheck_t gamma t2 in 
       if t2_type = a then subst_t x b t2 
       else raise MalformedType
    |_ -> raise MalformedType
    end
  |Forall (x, a, b) -> 
    begin 
    match typecheck_t gamma a with
    |Type -> 
      let gamma' = (x, a)::(List.remove_assoc x gamma) in
      begin
        match typecheck_t gamma' b with
        |Type -> Type
        |_ -> raise MalformedType
      end
    |_ -> raise MalformedType
    end
  |Type -> Type

(* let *)

let rec typecheck_let gamma id t p =
  let t' = typecheck_t gamma t in
  let p_subst = subst_prog id p t' in 
  typecheck_prog gamma p_subst

and typecheck_prog gamma prog =
  match prog with 
  | Let (id, t, p) -> typecheck_let gamma id t p
  | Theorem (theorem, p) -> failwith "unimplemented"
  | Expr t -> typecheck_t gamma t