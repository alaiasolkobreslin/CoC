open Ast
open Util

exception MalformedType
exception InvalidApplication
exception NotFound of string

type env = (id * t) list

let lookup gamma id =
  match List.assoc_opt id gamma with 
  | Some t -> t
  | None -> raise (NotFound id)

let ins_env gamma id t = (id, t)::(List.remove_assoc id gamma)

(* get a fresh type variable *)
(* let fresh : unit -> t =
  let source = Fresh.make (HashSet.make()) in
  fun() -> Id (Fresh.next source) *)


(** [subst_t var term sub] substitutes all instances of [var] in [term] with 
    [sub] and returns the resulting term *)
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

(** [subst_prog var prog sub] substitutes all instances of [var] in [prog]
    with [sub] and returns the resulting program *)
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

(** [typecheck_t gamma t] typechecks term [t] under context [gamma] and 
    returns the result *)
let rec typecheck_t gamma t =
  match t with
  |Id x -> lookup gamma x
  |Fun (x, a, t) -> 
    let gamma' = ins_env gamma x a in
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
      let gamma' = ins_env gamma x a in
      begin
        match typecheck_t gamma' b with
        |Type -> Type
        |_ -> raise MalformedType
      end
    |_ -> raise MalformedType
    end
  |Type -> Type

(** [typecheck_let gamma id t p] typechecks [t] and then substitues it for [id]
    in program [p] and returns the resulting program *)
let rec typecheck_let gamma id t p =
  let t' = typecheck_t gamma t in
  let p_subst = subst_prog id p t' in 
  typecheck_prog gamma p_subst

and typecheck_theorem gamma theorem p =
  failwith "unimplemented"

(** [typecheck_prog gamma prog] typechecks [prog] and returns the result *)
and typecheck_prog gamma prog =
  match prog with 
  | Let (id, t, p) -> typecheck_let gamma id t p
  | Theorem (theorem, p) -> typecheck_theorem gamma theorem p
  | Expr t -> typecheck_t gamma t

let rec beta_reduce t1 t2 =
  match t1 with 
  | Fun (id, l, r)
  | Forall (id, l, r) -> failwith "unimplemented"
  | _ -> raise InvalidApplication

let rec alpha_equiv gamma t1 t2 =
  match (t1, t2) with 
  | (Type, Type) -> true
  | (Id id1, Id id2) -> lookup gamma id1 = lookup gamma id2
  | (Fun (id1, l1, r1), Fun (id2, l2, r2))
  | (Forall (id1, l1, r1), Forall (id2, l2, r2)) ->
      if not (fv r2 |> List.exists (fun e -> e = id1)) then 
      begin
        let r2' = subst_t id2 r2 (Id id1) in
        let gamma' = ins_env gamma id1 l1 in
        (alpha_equiv gamma l1 l2) && (alpha_equiv gamma' r1 r2')
      end else
      if not (fv r1 |> List.exists (fun e -> e = id2)) then
      begin
        let r1' = subst_t id1 r1 (Id id2) in
        let gamma' = ins_env gamma id2 l2 in
        (alpha_equiv gamma l1 l2) && (alpha_equiv gamma' r1' r2)
      end else false
  | (App (l1, r1), App (l2, r2)) ->
      (alpha_equiv gamma l1 l2) && (alpha_equiv gamma r1 r2)
  | _ -> false