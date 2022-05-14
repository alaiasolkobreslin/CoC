open Ast
open Util

exception MalformedType of string
exception InvalidApplication
exception InvalidContext of string
exception NotFound of string

let lookup (gamma: (id*t) list) id =
  match List.assoc_opt id gamma with 
  | Some t -> t
  | None -> raise (NotFound id)

let ins_env env id t = (id, t)::(List.remove_assoc id env)

(** [lookup_conext gamma id curr] returns the most recent binding of [id]
    in [gamma] which is passed as [curr] and raises [InvalidContext] if
    the end of the context is reached and [curr] is [None] *)
let rec lookup_context gamma id curr =
  (* print_endline "here in lookup context"; *)
  match (gamma, curr) with 
  | (Type, None) -> raise (NotFound id)
  | (Type, Some v) -> v
  | (Forall (id', t1, t2), _) when id' = id -> lookup_context t2 id (Some t1)
  | (Forall (id', t1, t2), _) -> lookup_context t2 id curr
  | _ -> raise (InvalidContext "invalid context in lookup_context")

(** [ins_context gamma id t] inserts [id] and [t] into [gamma] and returns
    the new context *)
let rec ins_context gamma id t =
  Forall (id, t, gamma)
  (* match gamma with 
  | Type -> Forall (id, t, Type)
  | Forall (id', t1, t2) -> Forall (id', t1, ins_context t id t2)
  | _ -> raise (InvalidContext "invalid conext in ins_context") *)
  
let rec chop_context_tail = function
  | Forall (id, t1, Type) -> Type
  | Forall (id, t1, t2) -> Forall (id, t1, chop_context_tail t2)
  | _ -> raise (InvalidContext "invalid context in chop_context_tail")

let rec chop_context_head = function 
  | Forall (id, t1, Type) -> (id, t1)
  | Forall (id, t1, t2) -> chop_context_head t2
  | _ -> raise (InvalidContext "invalid context in chop_context_head")

(** [is_valid_context t] returns true if [t] is a valid context and false 
    otherwise*)
let rec is_valid_context = function 
  | Type -> true
  | Forall (_, _, t) -> is_valid_context t 
  | _ -> false

(** [subst_t var term sub] substitutes all instances of [var] in [term] with 
    [sub] and returns the resulting term *)
let rec subst_t var term sub = 
  match term with
  | Id x when x = var -> sub
  | Id x -> term
  (* TODO: In the true case, should we still substitute in a? *)
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

(** [alpha_equiv gamma t1 t2] returns true if [t1] and [t2] are alpha 
    equivalent and false otherwise *)
let rec alpha_equiv (env: (id*t) list) t1 t2 =
  match (t1, t2) with 
  | (Type, Type) -> true
  | (Id id1, Id id2) -> 
      begin
        (* let left = lookup_context gamma id1 None in 
        let right = lookup_context gamma id2 None in 
        print_endline ("lookup gamma: " ^ (pp_t gamma));
        print_endline ("id left: " ^ id1);
        print_endline ("id right: " ^ id2);
        print_endline ("lookup left: " ^ (pp_t left));
        print_endline ("lookup right: " ^ (pp_t right)); *)
        lookup env id1 = lookup env id2
      end
  | (Fun (id1, l1, r1), Fun (id2, l2, r2))
  | (Forall (id1, l1, r1), Forall (id2, l2, r2)) ->
      if not (fv r2 |> List.exists (fun e -> e = id1)) then 
      begin
        (* r2' = Forall (y, Type, Id y) *)
        let r2' = subst_t id2 r2 (Id id1) in
        (* gamma' = (Forall (y, Type, Forall (x, Type, Type))) *)
        let env' = ins_env env id1 l1 in
        (* print_endline ("gamma: " ^ (pp_t gamma));
        print_endline ("l1: " ^ (pp_t l1));
        print_endline ("l2: " ^ (pp_t l2));
        print_endline ("gamma': " ^ (pp_t gamma'));
        print_endline ("r1: " ^ (pp_t r1));
        print_endline ("r2': " ^ (pp_t r2')); *)
        (alpha_equiv env l1 l2) && (alpha_equiv env' r1 r2')
      end else
      if not (fv r1 |> List.exists (fun e -> e = id2)) then
      begin
        let r1' = subst_t id1 r1 (Id id2) in
        let env' = ins_env env id2 l2 in
        (alpha_equiv env l1 l2) && (alpha_equiv env' r1' r2)
      end else false
  | (App (l1, r1), App (l2, r2)) ->
      (alpha_equiv env l1 l2) && (alpha_equiv env r1 r2)
  | _ -> false

(** [beta_reduce gamma t] performs beta reduction on [t] in the context gamma
  and retuns the result *)
  let rec beta_reduce (env: (id*t) list) t =
    match t with
    | Type -> Type
    | Id id -> lookup env id
    | App (t1, tr) ->
      let tr' = beta_reduce env tr in
      begin
        match beta_reduce env t1 with
        | Fun (id, tl1, tl2)
        | Forall (id, tl1, tl2) when alpha_equiv env tl1 tr' ->
            let tl1' = beta_reduce env tl1 in
            let env' = ins_env env id tl1' in
            let tl' = subst_t id tl2 tr' in
            beta_reduce env' tl'
        | _ -> raise InvalidApplication
      end
    | Fun (id, l, r)
    | Forall (id, l, r) -> t

(* TODO: implement me *)
let rec typecheck_context gamma delta =
  match (gamma, delta) with 
  | (Type, Type) -> Type 
  | (Forall (id, t1, t2), Type) ->
      (* TODO: check this first case *)
      begin
        let hd = chop_context_head gamma in
        let delta = snd hd in
        let tail = chop_context_tail gamma in 
        if is_valid_context delta then typecheck_context tail delta else
          begin
            match typecheck_t delta with 
            | Type -> Type 
            | _ -> raise (InvalidContext "invalid context in typecheck_context")
          end
      end      
  | _, (Forall (id, t1, t2)) -> typecheck_context (ins_context gamma id t1) t2
  | _ -> raise (InvalidContext "invalid context in typecheck_context")

and typecheck_t t =
  if is_valid_context t then (typecheck_context t Type |> ignore; t) else
    typecheck_t_with_context Type t

(** [typecheck_t gamma t] typechecks term [t] under context [gamma] and 
    returns the result *)
and typecheck_t_with_context gamma t =
  (* print_endline "in typecheck_t_with_context";
  print_endline ("gamma: " ^ (pp_t gamma));
  print_endline ("t: " ^ (pp_t t)); *)
  match t with
  | Id x -> lookup_context gamma x None
  | Fun (x, a, t) -> typecheck_fun gamma x a t
  | App (t1, t2) -> typecheck_app gamma t1 t2
  | Forall (x, a, b) -> typecheck_forall gamma x a b
  | Type -> Type

and typecheck_fun gamma x a t =
  let gamma' = ins_context gamma x a in
  let t_type = typecheck_t_with_context gamma' t in
    match typecheck_t_with_context gamma (Forall (x, a, t_type)) with
    | Type -> (Forall (x, a, t_type))
    | e -> raise (MalformedType (pp_t e))

and typecheck_app gamma t1 t2 = Type
  (* let t1_t = typecheck_t_with_context gamma t1 in 
  let t2_t = typecheck_t_with_context gamma t2 in
  print_endline ("gamma: " ^ (pp_t gamma));
  print_endline ("t1: " ^ (pp_t t1));
  print_endline ("t2: " ^ (pp_t t2));
  print_endline ("t1 type: " ^ (pp_t t1_t));
  print_endline ("t2 type: " ^ (pp_t t2_t));
  print_endline ("t1 reduced: " ^ (beta_reduce gamma t1 |> pp_t));
  (* match typecheck_t_with_context gamma t1 with *)
  typecheck_t_with_context gamma t1 |> ignore;
  let t1_reduced = beta_reduce gamma t1 in
  match t1_reduced with
  | Forall (x, a, b) -> 
    print_endline "here here";
    let t2_type = typecheck_t_with_context gamma t2 in 
      if alpha_equiv gamma t2_type a then subst_t x b t2 
      else (print_endline "naur"; raise (MalformedType ((pp_t t1_reduced) ^ " and " ^ (pp_t t2_type))))
  | e -> raise (MalformedType ((pp_t e) ^ " and " ^ (pp_t t2_t) )) *)

and typecheck_forall gamma x a b =
  match typecheck_t_with_context gamma a with
  | Type -> 
    let gamma' = ins_context gamma x a in
    begin
      match typecheck_t_with_context gamma' b with
      | Type -> Type
      | e -> raise (MalformedType (pp_t e))
    end
  | e -> raise (MalformedType (pp_t e))

(** [typecheck_let id t p] typechecks [t] and then substitues it for [id]
    in program [p] and returns the resulting program *)
let rec typecheck_let id t p =
  let t' = typecheck_t t in
  let p_subst = subst_prog id p t' in 
  typecheck_prog p_subst

and typecheck_theorem theorem p =
  failwith "unimplemented 3"

(** [typecheck_prog prog] typechecks [prog] and returns the result *)
and typecheck_prog prog =
  match prog with 
  | Let (id, t, p) -> typecheck_let id t p
  | Theorem (theorem, p) -> typecheck_theorem theorem p
  | Expr t -> typecheck_t t
