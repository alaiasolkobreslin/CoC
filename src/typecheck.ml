open Ast

exception MalformedType of string
exception InvalidApplication of string
exception InvalidContext of string
exception NotFound of string

(** [lookup env id] returns the value associated with [id] in [env], if it
    exists, and raises [NotFound] otherwise *)
let lookup env id =
  match List.assoc_opt id env with 
  | Some t -> t
  | None -> raise (NotFound id)

(** [ins_env] inserts the binding [(id1, id2)] into [env] and returns the
    result *)
let ins_env env id1 id2 = (id1, id2)::(List.remove_assoc id1 env)

let pp_env env = 
  print_string "[";
  let rec helper lst  = 
    match lst with 
    | (id, t)::tl -> ("(" ^ id ^ ", " ^ t ^ "), ") ^ helper tl
    | [] -> "]" in
  helper env ^ "]"

(** [lookup_conext gamma id curr] returns the most recent binding of [id]
    in [gamma] which is passed as [curr] and raises [InvalidContext] if
    the end of the context is reached and [curr] is [None] *)
let rec lookup_context gamma id curr =
  match (gamma, curr) with 
  | (Type, None) -> raise (NotFound id)
  | (Type, Some v) -> v
  | (Forall (id', t1, t2), _) when id' = id -> lookup_context t2 id (Some t1)
  | (Forall (id', t1, t2), _) -> lookup_context t2 id curr
  | _ -> raise (InvalidContext "invalid context in lookup_context")

(** [ins_context gamma id t] inserts [id] and [t] into [gamma] and returns
    the new context *)
let rec ins_context gamma id t =
  match gamma with 
  | Type -> Forall (id, t, Type)
  | Forall (id', t1, t2) -> Forall (id', t1, ins_context t2 id t)
  | _ -> raise (InvalidContext "invalid conext in ins_context")

(** [chop_context_tail gamma] returns the tail of context [gamma]. This means
    that if [gamma] = Γ \[x:P\], then [chop_context_tail] returns Γ. This
    function is useful for typing a valid context *)
let rec chop_context_tail = function
  | Forall (id, t1, Type) -> Type
  | Forall (id, t1, t2) -> Forall (id, t1, chop_context_tail t2)
  | _ -> raise (InvalidContext "invalid context in chop_context_tail")

(** [chop_context_head gamma] returns the head of context [gamma]. This means
    that if [gamma] = Γ \[x:P\], then [chop_context_head] returns (x, P). This
    function is useful for typing a valid context *)
let rec chop_context_head = function 
  | Forall (id, t1, Type) -> (id, t1)
  | Forall (id, t1, t2) -> chop_context_head t2
  | _ -> raise (InvalidContext "invalid context in chop_context_head")

(** [is_valid_context t] returns true if [t] is a valid context and false 
    otherwise *)
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
let rec alpha_equiv (env: (id*id) list) t1 t2 =
  match (t1, t2) with 
  | (Type, Type) -> true
  | (Id id1, Id id2) -> 
      if id1 = id2 then true else
      lookup env id1 = lookup env id2
  | (Fun (id1, l1, r1), Fun (id2, l2, r2))
  | (Forall (id1, l1, r1), Forall (id2, l2, r2)) ->
      let env' = ins_env env id1 id2 in
      (alpha_equiv env' l1 l2) && (alpha_equiv env' r1 r2)
  | (App (l1, r1), App (l2, r2)) ->
      (alpha_equiv env l1 l2) && (alpha_equiv env r1 r2)
  | _ -> false

(** [beta_reduce gamma t] performs beta reduction on [t] in the context gamma
    and retuns the result *)
let rec beta_reduce gamma t =
  match t with
  | Type -> Type
  | Id _ -> t
  | App (Fun (id, l, r), t2) ->
    begin       
      let t2' = typecheck_non_context gamma t2 in
      if alpha_equiv [] l t2' then
        begin 
          let t' = subst_t id r t2 in 
          if alpha_equiv [] t' t then t' else beta_reduce gamma t'
        end
      else raise (InvalidApplication "invalid application in beta reduce")
    end
  | App (t1, tr) ->
    let t' = App (beta_reduce gamma t1, beta_reduce gamma tr) in 
    if alpha_equiv [] t' t then t' else beta_reduce gamma t'
  | Fun (id, l, r) ->
    begin 
      let gamma' = ins_context gamma id l in 
      let l' = beta_reduce gamma l in 
      let r' = beta_reduce gamma' r in
      typecheck_non_context gamma' r |> ignore;
      let t' = Fun (id, l', r') in 
      if alpha_equiv [] t' t then t' else beta_reduce gamma t'
    end
  | Forall (id, l, r) ->
    begin 
      let gamma' = ins_context gamma id l in
      let l' = beta_reduce gamma l in 
      let r' = beta_reduce gamma' r in 
      let t' = Forall (id, l', r') in 
      if alpha_equiv [] t' t then t' else beta_reduce gamma t'
    end

(** [typecheck_context gamma delta] typechecks [delta] in context [gamma].
    If this is successful, [Type] is returned. Otherwise, [InvalidContext]
    is raised *)
and typecheck_context gamma delta =
  match (gamma, delta) with
    (* valid context case 1 *)
  | (Type, Type) -> Type 
    (* valid context cases 2 and 3 *)
  | (Forall (id, t1, t2), Type) ->
      begin
        let hd = chop_context_head gamma in
        let delta = snd hd in
        let tail = chop_context_tail gamma in
        (* valid context case 2: Γ [x:Δ] |- * *)
        if is_valid_context delta then typecheck_context tail delta else
          (* valid context case 3: Γ [x:P] |- * *)
          begin
            match typecheck_t_with_context tail delta with 
            | Type -> Type 
            | _ -> raise (InvalidContext "invalid context in typecheck_context")
          end
      end
    (* product formation cases 1 and 2 *)
    (* product formation case 1: Γ |- [x:P]Δ *)
    (* product formation case 2: Γ |- [x:P]N : * *)
  | _, (Forall (id, t1, t2)) -> typecheck_context (ins_context gamma id t1) t2
  | _ -> raise (InvalidContext "invalid context in typecheck_context")

(** [typecheck_non_context gamma t] typechecks [t] in context [gamma], 
    performs beta reduction, and returns the result *)
and typecheck_non_context gamma t =
  typecheck_t_with_context gamma t |> (beta_reduce gamma)

(** [typecheck_t t] returns [Type] if [t] is a valid context and otherwise
    returns the result of typechecking [t] in context [Type] *)
and typecheck_t t =
  if is_valid_context t then (typecheck_context t |> ignore; Type) else
  typecheck_non_context Type t

(** [interp_t t] performs beta reduction on [t] and returns the result *)
and interp_t t = beta_reduce Type t

(** [typecheck_t gamma t] typechecks term [t] under context [gamma] and 
    returns the result *)
and typecheck_t_with_context gamma t =
  match t with
  | Id x -> lookup_context gamma x None
  | Fun (x, a, t) -> typecheck_fun gamma x a t
  | App (t1, t2) -> typecheck_app gamma t1 t2
  | Forall (x, a, b) -> typecheck_forall gamma x a b
  | Type -> Type


(** [typecheck_fun gamma x a t] typechecks [Fun (x, a, t)] under context
    [gamma] and returns the result *)
and typecheck_fun gamma x a t =
  let gamma' = ins_context gamma x a in
  let t_type = typecheck_non_context gamma' t in
  Forall (x, a, t_type)

(** [typecheck_forall gamma x a b] typechecks [Forall (x, a, b)] under context
    [gamma] and returns the result *)
and typecheck_forall gamma x a b =
  let gamma' = ins_context gamma x a in
  typecheck_context gamma' |> ignore;
  Type

(** [typecheck_app gamma t1 t2] typechecks [App (t1, t2)] under context gamma
    and returns the result *)
and typecheck_app gamma t1 t2 =
  let t1_t = typecheck_non_context gamma t1 in
  let t2_t = typecheck_non_context gamma t2 in
  match t1_t with
  | Forall (x, a, b) ->
      if alpha_equiv [] t2_t a then subst_t x b t2
      else raise (MalformedType ((pp_t a) ^ " and " ^ (pp_t t2_t)))
  | e -> raise (MalformedType ("wasn't even a forall " ^ (pp_t t1_t) ^ " and " ^ (pp_t t2_t) ))

(** [typecheck_let id t p] typechecks [t] and then substitues it for [id]
    in program [p] and returns the resulting program *)
let rec typecheck_let id t p prints =
  let t_res = interp_t t in
  let p_subst = subst_prog id p t_res in 
  let print' = "\nLet: " ^ id ^ " beta reduced: " ^ (pp_t t_res) in
  typecheck_prog p_subst (print'::prints)

(** [typecheck_theorem theorem p] checks that the type of [theorem.proof]
    is alpha equivalent to the beta reduction of [theorem.theorem]. 
    If it is, then it substitutes the beta_reduction of the proof in for
    theorem.id throughout the rest of the program [p]. Otherwise, it raises
    [MalformedType] *)
and typecheck_theorem theorem p prints =
  let {id; theorem; proof} = theorem in
  typecheck_t theorem |> ignore;
  let theorem' = interp_t theorem in
  let proof' = typecheck_t proof in 
  let proof_val = interp_t proof in
  let theorem_print = "Theorem: " ^ id ^ " beta reduced: " ^ (pp_t theorem') in 
  let proof_print_t = "Proof typed: " ^ (pp_t proof') in
  let proof_print_b = "Proof beta reduced: " ^ (pp_t proof_val) in
  if alpha_equiv [] theorem' proof' then
    typecheck_prog (subst_prog id p proof_val) 
      ("\n"::proof_print_b::proof_print_t::theorem_print::prints) else
  raise (MalformedType ("Invalid Proof:\n" ^ (pp_t theorem') ^ " and \n" ^ (pp_t proof')))

(** [typecheck_prog prog] typechecks [prog] and returns the result *)
and typecheck_prog prog prints =
  match prog with 
  | Let (id, t, p) -> typecheck_let id t p prints
  | Theorem (theorem, p) -> typecheck_theorem theorem p prints
  | Expr t -> 
    begin
      let print_t = "Term typed: " ^ (pp_t (typecheck_t t)) in
      let print_i = interp_t t |> pp_t in
      let prints' = print_t::print_i::prints in 
      prints'
    end
