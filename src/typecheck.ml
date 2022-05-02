open Ast

type env = (id * t) list

(* type t = 
  | Id of id
  | Fun of id * t * t
  | App of t * t
  | Forall of id * t * t
  | Type *)
let rec subst var term sub = 
  match term with
  | Id x when x = var -> sub
  | Fun (x, a, t) -> if x = var then term else
    Fun (x, (subst var a sub), (subst var t sub))
  | App (t1, t2) -> App ((subst var t1 sub), (subst var t2 sub))
  | Forall (x, a, t) when x = var -> term
  | Forall (x, a, t) -> Forall (x, (subst var a sub), (subst var t sub))
  | Type -> Type
  | _ -> failwith "ah fuck"
let rec typecheck gamma t =
  match t with
  |Id x -> List.assoc x gamma
  |Fun (x, a, t) -> 
    let gamma' = (x, a)::(List.remove_assoc x gamma) in
    let t_type = typecheck gamma' t in
    begin 
    match typecheck gamma (Forall (x, a, t_type)) with
    |Type -> (Forall (x, a, t_type))
    |_ -> failwith "malformed type"
    end
  |App (t1, t2) -> 
    begin
    match typecheck gamma t1 with
    |Forall (x, a, b) -> 
      let t2_type = typecheck gamma t2 in 
       if t2_type = a then subst x b t2 
       else failwith "malformed type"
    |_ -> failwith "malformed type"
    end
  |Forall (x, a, b) -> 
    begin 
    match typecheck gamma a with
    |Type -> 
      let gamma' = (x, a)::(List.remove_assoc x gamma) in
      begin
        match typecheck gamma' b with
        |Type -> Type
        |_ -> failwith "malformed type"
      end
    |_ -> failwith "malformed type"
    end
  |Type -> Type