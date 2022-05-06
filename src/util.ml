(* some utilities *)

open Ast

(*****************************************************
 * HashSet -- like in Java
 *****************************************************)
 module type HashSet = sig
  type 'a t
  val make : unit -> 'a t
  val add : 'a t -> 'a -> unit
  val remove : 'a t -> 'a -> unit
  val mem : 'a t -> 'a -> bool
  val size : 'a t -> int
  val values : 'a t -> 'a list
end

module HashSet : HashSet = struct
  type 'a t = ('a, 'a) Hashtbl.t
  let make() : 'a t = Hashtbl.create 11
  let mem (h : 'a t) (x : 'a) = Hashtbl.mem h x
  let add (h : 'a t) (x : 'a) =
    if mem h x then () else Hashtbl.add h x x
  let remove (h : 'a t) (x : 'a) =
    while Hashtbl.mem h x do
      Hashtbl.remove h x
    done
  let size (h : 'a t) : int = Hashtbl.length h
  let values (h : 'a t) : 'a list =
    Hashtbl.fold (fun x y v -> y :: v) h []
end

(*****************************************************
 * Stream of strings in length-lexicographic order --
 * use to create new variable names
 *****************************************************)
module type LexStream = sig
  type t
  val make : unit -> t
  val next : t -> string
end

module LexStream : LexStream = struct
  type t = int list ref 
  
  let rec inc (s : int list) : int list =
    match s with
      | [] -> [Char.code 'a']
      | x :: t ->
          if x < Char.code 'z' then (x + 1) :: t
          else Char.code 'a' :: inc t
        
  let make() : t = ref [Char.code 'a']

  let next (h : t) : string =
    let l = !h in
    h := inc l;
    String.concat "" (List.map (String.make 1) (List.map Char.chr (List.rev l)))
end

(*****************************************************
 * A source of fresh variable names, avoiding a given
 * set of strings
 *****************************************************)
module type Fresh = sig
  type t
  val make : string HashSet.t -> t
  val avoid : t -> string HashSet.t
  val next : t -> string
end

module Fresh : Fresh = struct
  type t = (string HashSet.t * LexStream.t) ref
        
  let make (avoid : string HashSet.t) : t = ref (avoid, LexStream.make())

  let avoid (s : t) : string HashSet.t = fst (!s)

  let next (s : t) : string =
    let (avoid, stream) = !s in
    let rec check n = if HashSet.mem avoid n then check (LexStream.next stream) else n in
    check (LexStream.next stream)
end

(* list utilities *)
let rec remove_duplicates (s : 'a list) : 'a list =
  match s with
  | [] -> []
  | x :: t -> if List.mem x t then remove_duplicates t else x :: remove_duplicates t

(* remove all elements of list t from list s *)
let remove_all t s =
  List.fold_left (fun s x -> List.filter ((<>) x) s) s t


(** [fv t] returns all the free variables in [t] *)
let rec fv t : id list =
  match t with
  | Id id -> [id]
  | App (t1, t2) -> (fv t1) @ (fv t2)
  | Type -> []
  | Fun (id, t1, t2)
  | Forall (id, t1, t2) -> fv t2 |> (List.filter (fun e -> e <> id))
