open OUnit2
open Hazel.Ast
open Hazel.Typecheck

let compare_t env t1 t2 = alpha_equiv env t1 t2

type env = (id * t) list

let make_alpha_equiv_test
    (name : string)
    (gamma : env)
    (t1 : t)
    (t2 : t)
    (expected : bool) : test = 
  name >:: (fun _ ->
      assert_equal expected (alpha_equiv gamma t1 t2))

let make_beta_reduce_equiv_test
    (name : string)
    (gamma : t)
    (t1 : t)
    (t2 : t) : test =
  name >:: (fun _ ->
      assert_equal (beta_reduce gamma t1) (beta_reduce gamma t2) ~printer:pp_t ~cmp:(compare_t [])) 

let make_beta_reduce_raises_test
    (name : string)
    (gamma : t)
    (t1 : t) : test =
  name >:: (fun _ ->
      assert_raises InvalidApplication (fun () -> beta_reduce gamma t1)) 

let make_typecheck_context_test
    (name : string)
    (gamma : t)
    (delta : t)
    (expected : t) : test = 
  name >:: (fun _ ->
      assert_equal expected (typecheck_context gamma delta))

let fun_1 = Fun ("x", Fun ("y", Type, Type), Fun ("z", Type, App (Id "x", Id "z")))
(* Fun x:(Type -> Type) -> Fun z:Type -> (x z) *)
let fun_2 = Fun("x", Type, Fun ("z", Fun ("y", Type, Type), App (Id "z", Id "x")))
(* Fun x:Type -> Fun z:(Type->Type) -> (z x) *)


let alpha_equiv_tests = [
    make_alpha_equiv_test "same function, different arg name" [] 
      (Fun ("x", Type, Type)) (Fun ("y", Type, Type)) true;
    make_alpha_equiv_test "same forall, different arg name" []
      (Forall ("x", Type, Type)) (Forall ("y", Type, Type)) true;
    make_alpha_equiv_test "funs beta equiv, but not alpha equiv" [] fun_1 fun_2 false;
    make_alpha_equiv_test "different ids, same type" [("x", Type); ("y", Type)]
      (Id "x") (Id "y") true;
    make_alpha_equiv_test "app alpha equiv returns false" 
      [("x", Type); ("y", Fun ("z", Type, Type))] (App (Id "x", Id "y"))
      (App (Id "y", Id "x")) false;
    make_alpha_equiv_test "app alpha equiv returns true"
      [("x", Fun ("y", Type, Type)); ("a", Type); ("b", Type)]
      (App (Id "x", Id "a")) (App (Id "x", Id "b")) true;
    make_alpha_equiv_test "id is in the free variables"
      [("x", Type)] (Forall ("y", Type, Id "x")) (Forall ("x", Type, Id "x")) true;
    make_alpha_equiv_test "id in free variables, not alpha equiv"
      [("x", Fun ("a", Type, Type))] (Forall ("y", Type, Id "x")) 
      (Forall ("x", Type, Id "x")) false;
    make_alpha_equiv_test "id in free variables, not alpha equiv (swapped)"
      [("x", Fun ("a", Type, Type))] (Forall ("x", Type, Id "x"))
      (Forall ("y", Type, Id "x")) false;
    make_alpha_equiv_test "two levels of forall, different var names" [] 
      (Forall ("x", Type, Forall ("y", Type, Type)))
      (Forall ("a", Type, Forall ("b", Type, Type))) true;
]

let beta_reduce_tests = [
    make_beta_reduce_equiv_test "getting id from env" 
      (Forall ("x", Type, Type)) (Id "x") Type;
    make_beta_reduce_equiv_test "simple function application" Type
      (App (Fun ("x", Type, Type), Type)) Type;
    make_beta_reduce_equiv_test "simple forall application" Type
      (App (Forall ("x", Type, Type), Type)) Type;
    make_beta_reduce_raises_test "too many applications"
      (Forall ("x", Forall ("a", Type, Type), Forall ("y", Type, Type)))
      (App (App (App (fun_1, Id "x"), Id "y"), Type));
    make_beta_reduce_equiv_test "different order of application"
      (Forall ("x", Forall ("a", Type, Type), Forall ("y", Type, Type)))
      (App (App (fun_1, Id "x"), Id "y")) (App (App (fun_2, Id "y"), Id "x"));
]

let typecheck_tests = [
    make_typecheck_context_test "typecheck nested context"
      (Forall ("x", Type, Forall ("y", Id("x"), Type))) Type Type;
    make_typecheck_context_test "another typecheck nested context"
      (Forall ("x", Type, Forall ("y", Id("x"), Forall ("z", Id "x", Type)))) 
      Type Type;
]

let suite = "test suite for Hazel" >::: List.flatten [
  alpha_equiv_tests;
  beta_reduce_tests;
  typecheck_tests
]

let _ = run_test_tt_main suite