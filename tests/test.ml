open OUnit2
open Hazel.Ast
open Hazel.Typecheck
(* open Main *)

let make_alpha_equiv_test
    (name : string)
    (gamma : env)
    (t1 : t)
    (t2 : t)
    (expected : bool) : test = 
  name >:: (fun _ ->
      assert_equal expected (alpha_equiv gamma t1 t2))

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
]

let suite = "test suite for Hazel" >::: List.flatten [alpha_equiv_tests]

let _ = run_test_tt_main suite