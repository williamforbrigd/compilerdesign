open Assert
open Hellocaml

(* These tests are provided by you -- they will NOT be graded *)

(* You should also add additional test cases here to help you   *)
(* debug your program.                                          *)

let context1 : ctxt = [("x", 3L); ("y", 2L)]

let e4 : exp = Mult(Const 50L, Add(e1, e3));;
let e5: exp = Add(Const 3L, Const 4L);;
let e6: exp = Add(Var "x", Neg(Add(Var "x", Neg(Const 1L))));;

let p1 : program = compile e1;;
let p2 : program = compile e2;;
let p3 : program = compile e3;;
let p4 : program = compile e4;;

let provided_tests : suite = [
  Test ("Student-Provided Tests For Problem 1-3", [
    ("case1", assert_eqf (fun () -> 42) prob3_ans );
    ("case2", assert_eqf (fun () -> 25) (prob3_case2 17) );
    ("case3", assert_eqf (fun () -> prob3_case3) 64);
  ]);

  Test("Problem3-5_provided", [
    ("list_not_sorted", assert_eqf(fun () -> insert 3 [4;2;1]) [4;2;1]);
  ]);

  Test("4-5_provided", [
    ("optimizer1", assert_eqf(fun () -> optimize e5) (Const 7L));
    ("optimizer2", assert_eqf(fun () -> optimize e6) (Const 1L));
  ]);

  Test("Problem4-4_provided", [
    ("interpret_raise ", assert_eqf (fun () -> interpret ctxt2 e3) (-63L));
  ]);

  Test("Problem 5", [
    ("compile_run1", assert_eqf(fun () -> run [] p1) 6L);
    ("compile_run2", assert_eqf(fun () -> run ["x", 3L] p2) 4L);
    ("compile_run3", assert_eqf(fun () -> run context1 p3) (-32L));
    ("compile_run4", assert_eqf(fun () -> run context1 p4) (-1300L));
  ]);

] 
