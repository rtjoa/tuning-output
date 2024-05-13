From QuickChick Require Import QuickChick. Import QcNotation.
From Coq Require Import Bool ZArith List. Import ListNotations.
From ExtLib Require Import Monad.
From ExtLib.Data.Monads Require Import OptionMonad.
Import MonadNotation.

From STLC Require Import Impl Spec.

Fixpoint manual_gen_typ (size : nat) (last_callsite : nat) : G Typ :=
  match size with
  | 0 => returnGen TBool
  | S size' =>
      let weight_tbool := match (size,last_callsite) with 
         | (1, 14) => 498
         | (1, 15) => 90
         | (2, 10) => 1000
         | _ => 500
         end in
      freq [ (weight_tbool, returnGen TBool);
      (1000 - weight_tbool,
      bindGen (manual_gen_typ size' 14)
        (fun p0 : Typ =>
         bindGen (manual_gen_typ size' 15)
           (fun p1 : Typ => returnGen (TFun p0 p1))))]
  end.

Fixpoint manual_gen_expr (size : nat) (last_callsite : nat) : G Expr :=
  match size with
  | 0 =>
      let weight_var := match (size,last_callsite) with 
         | (0, 11) => 0
         | (0, 12) => 975
         | (0, 13) => 1000
         | _ => 500
         end in
      freq [ (weight_var, bindGen arbitrary (fun p0 : nat => returnGen (Var p0)));
      (1000 - weight_var, bindGen arbitrary (fun p0 : bool => returnGen (Bool p0)))]
  | S size' =>
      let weight_var := match (size,last_callsite) with 
         | (1, 11) => 867
         | (1, 12) => 931
         | (1, 13) => 993
         | (2, 11) => 170
         | (2, 12) => 1000
         | (2, 13) => 999
         | (3, 11) => 0
         | (3, 12) => 77
         | (3, 13) => 7
         | (4, 11) => 1
         | (4, 12) => 1
         | (4, 13) => 1
         | (5, 20) => 0
         | _ => 500
         end in
      let weight_boolean := match (size,last_callsite) with 
         | (1, 11) => 961
         | (1, 12) => 989
         | (1, 13) => 2
         | (2, 11) => 2
         | (2, 12) => 23
         | (2, 13) => 69
         | (3, 11) => 0
         | (3, 12) => 998
         | (3, 13) => 995
         | (4, 11) => 1
         | (4, 12) => 1
         | (4, 13) => 0
         | (5, 20) => 0
         | _ => 500
         end in
      let weight_abs := match (size,last_callsite) with 
         | (1, 11) => 944
         | (1, 12) => 994
         | (1, 13) => 988
         | (2, 11) => 879
         | (2, 12) => 5
         | (2, 13) => 94
         | (3, 11) => 336
         | (3, 12) => 102
         | (3, 13) => 4
         | (4, 11) => 572
         | (4, 12) => 48
         | (4, 13) => 348
         | (5, 20) => 621
         | _ => 500
         end in
      let weight_app := match (size,last_callsite) with 
         | (1, 11) => 965
         | (1, 12) => 994
         | (1, 13) => 989
         | (2, 11) => 975
         | (2, 12) => 1000
         | (2, 13) => 1000
         | (3, 11) => 975
         | (3, 12) => 1000
         | (3, 13) => 1000
         | (4, 11) => 965
         | (4, 12) => 983
         | (4, 13) => 996
         | (5, 20) => 1000
         | _ => 500
         end in
      freq [ (weight_var,
      bindGen arbitrary (fun p0 : nat => returnGen (Var p0)));
      (weight_boolean, bindGen arbitrary (fun p0 : bool => returnGen (Bool p0)));
      (weight_abs,
      bindGen (manual_gen_typ 2 10)
        (fun p0 : Typ =>
         bindGen (manual_gen_expr size' 11)
           (fun p1 : Expr => returnGen (Abs p0 p1))));
      (weight_app,
      bindGen (manual_gen_expr size' 12)
        (fun p0 : Expr =>
         bindGen (manual_gen_expr size' 13)
           (fun p1 : Expr => returnGen (App p0 p1))))]
  end.

Definition gSized :=
  manual_gen_expr 5 20.
  
Definition test_prop_SinglePreserve :=
  forAll gSized (fun (e: Expr) =>
    prop_SinglePreserve e).

(*! QuickChick test_prop_SinglePreserve. *)
  
Definition test_prop_MultiPreserve :=
  forAll gSized (fun (e: Expr) =>
    prop_MultiPreserve e).
  
(*! QuickChick test_prop_MultiPreserve. *)


