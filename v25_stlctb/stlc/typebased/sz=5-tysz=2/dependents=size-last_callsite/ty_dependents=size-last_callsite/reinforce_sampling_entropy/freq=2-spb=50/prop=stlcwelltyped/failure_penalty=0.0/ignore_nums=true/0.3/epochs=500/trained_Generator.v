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
         | (1, 14) => 716
         | (1, 15) => 259
         | (2, 10) => 176
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
         | (0, 11) => 560
         | (0, 12) => 676
         | (0, 13) => 324
         | _ => 500
         end in
      freq [ (weight_var, bindGen arbitrary (fun p0 : nat => returnGen (Var p0)));
      (1000 - weight_var, bindGen arbitrary (fun p0 : bool => returnGen (Bool p0)))]
  | S size' =>
      let weight_var := match (size,last_callsite) with 
         | (1, 11) => 167
         | (1, 12) => 511
         | (1, 13) => 494
         | (2, 11) => 16
         | (2, 12) => 501
         | (2, 13) => 514
         | (3, 11) => 15
         | (3, 12) => 508
         | (3, 13) => 496
         | (4, 11) => 5
         | (4, 12) => 494
         | (4, 13) => 494
         | (5, 20) => 1
         | _ => 500
         end in
      let weight_boolean := match (size,last_callsite) with 
         | (1, 11) => 99
         | (1, 12) => 474
         | (1, 13) => 511
         | (2, 11) => 20
         | (2, 12) => 455
         | (2, 13) => 567
         | (3, 11) => 10
         | (3, 12) => 451
         | (3, 13) => 511
         | (4, 11) => 6
         | (4, 12) => 494
         | (4, 13) => 518
         | (5, 20) => 3
         | _ => 500
         end in
      let weight_abs := match (size,last_callsite) with 
         | (1, 11) => 925
         | (1, 12) => 539
         | (1, 13) => 521
         | (2, 11) => 942
         | (2, 12) => 579
         | (2, 13) => 455
         | (3, 11) => 944
         | (3, 12) => 580
         | (3, 13) => 539
         | (4, 11) => 949
         | (4, 12) => 518
         | (4, 13) => 494
         | (5, 20) => 955
         | _ => 500
         end in
      let weight_app := match (size,last_callsite) with 
         | (1, 11) => 3
         | (1, 12) => 474
         | (1, 13) => 474
         | (2, 11) => 1
         | (2, 12) => 455
         | (2, 13) => 455
         | (3, 11) => 1
         | (3, 12) => 451
         | (3, 13) => 451
         | (4, 11) => 1
         | (4, 12) => 494
         | (4, 13) => 494
         | (5, 20) => 1
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

#[global]
Instance genExpr : GenSized (Expr) := 
  {| arbitrarySized n := manual_gen_expr n 20 |}.
  
Definition test_prop_SinglePreserve :=
  forAll arbitrary (fun (e: Expr) =>
    prop_SinglePreserve e).

(*! QuickChick test_prop_SinglePreserve. *)
  
Definition test_prop_MultiPreserve :=
  forAll arbitrary (fun (e: Expr) =>
    prop_MultiPreserve e).
  
(*! QuickChick test_prop_MultiPreserve. *)


