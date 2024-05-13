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
         | (1, 14) => 504
         | (1, 15) => 506
         | (2, 10) => 472
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
         | (0, 11) => 500
         | (0, 12) => 501
         | (0, 13) => 499
         | _ => 500
         end in
      freq [ (weight_var, bindGen arbitrary (fun p0 : nat => returnGen (Var p0)));
      (1000 - weight_var, bindGen arbitrary (fun p0 : bool => returnGen (Bool p0)))]
  | S size' =>
      let weight_var := match (size,last_callsite) with 
         | (1, 11) => 501
         | (1, 12) => 500
         | (1, 13) => 500
         | (2, 11) => 504
         | (2, 12) => 500
         | (2, 13) => 500
         | (3, 11) => 506
         | (3, 12) => 500
         | (3, 13) => 500
         | (4, 11) => 508
         | (4, 12) => 497
         | (4, 13) => 497
         | (5, 20) => 412
         | _ => 500
         end in
      let weight_boolean := match (size,last_callsite) with 
         | (1, 11) => 501
         | (1, 12) => 499
         | (1, 13) => 501
         | (2, 11) => 503
         | (2, 12) => 499
         | (2, 13) => 501
         | (3, 11) => 506
         | (3, 12) => 497
         | (3, 13) => 504
         | (4, 11) => 507
         | (4, 12) => 497
         | (4, 13) => 507
         | (5, 20) => 497
         | _ => 500
         end in
      let weight_abs := match (size,last_callsite) with 
         | (1, 11) => 502
         | (1, 12) => 501
         | (1, 13) => 500
         | (2, 11) => 504
         | (2, 12) => 502
         | (2, 13) => 499
         | (3, 11) => 511
         | (3, 12) => 504
         | (3, 13) => 498
         | (4, 11) => 534
         | (4, 12) => 508
         | (4, 13) => 499
         | (5, 20) => 631
         | _ => 500
         end in
      let weight_app := match (size,last_callsite) with 
         | (1, 11) => 495
         | (1, 12) => 500
         | (1, 13) => 500
         | (2, 11) => 490
         | (2, 12) => 499
         | (2, 13) => 499
         | (3, 11) => 476
         | (3, 12) => 498
         | (3, 13) => 498
         | (4, 11) => 446
         | (4, 12) => 497
         | (4, 13) => 498
         | (5, 20) => 424
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


