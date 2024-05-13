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
         | (1, 14) => 508
         | (1, 15) => 525
         | (2, 10) => 422
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
         | (0, 11) => 506
         | (0, 12) => 501
         | (0, 13) => 499
         | _ => 500
         end in
      freq [ (weight_var, bindGen arbitrary (fun p0 : nat => returnGen (Var p0)));
      (1000 - weight_var, bindGen arbitrary (fun p0 : bool => returnGen (Bool p0)))]
  | S size' =>
      let weight_var := match (size,last_callsite) with 
         | (1, 11) => 504
         | (1, 12) => 500
         | (1, 13) => 500
         | (2, 11) => 509
         | (2, 12) => 502
         | (2, 13) => 501
         | (3, 11) => 526
         | (3, 12) => 501
         | (3, 13) => 499
         | (4, 11) => 521
         | (4, 12) => 493
         | (4, 13) => 493
         | (5, 20) => 281
         | _ => 500
         end in
      let weight_boolean := match (size,last_callsite) with 
         | (1, 11) => 504
         | (1, 12) => 499
         | (1, 13) => 503
         | (2, 11) => 510
         | (2, 12) => 497
         | (2, 13) => 503
         | (3, 11) => 515
         | (3, 12) => 493
         | (3, 13) => 511
         | (4, 11) => 509
         | (4, 12) => 493
         | (4, 13) => 514
         | (5, 20) => 472
         | _ => 500
         end in
      let weight_abs := match (size,last_callsite) with 
         | (1, 11) => 504
         | (1, 12) => 502
         | (1, 13) => 499
         | (2, 11) => 508
         | (2, 12) => 504
         | (2, 13) => 499
         | (3, 11) => 523
         | (3, 12) => 511
         | (3, 13) => 496
         | (4, 11) => 589
         | (4, 12) => 519
         | (4, 13) => 497
         | (5, 20) => 753
         | _ => 500
         end in
      let weight_app := match (size,last_callsite) with 
         | (1, 11) => 488
         | (1, 12) => 499
         | (1, 13) => 499
         | (2, 11) => 472
         | (2, 12) => 497
         | (2, 13) => 498
         | (3, 11) => 432
         | (3, 12) => 494
         | (3, 13) => 494
         | (4, 11) => 356
         | (4, 12) => 493
         | (4, 13) => 495
         | (5, 20) => 302
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


