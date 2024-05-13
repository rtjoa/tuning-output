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
         | (1, 14) => 528
         | (1, 15) => 503
         | (2, 10) => 198
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
         | (0, 11) => 499
         | (0, 12) => 521
         | (0, 13) => 479
         | _ => 500
         end in
      freq [ (weight_var, bindGen arbitrary (fun p0 : nat => returnGen (Var p0)));
      (1000 - weight_var, bindGen arbitrary (fun p0 : bool => returnGen (Bool p0)))]
  | S size' =>
      let weight_var := match (size,last_callsite) with 
         | (1, 11) => 522
         | (1, 12) => 505
         | (1, 13) => 496
         | (2, 11) => 557
         | (2, 12) => 508
         | (2, 13) => 499
         | (3, 11) => 496
         | (3, 12) => 511
         | (3, 13) => 496
         | (4, 11) => 258
         | (4, 12) => 488
         | (4, 13) => 488
         | (5, 20) => 27
         | _ => 500
         end in
      let weight_boolean := match (size,last_callsite) with 
         | (1, 11) => 534
         | (1, 12) => 490
         | (1, 13) => 514
         | (2, 11) => 559
         | (2, 12) => 485
         | (2, 13) => 520
         | (3, 11) => 504
         | (3, 12) => 479
         | (3, 13) => 529
         | (4, 11) => 256
         | (4, 12) => 488
         | (4, 13) => 527
         | (5, 20) => 77
         | _ => 500
         end in
      let weight_abs := match (size,last_callsite) with 
         | (1, 11) => 561
         | (1, 12) => 513
         | (1, 13) => 497
         | (2, 11) => 612
         | (2, 12) => 521
         | (2, 13) => 493
         | (3, 11) => 750
         | (3, 12) => 527
         | (3, 13) => 492
         | (4, 11) => 866
         | (4, 12) => 534
         | (4, 13) => 495
         | (5, 20) => 917
         | _ => 500
         end in
      let weight_app := match (size,last_callsite) with 
         | (1, 11) => 365
         | (1, 12) => 491
         | (1, 13) => 493
         | (2, 11) => 215
         | (2, 12) => 486
         | (2, 13) => 488
         | (3, 11) => 99
         | (3, 12) => 481
         | (3, 13) => 482
         | (4, 11) => 51
         | (4, 12) => 489
         | (4, 13) => 489
         | (5, 20) => 29
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


