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
         | (1, 14) => 559
         | (1, 15) => 449
         | (2, 10) => 216
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
         | (0, 11) => 504
         | (0, 12) => 514
         | (0, 13) => 486
         | _ => 500
         end in
      freq [ (weight_var, bindGen arbitrary (fun p0 : nat => returnGen (Var p0)));
      (1000 - weight_var, bindGen arbitrary (fun p0 : bool => returnGen (Bool p0)))]
  | S size' =>
      let weight_var := match (size,last_callsite) with 
         | (1, 11) => 514
         | (1, 12) => 503
         | (1, 13) => 497
         | (2, 11) => 527
         | (2, 12) => 509
         | (2, 13) => 498
         | (3, 11) => 549
         | (3, 12) => 516
         | (3, 13) => 490
         | (4, 11) => 407
         | (4, 12) => 490
         | (4, 13) => 490
         | (5, 20) => 50
         | _ => 500
         end in
      let weight_boolean := match (size,last_callsite) with 
         | (1, 11) => 507
         | (1, 12) => 494
         | (1, 13) => 515
         | (2, 11) => 542
         | (2, 12) => 485
         | (2, 13) => 521
         | (3, 11) => 537
         | (3, 12) => 484
         | (3, 13) => 528
         | (4, 11) => 415
         | (4, 12) => 490
         | (4, 13) => 525
         | (5, 20) => 146
         | _ => 500
         end in
      let weight_abs := match (size,last_callsite) with 
         | (1, 11) => 545
         | (1, 12) => 507
         | (1, 13) => 494
         | (2, 11) => 576
         | (2, 12) => 519
         | (2, 13) => 489
         | (3, 11) => 650
         | (3, 12) => 514
         | (3, 13) => 493
         | (4, 11) => 805
         | (4, 12) => 527
         | (4, 13) => 495
         | (5, 20) => 901
         | _ => 500
         end in
      let weight_app := match (size,last_callsite) with 
         | (1, 11) => 427
         | (1, 12) => 496
         | (1, 13) => 494
         | (2, 11) => 326
         | (2, 12) => 487
         | (2, 13) => 491
         | (3, 11) => 192
         | (3, 12) => 485
         | (3, 13) => 487
         | (4, 11) => 91
         | (4, 12) => 492
         | (4, 13) => 490
         | (5, 20) => 53
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


