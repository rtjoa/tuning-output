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
         | (1, 14) => 478
         | (1, 15) => 453
         | (2, 10) => 190
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
         | (0, 11) => 522
         | (0, 12) => 723
         | (0, 13) => 277
         | _ => 500
         end in
      freq [ (weight_var, bindGen arbitrary (fun p0 : nat => returnGen (Var p0)));
      (1000 - weight_var, bindGen arbitrary (fun p0 : bool => returnGen (Bool p0)))]
  | S size' =>
      let weight_var := match (size,last_callsite) with 
         | (1, 11) => 103
         | (1, 12) => 532
         | (1, 13) => 482
         | (2, 11) => 14
         | (2, 12) => 541
         | (2, 13) => 499
         | (3, 11) => 5
         | (3, 12) => 516
         | (3, 13) => 496
         | (4, 11) => 3
         | (4, 12) => 484
         | (4, 13) => 484
         | (5, 20) => 1
         | _ => 500
         end in
      let weight_boolean := match (size,last_callsite) with 
         | (1, 11) => 109
         | (1, 12) => 459
         | (1, 13) => 560
         | (2, 11) => 14
         | (2, 12) => 461
         | (2, 13) => 549
         | (3, 11) => 4
         | (3, 12) => 465
         | (3, 13) => 551
         | (4, 11) => 3
         | (4, 12) => 484
         | (4, 13) => 530
         | (5, 20) => 2
         | _ => 500
         end in
      let weight_abs := match (size,last_callsite) with 
         | (1, 11) => 925
         | (1, 12) => 531
         | (1, 13) => 479
         | (2, 11) => 944
         | (2, 12) => 529
         | (2, 13) => 479
         | (3, 11) => 950
         | (3, 12) => 542
         | (3, 13) => 480
         | (4, 11) => 952
         | (4, 12) => 542
         | (4, 13) => 495
         | (5, 20) => 957
         | _ => 500
         end in
      let weight_app := match (size,last_callsite) with 
         | (1, 11) => 1
         | (1, 12) => 474
         | (1, 13) => 473
         | (2, 11) => 1
         | (2, 12) => 464
         | (2, 13) => 469
         | (3, 11) => 1
         | (3, 12) => 472
         | (3, 13) => 470
         | (4, 11) => 1
         | (4, 12) => 487
         | (4, 13) => 489
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


