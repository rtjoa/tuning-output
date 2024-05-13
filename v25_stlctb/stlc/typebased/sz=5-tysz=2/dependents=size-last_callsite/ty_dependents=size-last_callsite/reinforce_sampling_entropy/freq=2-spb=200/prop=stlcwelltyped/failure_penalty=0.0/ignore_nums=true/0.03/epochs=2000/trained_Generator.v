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
         | (1, 14) => 513
         | (1, 15) => 470
         | (2, 10) => 188
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
         | (0, 11) => 470
         | (0, 12) => 610
         | (0, 13) => 390
         | _ => 500
         end in
      freq [ (weight_var, bindGen arbitrary (fun p0 : nat => returnGen (Var p0)));
      (1000 - weight_var, bindGen arbitrary (fun p0 : bool => returnGen (Bool p0)))]
  | S size' =>
      let weight_var := match (size,last_callsite) with 
         | (1, 11) => 260
         | (1, 12) => 527
         | (1, 13) => 491
         | (2, 11) => 63
         | (2, 12) => 516
         | (2, 13) => 499
         | (3, 11) => 26
         | (3, 12) => 513
         | (3, 13) => 499
         | (4, 11) => 12
         | (4, 12) => 484
         | (4, 13) => 484
         | (5, 20) => 3
         | _ => 500
         end in
      let weight_boolean := match (size,last_callsite) with 
         | (1, 11) => 276
         | (1, 12) => 467
         | (1, 13) => 538
         | (2, 11) => 57
         | (2, 12) => 473
         | (2, 13) => 529
         | (3, 11) => 25
         | (3, 12) => 465
         | (3, 13) => 548
         | (4, 11) => 13
         | (4, 12) => 484
         | (4, 13) => 533
         | (5, 20) => 8
         | _ => 500
         end in
      let weight_abs := match (size,last_callsite) with 
         | (1, 11) => 882
         | (1, 12) => 528
         | (1, 13) => 493
         | (2, 11) => 922
         | (2, 12) => 532
         | (2, 13) => 488
         | (3, 11) => 933
         | (3, 12) => 549
         | (3, 13) => 480
         | (4, 11) => 939
         | (4, 12) => 545
         | (4, 13) => 495
         | (5, 20) => 946
         | _ => 500
         end in
      let weight_app := match (size,last_callsite) with 
         | (1, 11) => 15
         | (1, 12) => 475
         | (1, 13) => 476
         | (2, 11) => 7
         | (2, 12) => 477
         | (2, 13) => 482
         | (3, 11) => 5
         | (3, 12) => 468
         | (3, 13) => 470
         | (4, 11) => 4
         | (4, 12) => 484
         | (4, 13) => 486
         | (5, 20) => 3
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


