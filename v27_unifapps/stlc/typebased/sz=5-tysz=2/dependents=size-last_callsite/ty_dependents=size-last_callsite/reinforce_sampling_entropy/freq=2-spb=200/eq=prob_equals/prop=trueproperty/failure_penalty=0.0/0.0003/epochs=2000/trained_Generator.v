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
         | (1, 14) => 497
         | (1, 15) => 497
         | (2, 10) => 459
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
         | (0, 11) => 501
         | (0, 12) => 499
         | (0, 13) => 500
         | _ => 500
         end in
      freq [ (weight_var, bindGen arbitrary (fun p0 : nat => returnGen (Var p0)));
      (1000 - weight_var, bindGen arbitrary (fun p0 : bool => returnGen (Bool p0)))]
  | S size' =>
      let weight_var := match (size,last_callsite) with 
         | (1, 11) => 498
         | (1, 12) => 498
         | (1, 13) => 498
         | (2, 11) => 495
         | (2, 12) => 493
         | (2, 13) => 495
         | (3, 11) => 489
         | (3, 12) => 488
         | (3, 13) => 488
         | (4, 11) => 482
         | (4, 12) => 481
         | (4, 13) => 481
         | (5, 20) => 418
         | _ => 500
         end in
      let weight_boolean := match (size,last_callsite) with 
         | (1, 11) => 499
         | (1, 12) => 499
         | (1, 13) => 498
         | (2, 11) => 493
         | (2, 12) => 494
         | (2, 13) => 494
         | (3, 11) => 489
         | (3, 12) => 489
         | (3, 13) => 489
         | (4, 11) => 482
         | (4, 12) => 481
         | (4, 13) => 480
         | (5, 20) => 418
         | _ => 500
         end in
      let weight_abs := match (size,last_callsite) with 
         | (1, 11) => 502
         | (1, 12) => 502
         | (1, 13) => 503
         | (2, 11) => 505
         | (2, 12) => 506
         | (2, 13) => 504
         | (3, 11) => 507
         | (3, 12) => 507
         | (3, 13) => 507
         | (4, 11) => 510
         | (4, 12) => 510
         | (4, 13) => 510
         | (5, 20) => 536
         | _ => 500
         end in
      let weight_app := match (size,last_callsite) with 
         | (1, 11) => 502
         | (1, 12) => 501
         | (1, 13) => 501
         | (2, 11) => 507
         | (2, 12) => 507
         | (2, 13) => 507
         | (3, 11) => 515
         | (3, 12) => 516
         | (3, 13) => 515
         | (4, 11) => 524
         | (4, 12) => 527
         | (4, 13) => 527
         | (5, 20) => 602
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


