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
         | (1, 14) => 677
         | (1, 15) => 553
         | (2, 10) => 273
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
         | (0, 11) => 343
         | (0, 12) => 578
         | (0, 13) => 422
         | _ => 500
         end in
      freq [ (weight_var, bindGen arbitrary (fun p0 : nat => returnGen (Var p0)));
      (1000 - weight_var, bindGen arbitrary (fun p0 : bool => returnGen (Bool p0)))]
  | S size' =>
      let weight_var := match (size,last_callsite) with 
         | (1, 11) => 386
         | (1, 12) => 517
         | (1, 13) => 494
         | (2, 11) => 124
         | (2, 12) => 540
         | (2, 13) => 482
         | (3, 11) => 49
         | (3, 12) => 512
         | (3, 13) => 507
         | (4, 11) => 18
         | (4, 12) => 486
         | (4, 13) => 486
         | (5, 20) => 4
         | _ => 500
         end in
      let weight_boolean := match (size,last_callsite) with 
         | (1, 11) => 465
         | (1, 12) => 481
         | (1, 13) => 534
         | (2, 11) => 122
         | (2, 12) => 475
         | (2, 13) => 534
         | (3, 11) => 49
         | (3, 12) => 465
         | (3, 13) => 526
         | (4, 11) => 21
         | (4, 12) => 486
         | (4, 13) => 521
         | (5, 20) => 12
         | _ => 500
         end in
      let weight_abs := match (size,last_callsite) with 
         | (1, 11) => 837
         | (1, 12) => 513
         | (1, 13) => 488
         | (2, 11) => 908
         | (2, 12) => 508
         | (2, 13) => 501
         | (3, 11) => 925
         | (3, 12) => 553
         | (3, 13) => 495
         | (4, 11) => 935
         | (4, 12) => 539
         | (4, 13) => 499
         | (5, 20) => 943
         | _ => 500
         end in
      let weight_app := match (size,last_callsite) with 
         | (1, 11) => 27
         | (1, 12) => 488
         | (1, 13) => 481
         | (2, 11) => 13
         | (2, 12) => 475
         | (2, 13) => 481
         | (3, 11) => 8
         | (3, 12) => 465
         | (3, 13) => 471
         | (4, 11) => 6
         | (4, 12) => 486
         | (4, 13) => 494
         | (5, 20) => 5
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


