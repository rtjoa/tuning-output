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
         | (1, 14) => 110
         | (1, 15) => 0
         | (2, 10) => 100
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
         | (0, 11) => 511
         | (0, 12) => 500
         | (0, 13) => 500
         | _ => 500
         end in
      freq [ (weight_var, bindGen arbitrary (fun p0 : nat => returnGen (Var p0)));
      (1000 - weight_var, bindGen arbitrary (fun p0 : bool => returnGen (Bool p0)))]
  | S size' =>
      let weight_var := match (size,last_callsite) with 
         | (1, 11) => 117
         | (1, 12) => 550
         | (1, 13) => 532
         | (2, 11) => 115
         | (2, 12) => 538
         | (2, 13) => 487
         | (3, 11) => 24
         | (3, 12) => 439
         | (3, 13) => 643
         | (4, 11) => 21
         | (4, 12) => 478
         | (4, 13) => 478
         | (5, 20) => 0
         | _ => 500
         end in
      let weight_boolean := match (size,last_callsite) with 
         | (1, 11) => 127
         | (1, 12) => 426
         | (1, 13) => 548
         | (2, 11) => 168
         | (2, 12) => 487
         | (2, 13) => 538
         | (3, 11) => 21
         | (3, 12) => 405
         | (3, 13) => 511
         | (4, 11) => 35
         | (4, 12) => 478
         | (4, 13) => 514
         | (5, 20) => 1
         | _ => 500
         end in
      let weight_abs := match (size,last_callsite) with 
         | (1, 11) => 947
         | (1, 12) => 584
         | (1, 13) => 493
         | (2, 11) => 937
         | (2, 12) => 487
         | (2, 13) => 487
         | (3, 11) => 948
         | (3, 12) => 684
         | (3, 13) => 405
         | (4, 11) => 944
         | (4, 12) => 563
         | (4, 13) => 530
         | (5, 20) => 960
         | _ => 500
         end in
      let weight_app := match (size,last_callsite) with 
         | (1, 11) => 1
         | (1, 12) => 426
         | (1, 13) => 426
         | (2, 11) => 1
         | (2, 12) => 487
         | (2, 13) => 487
         | (3, 11) => 1
         | (3, 12) => 405
         | (3, 13) => 405
         | (4, 11) => 1
         | (4, 12) => 478
         | (4, 13) => 478
         | (5, 20) => 0
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


