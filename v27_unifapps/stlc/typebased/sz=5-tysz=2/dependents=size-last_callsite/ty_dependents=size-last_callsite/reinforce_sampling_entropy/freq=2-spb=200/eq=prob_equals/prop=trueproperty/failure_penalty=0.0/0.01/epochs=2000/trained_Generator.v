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
         | (1, 14) => 448
         | (1, 15) => 415
         | (2, 10) => 207
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
         | (0, 12) => 438
         | (0, 13) => 374
         | _ => 500
         end in
      freq [ (weight_var, bindGen arbitrary (fun p0 : nat => returnGen (Var p0)));
      (1000 - weight_var, bindGen arbitrary (fun p0 : bool => returnGen (Bool p0)))]
  | S size' =>
      let weight_var := match (size,last_callsite) with 
         | (1, 11) => 116
         | (1, 12) => 130
         | (1, 13) => 117
         | (2, 11) => 82
         | (2, 12) => 27
         | (2, 13) => 22
         | (3, 11) => 89
         | (3, 12) => 8
         | (3, 13) => 8
         | (4, 11) => 207
         | (4, 12) => 6
         | (4, 13) => 5
         | (5, 20) => 2
         | _ => 500
         end in
      let weight_boolean := match (size,last_callsite) with 
         | (1, 11) => 118
         | (1, 12) => 83
         | (1, 13) => 92
         | (2, 11) => 85
         | (2, 12) => 26
         | (2, 13) => 20
         | (3, 11) => 85
         | (3, 12) => 7
         | (3, 13) => 10
         | (4, 11) => 206
         | (4, 12) => 5
         | (4, 13) => 5
         | (5, 20) => 2
         | _ => 500
         end in
      let weight_abs := match (size,last_callsite) with 
         | (1, 11) => 846
         | (1, 12) => 869
         | (1, 13) => 854
         | (2, 11) => 606
         | (2, 12) => 415
         | (2, 13) => 417
         | (3, 11) => 540
         | (3, 12) => 42
         | (3, 13) => 48
         | (4, 11) => 558
         | (4, 12) => 16
         | (4, 13) => 18
         | (5, 20) => 4
         | _ => 500
         end in
      let weight_app := match (size,last_callsite) with 
         | (1, 11) => 467
         | (1, 12) => 327
         | (1, 13) => 459
         | (2, 11) => 835
         | (2, 12) => 898
         | (2, 13) => 902
         | (3, 11) => 846
         | (3, 12) => 934
         | (3, 13) => 932
         | (4, 11) => 775
         | (4, 12) => 940
         | (4, 13) => 940
         | (5, 20) => 950
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


