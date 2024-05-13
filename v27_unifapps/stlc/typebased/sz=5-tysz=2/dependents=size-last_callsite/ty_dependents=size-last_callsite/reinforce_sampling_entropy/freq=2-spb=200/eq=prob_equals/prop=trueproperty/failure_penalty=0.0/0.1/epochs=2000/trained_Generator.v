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
         | (1, 14) => 929
         | (1, 15) => 54
         | (2, 10) => 77
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
         | (0, 11) => 912
         | (0, 12) => 137
         | (0, 13) => 138
         | _ => 500
         end in
      freq [ (weight_var, bindGen arbitrary (fun p0 : nat => returnGen (Var p0)));
      (1000 - weight_var, bindGen arbitrary (fun p0 : bool => returnGen (Bool p0)))]
  | S size' =>
      let weight_var := match (size,last_callsite) with 
         | (1, 11) => 275
         | (1, 12) => 380
         | (1, 13) => 265
         | (2, 11) => 45
         | (2, 12) => 29
         | (2, 13) => 4
         | (3, 11) => 58
         | (3, 12) => 1
         | (3, 13) => 1
         | (4, 11) => 224
         | (4, 12) => 1
         | (4, 13) => 0
         | (5, 20) => 0
         | _ => 500
         end in
      let weight_boolean := match (size,last_callsite) with 
         | (1, 11) => 285
         | (1, 12) => 305
         | (1, 13) => 220
         | (2, 11) => 49
         | (2, 12) => 9
         | (2, 13) => 18
         | (3, 11) => 62
         | (3, 12) => 1
         | (3, 13) => 1
         | (4, 11) => 228
         | (4, 12) => 0
         | (4, 13) => 0
         | (5, 20) => 0
         | _ => 500
         end in
      let weight_abs := match (size,last_callsite) with 
         | (1, 11) => 912
         | (1, 12) => 952
         | (1, 13) => 949
         | (2, 11) => 434
         | (2, 12) => 295
         | (2, 13) => 219
         | (3, 11) => 393
         | (3, 12) => 39
         | (3, 13) => 37
         | (4, 11) => 565
         | (4, 12) => 1
         | (4, 13) => 1
         | (5, 20) => 0
         | _ => 500
         end in
      let weight_app := match (size,last_callsite) with 
         | (1, 11) => 627
         | (1, 12) => 712
         | (1, 13) => 810
         | (2, 11) => 892
         | (2, 12) => 941
         | (2, 13) => 947
         | (3, 11) => 880
         | (3, 12) => 952
         | (3, 13) => 950
         | (4, 11) => 761
         | (4, 12) => 959
         | (4, 13) => 959
         | (5, 20) => 963
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


