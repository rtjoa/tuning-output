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
         | (1, 14) => 14
         | (1, 15) => 871
         | (2, 10) => 964
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
         | (0, 11) => 69
         | (0, 12) => 972
         | (0, 13) => 4
         | _ => 500
         end in
      freq [ (weight_var, bindGen arbitrary (fun p0 : nat => returnGen (Var p0)));
      (1000 - weight_var, bindGen arbitrary (fun p0 : bool => returnGen (Bool p0)))]
  | S size' =>
      let weight_var := match (size,last_callsite) with 
         | (1, 11) => 776
         | (1, 12) => 826
         | (1, 13) => 39
         | (2, 11) => 11
         | (2, 12) => 28
         | (2, 13) => 3
         | (3, 11) => 7
         | (3, 12) => 0
         | (3, 13) => 648
         | (4, 11) => 148
         | (4, 12) => 0
         | (4, 13) => 0
         | (5, 20) => 0
         | _ => 500
         end in
      let weight_boolean := match (size,last_callsite) with 
         | (1, 11) => 939
         | (1, 12) => 77
         | (1, 13) => 858
         | (2, 11) => 38
         | (2, 12) => 705
         | (2, 13) => 602
         | (3, 11) => 18
         | (3, 12) => 1
         | (3, 13) => 1
         | (4, 11) => 123
         | (4, 12) => 0
         | (4, 13) => 1
         | (5, 20) => 0
         | _ => 500
         end in
      let weight_abs := match (size,last_callsite) with 
         | (1, 11) => 829
         | (1, 12) => 995
         | (1, 13) => 45
         | (2, 11) => 76
         | (2, 12) => 15
         | (2, 13) => 25
         | (3, 11) => 135
         | (3, 12) => 17
         | (3, 13) => 37
         | (4, 11) => 453
         | (4, 12) => 30
         | (4, 13) => 4
         | (5, 20) => 0
         | _ => 500
         end in
      let weight_app := match (size,last_callsite) with 
         | (1, 11) => 900
         | (1, 12) => 924
         | (1, 13) => 995
         | (2, 11) => 961
         | (2, 12) => 999
         | (2, 13) => 999
         | (3, 11) => 936
         | (3, 12) => 975
         | (3, 13) => 998
         | (4, 11) => 846
         | (4, 12) => 960
         | (4, 13) => 962
         | (5, 20) => 969
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


