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
         | (1, 14) => 964
         | (1, 15) => 653
         | (2, 10) => 967
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
         | (0, 11) => 39
         | (0, 12) => 962
         | (0, 13) => 55
         | _ => 500
         end in
      freq [ (weight_var, bindGen arbitrary (fun p0 : nat => returnGen (Var p0)));
      (1000 - weight_var, bindGen arbitrary (fun p0 : bool => returnGen (Bool p0)))]
  | S size' =>
      let weight_var := match (size,last_callsite) with 
         | (1, 11) => 622
         | (1, 12) => 681
         | (1, 13) => 577
         | (2, 11) => 28
         | (2, 12) => 9
         | (2, 13) => 37
         | (3, 11) => 50
         | (3, 12) => 1
         | (3, 13) => 1
         | (4, 11) => 165
         | (4, 12) => 0
         | (4, 13) => 0
         | (5, 20) => 0
         | _ => 500
         end in
      let weight_boolean := match (size,last_callsite) with 
         | (1, 11) => 899
         | (1, 12) => 832
         | (1, 13) => 644
         | (2, 11) => 9
         | (2, 12) => 6
         | (2, 13) => 6
         | (3, 11) => 40
         | (3, 12) => 6
         | (3, 13) => 0
         | (4, 11) => 158
         | (4, 12) => 0
         | (4, 13) => 0
         | (5, 20) => 0
         | _ => 500
         end in
      let weight_abs := match (size,last_callsite) with 
         | (1, 11) => 970
         | (1, 12) => 975
         | (1, 13) => 978
         | (2, 11) => 157
         | (2, 12) => 514
         | (2, 13) => 515
         | (3, 11) => 235
         | (3, 12) => 10
         | (3, 13) => 7
         | (4, 11) => 601
         | (4, 12) => 2
         | (4, 13) => 1
         | (5, 20) => 0
         | _ => 500
         end in
      let weight_app := match (size,last_callsite) with 
         | (1, 11) => 937
         | (1, 12) => 981
         | (1, 13) => 981
         | (2, 11) => 932
         | (2, 12) => 987
         | (2, 13) => 987
         | (3, 11) => 901
         | (3, 12) => 950
         | (3, 13) => 960
         | (4, 11) => 792
         | (4, 12) => 961
         | (4, 13) => 962
         | (5, 20) => 966
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


