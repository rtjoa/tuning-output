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
         | (1, 14) => 500
         | (1, 15) => 500
         | (2, 10) => 500
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
         | (0, 11) => 500
         | (0, 12) => 500
         | (0, 13) => 500
         | _ => 500
         end in
      freq [ (weight_var, bindGen arbitrary (fun p0 : nat => returnGen (Var p0)));
      (1000 - weight_var, bindGen arbitrary (fun p0 : bool => returnGen (Bool p0)))]
  | S size' =>
      let weight1 := match (size,last_callsite) with 
         | (1, 11) => 500
         | (1, 12) => 500
         | (1, 13) => 500
         | (2, 11) => 500
         | (2, 12) => 500
         | (2, 13) => 500
         | (3, 20) => 500
         | _ => 500
         end in
      let weight2 := match (size,last_callsite) with 
         | (1, 11) => 500
         | (1, 12) => 500
         | (1, 13) => 500
         | (2, 11) => 500
         | (2, 12) => 500
         | (2, 13) => 500
         | (3, 20) => 500
         | _ => 500
         end in
      let weight3 := match (size,last_callsite) with 
         | (1, 11) => 500
         | (1, 12) => 500
         | (1, 13) => 500
         | (2, 11) => 500
         | (2, 12) => 500
         | (2, 13) => 500
         | (3, 20) => 500
         | _ => 500
         end in
      let weight4 := match (size,last_callsite) with 
         | (1, 11) => 500
         | (1, 12) => 500
         | (1, 13) => 500
         | (2, 11) => 500
         | (2, 12) => 500
         | (2, 13) => 500
         | (3, 20) => 500
         | _ => 500
         end in
      freq [ (weight1,
      bindGen arbitrary (fun p0 : nat => returnGen (Var p0)));
      (weight2, bindGen arbitrary (fun p0 : bool => returnGen (Bool p0)));
      (weight3,
      bindGen (manual_gen_type 2 10)
        (fun p0 : Typ =>
         bindGen (manual_gen_expr size' 11)
           (fun p1 : Expr => returnGen (Abs p0 p1))));
      (weight4,
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


