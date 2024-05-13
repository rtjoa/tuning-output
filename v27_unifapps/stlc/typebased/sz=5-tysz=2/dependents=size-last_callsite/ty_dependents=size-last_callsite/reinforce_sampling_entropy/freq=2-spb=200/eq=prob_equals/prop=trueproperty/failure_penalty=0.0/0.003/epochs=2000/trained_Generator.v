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
         | (1, 14) => 519
         | (1, 15) => 482
         | (2, 10) => 199
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
         | (0, 11) => 505
         | (0, 12) => 495
         | (0, 13) => 497
         | _ => 500
         end in
      freq [ (weight_var, bindGen arbitrary (fun p0 : nat => returnGen (Var p0)));
      (1000 - weight_var, bindGen arbitrary (fun p0 : bool => returnGen (Bool p0)))]
  | S size' =>
      let weight_var := match (size,last_callsite) with 
         | (1, 11) => 457
         | (1, 12) => 433
         | (1, 13) => 443
         | (2, 11) => 348
         | (2, 12) => 315
         | (2, 13) => 327
         | (3, 11) => 270
         | (3, 12) => 234
         | (3, 13) => 229
         | (4, 11) => 269
         | (4, 12) => 144
         | (4, 13) => 144
         | (5, 20) => 35
         | _ => 500
         end in
      let weight_boolean := match (size,last_callsite) with 
         | (1, 11) => 433
         | (1, 12) => 442
         | (1, 13) => 436
         | (2, 11) => 335
         | (2, 12) => 318
         | (2, 13) => 333
         | (3, 11) => 270
         | (3, 12) => 233
         | (3, 13) => 233
         | (4, 11) => 269
         | (4, 12) => 146
         | (4, 13) => 146
         | (5, 20) => 35
         | _ => 500
         end in
      let weight_abs := match (size,last_callsite) with 
         | (1, 11) => 580
         | (1, 12) => 584
         | (1, 13) => 579
         | (2, 11) => 607
         | (2, 12) => 602
         | (2, 13) => 602
         | (3, 11) => 573
         | (3, 12) => 595
         | (3, 13) => 602
         | (4, 11) => 563
         | (4, 12) => 555
         | (4, 13) => 555
         | (5, 20) => 181
         | _ => 500
         end in
      let weight_app := match (size,last_callsite) with 
         | (1, 11) => 517
         | (1, 12) => 524
         | (1, 13) => 528
         | (2, 11) => 635
         | (2, 12) => 666
         | (2, 13) => 652
         | (3, 11) => 725
         | (3, 12) => 742
         | (3, 13) => 739
         | (4, 11) => 731
         | (4, 12) => 811
         | (4, 13) => 811
         | (5, 20) => 906
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


