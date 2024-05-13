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
         | (1, 14) => 499
         | (1, 15) => 504
         | (2, 10) => 365
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
         | (0, 11) => 496
         | (0, 12) => 504
         | (0, 13) => 504
         | _ => 500
         end in
      freq [ (weight_var, bindGen arbitrary (fun p0 : nat => returnGen (Var p0)));
      (1000 - weight_var, bindGen arbitrary (fun p0 : bool => returnGen (Bool p0)))]
  | S size' =>
      let weight_var := match (size,last_callsite) with 
         | (1, 11) => 495
         | (1, 12) => 489
         | (1, 13) => 488
         | (2, 11) => 473
         | (2, 12) => 472
         | (2, 13) => 472
         | (3, 11) => 454
         | (3, 12) => 448
         | (3, 13) => 448
         | (4, 11) => 429
         | (4, 12) => 414
         | (4, 13) => 417
         | (5, 20) => 226
         | _ => 500
         end in
      let weight_boolean := match (size,last_callsite) with 
         | (1, 11) => 492
         | (1, 12) => 490
         | (1, 13) => 492
         | (2, 11) => 478
         | (2, 12) => 475
         | (2, 13) => 473
         | (3, 11) => 452
         | (3, 12) => 449
         | (3, 13) => 453
         | (4, 11) => 430
         | (4, 12) => 416
         | (4, 13) => 416
         | (5, 20) => 226
         | _ => 500
         end in
      let weight_abs := match (size,last_callsite) with 
         | (1, 11) => 510
         | (1, 12) => 515
         | (1, 13) => 513
         | (2, 11) => 519
         | (2, 12) => 524
         | (2, 13) => 519
         | (3, 11) => 526
         | (3, 12) => 526
         | (3, 13) => 530
         | (4, 11) => 533
         | (4, 12) => 538
         | (4, 13) => 542
         | (5, 20) => 569
         | _ => 500
         end in
      let weight_app := match (size,last_callsite) with 
         | (1, 11) => 502
         | (1, 12) => 506
         | (1, 13) => 506
         | (2, 11) => 528
         | (2, 12) => 527
         | (2, 13) => 533
         | (3, 11) => 559
         | (3, 12) => 567
         | (3, 13) => 560
         | (4, 11) => 589
         | (4, 12) => 604
         | (4, 13) => 599
         | (5, 20) => 758
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


