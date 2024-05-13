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
         | (1, 14) => 711
         | (1, 15) => 288
         | (2, 10) => 193
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
         | (0, 11) => 560
         | (0, 12) => 787
         | (0, 13) => 213
         | _ => 500
         end in
      freq [ (weight_var, bindGen arbitrary (fun p0 : nat => returnGen (Var p0)));
      (1000 - weight_var, bindGen arbitrary (fun p0 : bool => returnGen (Bool p0)))]
  | S size' =>
      let weight_var := match (size,last_callsite) with 
         | (1, 11) => 518
         | (1, 12) => 498
         | (1, 13) => 480
         | (2, 11) => 6
         | (2, 12) => 494
         | (2, 13) => 497
         | (3, 11) => 3
         | (3, 12) => 496
         | (3, 13) => 495
         | (4, 11) => 0
         | (4, 12) => 483
         | (4, 13) => 483
         | (5, 20) => 0
         | _ => 500
         end in
      let weight_boolean := match (size,last_callsite) with 
         | (1, 11) => 160
         | (1, 12) => 473
         | (1, 13) => 551
         | (2, 11) => 33
         | (2, 12) => 484
         | (2, 13) => 520
         | (3, 11) => 5
         | (3, 12) => 491
         | (3, 13) => 514
         | (4, 11) => 2
         | (4, 12) => 483
         | (4, 13) => 543
         | (5, 20) => 1
         | _ => 500
         end in
      let weight_abs := match (size,last_callsite) with 
         | (1, 11) => 918
         | (1, 12) => 547
         | (1, 13) => 486
         | (2, 11) => 948
         | (2, 12) => 536
         | (2, 13) => 490
         | (3, 11) => 954
         | (3, 12) => 516
         | (3, 13) => 499
         | (4, 11) => 960
         | (4, 12) => 547
         | (4, 13) => 488
         | (5, 20) => 962
         | _ => 500
         end in
      let weight_app := match (size,last_callsite) with 
         | (1, 11) => 1
         | (1, 12) => 479
         | (1, 13) => 480
         | (2, 11) => 0
         | (2, 12) => 484
         | (2, 13) => 493
         | (3, 11) => 0
         | (3, 12) => 497
         | (3, 13) => 491
         | (4, 11) => 0
         | (4, 12) => 483
         | (4, 13) => 483
         | (5, 20) => 0
         | _ => 500
         end in
      freq [
      (weight_var,

         let weight_1 := match (size,last_callsite) with 
         | (1, 11) => 503
         | (1, 12) => 488
         | (1, 13) => 494
         | (2, 11) => 141
         | (2, 12) => 511
         | (2, 13) => 501
         | (3, 11) => 511
         | (3, 12) => 495
         | (3, 13) => 496
         | (4, 11) => 265
         | (4, 12) => 500
         | (4, 13) => 500
         | (5, 20) => 500
         | _ => 500
         end in
        bindGen (freq [ (weight_1, returnGen 1); (1000-weight_1, returnGen 0)])
        (fun n1 : nat =>  
         let weight_2 := match (size,last_callsite) with 
         | (1, 11) => 381
         | (1, 12) => 488
         | (1, 13) => 494
         | (2, 11) => 235
         | (2, 12) => 489
         | (2, 13) => 487
         | (3, 11) => 42
         | (3, 12) => 495
         | (3, 13) => 496
         | (4, 11) => 265
         | (4, 12) => 500
         | (4, 13) => 500
         | (5, 20) => 500
         | _ => 500
         end in
        bindGen (freq [ (weight_2, returnGen 2); (1000-weight_2, returnGen 0)])
        (fun n2 : nat =>  
         let weight_4 := match (size,last_callsite) with 
         | (1, 11) => 1
         | (1, 12) => 476
         | (1, 13) => 494
         | (2, 11) => 20
         | (2, 12) => 489
         | (2, 13) => 487
         | (3, 11) => 42
         | (3, 12) => 495
         | (3, 13) => 496
         | (4, 11) => 265
         | (4, 12) => 500
         | (4, 13) => 500
         | (5, 20) => 500
         | _ => 500
         end in
        bindGen (freq [ (weight_4, returnGen 4); (1000-weight_4, returnGen 0)])
        (fun n4 : nat =>  
         let weight_8 := match (size,last_callsite) with 
         | (1, 11) => 1
         | (1, 12) => 476
         | (1, 13) => 494
         | (2, 11) => 20
         | (2, 12) => 489
         | (2, 13) => 487
         | (3, 11) => 42
         | (3, 12) => 495
         | (3, 13) => 496
         | (4, 11) => 265
         | (4, 12) => 500
         | (4, 13) => 500
         | (5, 20) => 500
         | _ => 500
         end in
        bindGen (freq [ (weight_8, returnGen 8); (1000-weight_8, returnGen 0)])
        (fun n8 : nat =>  
        let p1 := n1+n2+n4+n8 in
        returnGen (Var p1))
      ))));
      (weight_boolean,
        let weight_true := match (size,last_callsite) with 
         | (1, 11) => 529
         | (1, 12) => 500
         | (1, 13) => 534
         | (2, 11) => 599
         | (2, 12) => 500
         | (2, 13) => 499
         | (3, 11) => 507
         | (3, 12) => 500
         | (3, 13) => 511
         | (4, 11) => 552
         | (4, 12) => 500
         | (4, 13) => 494
         | (5, 20) => 480
         | _ => 500
         end in
        freq [ (weight_true, returnGen (Bool true)); (1000 - weight_true, returnGen (Bool false))]
      );
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


