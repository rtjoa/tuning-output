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
         | (1, 14) => 511
         | (1, 15) => 520
         | (2, 10) => 202
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
         | (0, 11) => 490
         | (0, 12) => 603
         | (0, 13) => 397
         | _ => 500
         end in
      freq [ (weight_var, bindGen arbitrary (fun p0 : nat => returnGen (Var p0)));
      (1000 - weight_var, bindGen arbitrary (fun p0 : bool => returnGen (Bool p0)))]
  | S size' =>
      let weight_var := match (size,last_callsite) with 
         | (1, 11) => 110
         | (1, 12) => 494
         | (1, 13) => 492
         | (2, 11) => 41
         | (2, 12) => 496
         | (2, 13) => 494
         | (3, 11) => 14
         | (3, 12) => 494
         | (3, 13) => 493
         | (4, 11) => 6
         | (4, 12) => 487
         | (4, 13) => 487
         | (5, 20) => 4
         | _ => 500
         end in
      let weight_boolean := match (size,last_callsite) with 
         | (1, 11) => 582
         | (1, 12) => 486
         | (1, 13) => 518
         | (2, 11) => 246
         | (2, 12) => 490
         | (2, 13) => 520
         | (3, 11) => 66
         | (3, 12) => 490
         | (3, 13) => 520
         | (4, 11) => 27
         | (4, 12) => 487
         | (4, 13) => 534
         | (5, 20) => 14
         | _ => 500
         end in
      let weight_abs := match (size,last_callsite) with 
         | (1, 11) => 857
         | (1, 12) => 527
         | (1, 13) => 500
         | (2, 11) => 909
         | (2, 12) => 521
         | (2, 13) => 495
         | (3, 11) => 929
         | (3, 12) => 524
         | (3, 13) => 496
         | (4, 11) => 938
         | (4, 12) => 537
         | (4, 13) => 491
         | (5, 20) => 942
         | _ => 500
         end in
      let weight_app := match (size,last_callsite) with 
         | (1, 11) => 28
         | (1, 12) => 492
         | (1, 13) => 489
         | (2, 11) => 13
         | (2, 12) => 492
         | (2, 13) => 490
         | (3, 11) => 7
         | (3, 12) => 492
         | (3, 13) => 491
         | (4, 11) => 5
         | (4, 12) => 488
         | (4, 13) => 487
         | (5, 20) => 4
         | _ => 500
         end in
      freq [
      (weight_var,

         let weight_1 := match (size,last_callsite) with 
         | (1, 11) => 470
         | (1, 12) => 495
         | (1, 13) => 498
         | (2, 11) => 316
         | (2, 12) => 501
         | (2, 13) => 502
         | (3, 11) => 482
         | (3, 12) => 496
         | (3, 13) => 497
         | (4, 11) => 350
         | (4, 12) => 500
         | (4, 13) => 500
         | (5, 20) => 500
         | _ => 500
         end in
        bindGen (freq [ (weight_1, returnGen 1); (1000-weight_1, returnGen 0)])
        (fun n1 : nat =>  
         let weight_2 := match (size,last_callsite) with 
         | (1, 11) => 524
         | (1, 12) => 497
         | (1, 13) => 497
         | (2, 11) => 339
         | (2, 12) => 495
         | (2, 13) => 496
         | (3, 11) => 213
         | (3, 12) => 496
         | (3, 13) => 497
         | (4, 11) => 350
         | (4, 12) => 500
         | (4, 13) => 500
         | (5, 20) => 500
         | _ => 500
         end in
        bindGen (freq [ (weight_2, returnGen 2); (1000-weight_2, returnGen 0)])
        (fun n2 : nat =>  
         let weight_4 := match (size,last_callsite) with 
         | (1, 11) => 133
         | (1, 12) => 493
         | (1, 13) => 494
         | (2, 11) => 156
         | (2, 12) => 495
         | (2, 13) => 496
         | (3, 11) => 213
         | (3, 12) => 496
         | (3, 13) => 497
         | (4, 11) => 350
         | (4, 12) => 500
         | (4, 13) => 500
         | (5, 20) => 500
         | _ => 500
         end in
        bindGen (freq [ (weight_4, returnGen 4); (1000-weight_4, returnGen 0)])
        (fun n4 : nat =>  
         let weight_8 := match (size,last_callsite) with 
         | (1, 11) => 133
         | (1, 12) => 493
         | (1, 13) => 494
         | (2, 11) => 156
         | (2, 12) => 495
         | (2, 13) => 496
         | (3, 11) => 213
         | (3, 12) => 496
         | (3, 13) => 497
         | (4, 11) => 350
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
         | (1, 11) => 485
         | (1, 12) => 500
         | (1, 13) => 494
         | (2, 11) => 507
         | (2, 12) => 500
         | (2, 13) => 500
         | (3, 11) => 504
         | (3, 12) => 500
         | (3, 13) => 502
         | (4, 11) => 518
         | (4, 12) => 500
         | (4, 13) => 504
         | (5, 20) => 492
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


