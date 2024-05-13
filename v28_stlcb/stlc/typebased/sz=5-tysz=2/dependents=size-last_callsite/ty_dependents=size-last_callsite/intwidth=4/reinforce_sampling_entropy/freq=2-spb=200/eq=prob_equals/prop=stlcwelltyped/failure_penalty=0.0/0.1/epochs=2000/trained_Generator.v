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
         | (1, 14) => 549
         | (1, 15) => 562
         | (2, 10) => 214
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
         | (0, 11) => 453
         | (0, 12) => 677
         | (0, 13) => 323
         | _ => 500
         end in
      freq [ (weight_var, bindGen arbitrary (fun p0 : nat => returnGen (Var p0)));
      (1000 - weight_var, bindGen arbitrary (fun p0 : bool => returnGen (Bool p0)))]
  | S size' =>
      let weight_var := match (size,last_callsite) with 
         | (1, 11) => 332
         | (1, 12) => 497
         | (1, 13) => 493
         | (2, 11) => 7
         | (2, 12) => 493
         | (2, 13) => 487
         | (3, 11) => 1
         | (3, 12) => 490
         | (3, 13) => 489
         | (4, 11) => 1
         | (4, 12) => 484
         | (4, 13) => 484
         | (5, 20) => 1
         | _ => 500
         end in
      let weight_boolean := match (size,last_callsite) with 
         | (1, 11) => 218
         | (1, 12) => 485
         | (1, 13) => 523
         | (2, 11) => 28
         | (2, 12) => 485
         | (2, 13) => 537
         | (3, 11) => 8
         | (3, 12) => 487
         | (3, 13) => 528
         | (4, 11) => 3
         | (4, 12) => 484
         | (4, 13) => 542
         | (5, 20) => 2
         | _ => 500
         end in
      let weight_abs := match (size,last_callsite) with 
         | (1, 11) => 905
         | (1, 12) => 525
         | (1, 13) => 493
         | (2, 11) => 944
         | (2, 12) => 533
         | (2, 13) => 490
         | (3, 11) => 952
         | (3, 12) => 530
         | (3, 13) => 495
         | (4, 11) => 955
         | (4, 12) => 546
         | (4, 13) => 488
         | (5, 20) => 956
         | _ => 500
         end in
      let weight_app := match (size,last_callsite) with 
         | (1, 11) => 2
         | (1, 12) => 492
         | (1, 13) => 489
         | (2, 11) => 1
         | (2, 12) => 487
         | (2, 13) => 485
         | (3, 11) => 1
         | (3, 12) => 491
         | (3, 13) => 487
         | (4, 11) => 1
         | (4, 12) => 484
         | (4, 13) => 484
         | (5, 20) => 1
         | _ => 500
         end in
      freq [
      (weight_var,

         let weight_1 := match (size,last_callsite) with 
         | (1, 11) => 522
         | (1, 12) => 492
         | (1, 13) => 491
         | (2, 11) => 269
         | (2, 12) => 498
         | (2, 13) => 498
         | (3, 11) => 474
         | (3, 12) => 497
         | (3, 13) => 499
         | (4, 11) => 310
         | (4, 12) => 500
         | (4, 13) => 500
         | (5, 20) => 500
         | _ => 500
         end in
        bindGen (freq [ (weight_1, returnGen 1); (1000-weight_1, returnGen 0)])
        (fun n1 : nat =>  
         let weight_2 := match (size,last_callsite) with 
         | (1, 11) => 569
         | (1, 12) => 504
         | (1, 13) => 500
         | (2, 11) => 207
         | (2, 12) => 492
         | (2, 13) => 498
         | (3, 11) => 167
         | (3, 12) => 497
         | (3, 13) => 499
         | (4, 11) => 310
         | (4, 12) => 500
         | (4, 13) => 500
         | (5, 20) => 500
         | _ => 500
         end in
        bindGen (freq [ (weight_2, returnGen 2); (1000-weight_2, returnGen 0)])
        (fun n2 : nat =>  
         let weight_4 := match (size,last_callsite) with 
         | (1, 11) => 4
         | (1, 12) => 488
         | (1, 13) => 491
         | (2, 11) => 62
         | (2, 12) => 492
         | (2, 13) => 498
         | (3, 11) => 167
         | (3, 12) => 497
         | (3, 13) => 499
         | (4, 11) => 310
         | (4, 12) => 500
         | (4, 13) => 500
         | (5, 20) => 500
         | _ => 500
         end in
        bindGen (freq [ (weight_4, returnGen 4); (1000-weight_4, returnGen 0)])
        (fun n4 : nat =>  
         let weight_8 := match (size,last_callsite) with 
         | (1, 11) => 4
         | (1, 12) => 488
         | (1, 13) => 491
         | (2, 11) => 62
         | (2, 12) => 492
         | (2, 13) => 498
         | (3, 11) => 167
         | (3, 12) => 497
         | (3, 13) => 499
         | (4, 11) => 310
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
         | (1, 11) => 457
         | (1, 12) => 500
         | (1, 13) => 509
         | (2, 11) => 600
         | (2, 12) => 500
         | (2, 13) => 506
         | (3, 11) => 476
         | (3, 12) => 500
         | (3, 13) => 493
         | (4, 11) => 553
         | (4, 12) => 500
         | (4, 13) => 502
         | (5, 20) => 505
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


