From QuickChick Require Import QuickChick. Import QcNotation.
From Coq Require Import Bool ZArith List. Import ListNotations.
From ExtLib Require Import Monad.
From ExtLib.Data.Monads Require Import OptionMonad.
Import MonadNotation.

From STLC Require Import Impl Spec.

Fixpoint manual_gen_typ (size : nat) (stack1 : nat) (stack2 : nat) : G Typ :=
  match size with
  | 0 => returnGen TBool
  | S size' =>
      let weight_tbool := match (size,(stack1, stack2)) with 
         | (1, (10, 14)) => 500
         | (1, (10, 15)) => 500
         | (2, (0, 10)) => 500
         | (2, (11, 10)) => 500
         | (2, (12, 10)) => 500
         | (2, (13, 10)) => 500
         | _ => 500
         end in
      freq [ (weight_tbool, returnGen TBool);
      (1000 - weight_tbool,
      bindGen (manual_gen_typ size' (stack2 : nat) 14)
        (fun p0 : Typ =>
         bindGen (manual_gen_typ size' (stack2 : nat) 15)
           (fun p1 : Typ => returnGen (TFun p0 p1))))]
  end.

Fixpoint manual_gen_expr (size : nat) (stack1 : nat) (stack2 : nat) : G Expr :=
  match size with
  | 0 =>
      let weight_var := match (size,(stack1, stack2)) with 
         | (0, (11, 11)) => 497
         | (0, (11, 12)) => 646
         | (0, (11, 13)) => 354
         | (0, (12, 11)) => 550
         | (0, (12, 12)) => 507
         | (0, (12, 13)) => 493
         | (0, (13, 11)) => 507
         | (0, (13, 12)) => 508
         | (0, (13, 13)) => 492
         | _ => 500
         end in
      freq [ (weight_var, bindGen arbitrary (fun p0 : nat => returnGen (Var p0)));
      (1000 - weight_var, bindGen arbitrary (fun p0 : bool => returnGen (Bool p0)))]
  | S size' =>
      let weight_var := match (size,(stack1, stack2)) with 
         | (1, (11, 11)) => 5
         | (1, (11, 12)) => 447
         | (1, (11, 13)) => 443
         | (1, (12, 11)) => 486
         | (1, (12, 12)) => 500
         | (1, (12, 13)) => 500
         | (1, (13, 11)) => 500
         | (1, (13, 12)) => 500
         | (1, (13, 13)) => 500
         | (2, (11, 11)) => 3
         | (2, (11, 12)) => 487
         | (2, (11, 13)) => 484
         | (2, (12, 11)) => 471
         | (2, (12, 12)) => 499
         | (2, (12, 13)) => 499
         | (2, (13, 11)) => 499
         | (2, (13, 12)) => 500
         | (2, (13, 13)) => 500
         | (3, (11, 11)) => 2
         | (3, (11, 12)) => 473
         | (3, (11, 13)) => 471
         | (3, (12, 11)) => 465
         | (3, (12, 12)) => 500
         | (3, (12, 13)) => 500
         | (3, (13, 11)) => 498
         | (3, (13, 12)) => 499
         | (3, (13, 13)) => 499
         | (4, (0, 11)) => 1
         | (4, (0, 12)) => 465
         | (4, (0, 13)) => 465
         | (5, (0, 0)) => 1
         | _ => 500
         end in
      let weight_boolean := match (size,(stack1, stack2)) with 
         | (1, (11, 11)) => 458
         | (1, (11, 12)) => 436
         | (1, (11, 13)) => 625
         | (1, (12, 11)) => 511
         | (1, (12, 12)) => 500
         | (1, (12, 13)) => 500
         | (1, (13, 11)) => 500
         | (1, (13, 12)) => 500
         | (1, (13, 13)) => 500
         | (2, (11, 11)) => 308
         | (2, (11, 12)) => 484
         | (2, (11, 13)) => 545
         | (2, (12, 11)) => 536
         | (2, (12, 12)) => 499
         | (2, (12, 13)) => 503
         | (2, (13, 11)) => 502
         | (2, (13, 12)) => 500
         | (2, (13, 13)) => 500
         | (3, (11, 11)) => 229
         | (3, (11, 12)) => 471
         | (3, (11, 13)) => 576
         | (3, (12, 11)) => 544
         | (3, (12, 12)) => 500
         | (3, (12, 13)) => 500
         | (3, (13, 11)) => 505
         | (3, (13, 12)) => 499
         | (3, (13, 13)) => 503
         | (4, (0, 11)) => 173
         | (4, (0, 12)) => 465
         | (4, (0, 13)) => 584
         | (5, (0, 0)) => 152
         | _ => 500
         end in
      let weight_abs := match (size,(stack1, stack2)) with 
         | (1, (11, 11)) => 920
         | (1, (11, 12)) => 638
         | (1, (11, 13)) => 459
         | (1, (12, 11)) => 519
         | (1, (12, 12)) => 500
         | (1, (12, 13)) => 500
         | (1, (13, 11)) => 500
         | (1, (13, 12)) => 500
         | (1, (13, 13)) => 500
         | (2, (11, 11)) => 930
         | (2, (11, 12)) => 543
         | (2, (11, 13)) => 484
         | (2, (12, 11)) => 515
         | (2, (12, 12)) => 503
         | (2, (12, 13)) => 499
         | (2, (13, 11)) => 499
         | (2, (13, 12)) => 500
         | (2, (13, 13)) => 500
         | (3, (11, 11)) => 937
         | (3, (11, 12)) => 573
         | (3, (11, 13)) => 474
         | (3, (12, 11)) => 523
         | (3, (12, 12)) => 500
         | (3, (12, 13)) => 500
         | (3, (13, 11)) => 498
         | (3, (13, 12)) => 503
         | (3, (13, 13)) => 499
         | (4, (0, 11)) => 940
         | (4, (0, 12)) => 592
         | (4, (0, 13)) => 471
         | (5, (0, 0)) => 942
         | _ => 500
         end in
      let weight_app := match (size,(stack1, stack2)) with 
         | (1, (11, 11)) => 6
         | (1, (11, 12)) => 443
         | (1, (11, 13)) => 444
         | (1, (12, 11)) => 484
         | (1, (12, 12)) => 500
         | (1, (12, 13)) => 500
         | (1, (13, 11)) => 500
         | (1, (13, 12)) => 500
         | (1, (13, 13)) => 500
         | (2, (11, 11)) => 4
         | (2, (11, 12)) => 484
         | (2, (11, 13)) => 484
         | (2, (12, 11)) => 476
         | (2, (12, 12)) => 499
         | (2, (12, 13)) => 499
         | (2, (13, 11)) => 499
         | (2, (13, 12)) => 500
         | (2, (13, 13)) => 500
         | (3, (11, 11)) => 2
         | (3, (11, 12)) => 475
         | (3, (11, 13)) => 471
         | (3, (12, 11)) => 465
         | (3, (12, 12)) => 500
         | (3, (12, 13)) => 500
         | (3, (13, 11)) => 498
         | (3, (13, 12)) => 499
         | (3, (13, 13)) => 499
         | (4, (0, 11)) => 2
         | (4, (0, 12)) => 465
         | (4, (0, 13)) => 468
         | (5, (0, 0)) => 1
         | _ => 500
         end in
      freq [
      (weight_var,

         let weight_1 := match (size,(stack1, stack2)) with 
         | (1, (11, 11)) => 500
         | (1, (11, 12)) => 500
         | (1, (11, 13)) => 500
         | (1, (12, 11)) => 500
         | (1, (12, 12)) => 500
         | (1, (12, 13)) => 500
         | (1, (13, 11)) => 500
         | (1, (13, 12)) => 500
         | (1, (13, 13)) => 500
         | (2, (11, 11)) => 500
         | (2, (11, 12)) => 500
         | (2, (11, 13)) => 500
         | (2, (12, 11)) => 500
         | (2, (12, 12)) => 500
         | (2, (12, 13)) => 500
         | (2, (13, 11)) => 500
         | (2, (13, 12)) => 500
         | (2, (13, 13)) => 500
         | (3, (11, 11)) => 500
         | (3, (11, 12)) => 500
         | (3, (11, 13)) => 500
         | (3, (12, 11)) => 500
         | (3, (12, 12)) => 500
         | (3, (12, 13)) => 500
         | (3, (13, 11)) => 500
         | (3, (13, 12)) => 500
         | (3, (13, 13)) => 500
         | (4, (0, 11)) => 500
         | (4, (0, 12)) => 500
         | (4, (0, 13)) => 500
         | (5, (0, 0)) => 500
         | _ => 500
         end in
        bindGen (freq [ (weight_1, returnGen 1); (1000-weight_1, returnGen 0)])
        (fun n1 : nat =>  
         let weight_2 := match (size,(stack1, stack2)) with 
         | (1, (11, 11)) => 500
         | (1, (11, 12)) => 500
         | (1, (11, 13)) => 500
         | (1, (12, 11)) => 500
         | (1, (12, 12)) => 500
         | (1, (12, 13)) => 500
         | (1, (13, 11)) => 500
         | (1, (13, 12)) => 500
         | (1, (13, 13)) => 500
         | (2, (11, 11)) => 500
         | (2, (11, 12)) => 500
         | (2, (11, 13)) => 500
         | (2, (12, 11)) => 500
         | (2, (12, 12)) => 500
         | (2, (12, 13)) => 500
         | (2, (13, 11)) => 500
         | (2, (13, 12)) => 500
         | (2, (13, 13)) => 500
         | (3, (11, 11)) => 500
         | (3, (11, 12)) => 500
         | (3, (11, 13)) => 500
         | (3, (12, 11)) => 500
         | (3, (12, 12)) => 500
         | (3, (12, 13)) => 500
         | (3, (13, 11)) => 500
         | (3, (13, 12)) => 500
         | (3, (13, 13)) => 500
         | (4, (0, 11)) => 500
         | (4, (0, 12)) => 500
         | (4, (0, 13)) => 500
         | (5, (0, 0)) => 500
         | _ => 500
         end in
        bindGen (freq [ (weight_2, returnGen 2); (1000-weight_2, returnGen 0)])
        (fun n2 : nat =>  
         let weight_4 := match (size,(stack1, stack2)) with 
         | (1, (11, 11)) => 500
         | (1, (11, 12)) => 500
         | (1, (11, 13)) => 500
         | (1, (12, 11)) => 500
         | (1, (12, 12)) => 500
         | (1, (12, 13)) => 500
         | (1, (13, 11)) => 500
         | (1, (13, 12)) => 500
         | (1, (13, 13)) => 500
         | (2, (11, 11)) => 500
         | (2, (11, 12)) => 500
         | (2, (11, 13)) => 500
         | (2, (12, 11)) => 500
         | (2, (12, 12)) => 500
         | (2, (12, 13)) => 500
         | (2, (13, 11)) => 500
         | (2, (13, 12)) => 500
         | (2, (13, 13)) => 500
         | (3, (11, 11)) => 500
         | (3, (11, 12)) => 500
         | (3, (11, 13)) => 500
         | (3, (12, 11)) => 500
         | (3, (12, 12)) => 500
         | (3, (12, 13)) => 500
         | (3, (13, 11)) => 500
         | (3, (13, 12)) => 500
         | (3, (13, 13)) => 500
         | (4, (0, 11)) => 500
         | (4, (0, 12)) => 500
         | (4, (0, 13)) => 500
         | (5, (0, 0)) => 500
         | _ => 500
         end in
        bindGen (freq [ (weight_4, returnGen 4); (1000-weight_4, returnGen 0)])
        (fun n4 : nat =>  
         let weight_8 := match (size,(stack1, stack2)) with 
         | (1, (11, 11)) => 500
         | (1, (11, 12)) => 500
         | (1, (11, 13)) => 500
         | (1, (12, 11)) => 500
         | (1, (12, 12)) => 500
         | (1, (12, 13)) => 500
         | (1, (13, 11)) => 500
         | (1, (13, 12)) => 500
         | (1, (13, 13)) => 500
         | (2, (11, 11)) => 500
         | (2, (11, 12)) => 500
         | (2, (11, 13)) => 500
         | (2, (12, 11)) => 500
         | (2, (12, 12)) => 500
         | (2, (12, 13)) => 500
         | (2, (13, 11)) => 500
         | (2, (13, 12)) => 500
         | (2, (13, 13)) => 500
         | (3, (11, 11)) => 500
         | (3, (11, 12)) => 500
         | (3, (11, 13)) => 500
         | (3, (12, 11)) => 500
         | (3, (12, 12)) => 500
         | (3, (12, 13)) => 500
         | (3, (13, 11)) => 500
         | (3, (13, 12)) => 500
         | (3, (13, 13)) => 500
         | (4, (0, 11)) => 500
         | (4, (0, 12)) => 500
         | (4, (0, 13)) => 500
         | (5, (0, 0)) => 500
         | _ => 500
         end in
        bindGen (freq [ (weight_8, returnGen 8); (1000-weight_8, returnGen 0)])
        (fun n8 : nat =>  
         let weight_16 := match (size,(stack1, stack2)) with 
         | (1, (11, 11)) => 500
         | (1, (11, 12)) => 500
         | (1, (11, 13)) => 500
         | (1, (12, 11)) => 500
         | (1, (12, 12)) => 500
         | (1, (12, 13)) => 500
         | (1, (13, 11)) => 500
         | (1, (13, 12)) => 500
         | (1, (13, 13)) => 500
         | (2, (11, 11)) => 500
         | (2, (11, 12)) => 500
         | (2, (11, 13)) => 500
         | (2, (12, 11)) => 500
         | (2, (12, 12)) => 500
         | (2, (12, 13)) => 500
         | (2, (13, 11)) => 500
         | (2, (13, 12)) => 500
         | (2, (13, 13)) => 500
         | (3, (11, 11)) => 500
         | (3, (11, 12)) => 500
         | (3, (11, 13)) => 500
         | (3, (12, 11)) => 500
         | (3, (12, 12)) => 500
         | (3, (12, 13)) => 500
         | (3, (13, 11)) => 500
         | (3, (13, 12)) => 500
         | (3, (13, 13)) => 500
         | (4, (0, 11)) => 500
         | (4, (0, 12)) => 500
         | (4, (0, 13)) => 500
         | (5, (0, 0)) => 500
         | _ => 500
         end in
        bindGen (freq [ (weight_16, returnGen 16); (1000-weight_16, returnGen 0)])
        (fun n16 : nat =>  
         let weight_32 := match (size,(stack1, stack2)) with 
         | (1, (11, 11)) => 500
         | (1, (11, 12)) => 500
         | (1, (11, 13)) => 500
         | (1, (12, 11)) => 500
         | (1, (12, 12)) => 500
         | (1, (12, 13)) => 500
         | (1, (13, 11)) => 500
         | (1, (13, 12)) => 500
         | (1, (13, 13)) => 500
         | (2, (11, 11)) => 500
         | (2, (11, 12)) => 500
         | (2, (11, 13)) => 500
         | (2, (12, 11)) => 500
         | (2, (12, 12)) => 500
         | (2, (12, 13)) => 500
         | (2, (13, 11)) => 500
         | (2, (13, 12)) => 500
         | (2, (13, 13)) => 500
         | (3, (11, 11)) => 500
         | (3, (11, 12)) => 500
         | (3, (11, 13)) => 500
         | (3, (12, 11)) => 500
         | (3, (12, 12)) => 500
         | (3, (12, 13)) => 500
         | (3, (13, 11)) => 500
         | (3, (13, 12)) => 500
         | (3, (13, 13)) => 500
         | (4, (0, 11)) => 500
         | (4, (0, 12)) => 500
         | (4, (0, 13)) => 500
         | (5, (0, 0)) => 500
         | _ => 500
         end in
        bindGen (freq [ (weight_32, returnGen 32); (1000-weight_32, returnGen 0)])
        (fun n32 : nat =>  
        let p1 := n1+n2+n4+n8+n16+n32 in
        returnGen (Var p1))
      ))))));
      (weight_boolean,
        let weight_true := match (size,(stack1, stack2)) with 
         | (1, (11, 11)) => 500
         | (1, (11, 12)) => 500
         | (1, (11, 13)) => 500
         | (1, (12, 11)) => 500
         | (1, (12, 12)) => 500
         | (1, (12, 13)) => 500
         | (1, (13, 11)) => 500
         | (1, (13, 12)) => 500
         | (1, (13, 13)) => 500
         | (2, (11, 11)) => 500
         | (2, (11, 12)) => 500
         | (2, (11, 13)) => 500
         | (2, (12, 11)) => 500
         | (2, (12, 12)) => 500
         | (2, (12, 13)) => 500
         | (2, (13, 11)) => 500
         | (2, (13, 12)) => 500
         | (2, (13, 13)) => 500
         | (3, (11, 11)) => 500
         | (3, (11, 12)) => 500
         | (3, (11, 13)) => 500
         | (3, (12, 11)) => 500
         | (3, (12, 12)) => 500
         | (3, (12, 13)) => 500
         | (3, (13, 11)) => 500
         | (3, (13, 12)) => 500
         | (3, (13, 13)) => 500
         | (4, (0, 11)) => 500
         | (4, (0, 12)) => 500
         | (4, (0, 13)) => 500
         | (5, (0, 0)) => 500
         | _ => 500
         end in
        freq [ (weight_true, returnGen (Bool true)); (1000 - weight_true, returnGen (Bool false))]
      );
      (weight_abs,
      bindGen (manual_gen_typ 2 (stack2 : nat) 10)
        (fun p0 : Typ =>
         bindGen (manual_gen_expr size' (stack2 : nat) 11)
           (fun p1 : Expr => returnGen (Abs p0 p1))));
      (weight_app,
      bindGen (manual_gen_expr size' (stack2 : nat) 12)
        (fun p0 : Expr =>
         bindGen (manual_gen_expr size' (stack2 : nat) 13)
           (fun p1 : Expr => returnGen (App p0 p1))))]
  end.

Definition gSized :=
  manual_gen_expr 5 0 0.
  
Definition test_prop_SinglePreserve :=
  forAll gSized (fun (e: Expr) =>
    prop_SinglePreserve e).

(*! QuickChick test_prop_SinglePreserve. *)
  
Definition test_prop_MultiPreserve :=
  forAll gSized (fun (e: Expr) =>
    prop_MultiPreserve e).
  
(*! QuickChick test_prop_MultiPreserve. *)


