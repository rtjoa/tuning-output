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
         | (1, (0, 10)) => 522
         | (1, (11, 10)) => 476
         | (1, (12, 10)) => 492
         | (1, (13, 10)) => 503
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
         | (0, (11, 11)) => 503
         | (0, (11, 12)) => 551
         | (0, (11, 13)) => 493
         | (0, (12, 11)) => 540
         | (0, (12, 12)) => 493
         | (0, (12, 13)) => 500
         | (0, (13, 11)) => 486
         | (0, (13, 12)) => 491
         | (0, (13, 13)) => 507
         | _ => 500
         end in
      freq [ (weight_var, bindGen arbitrary (fun p0 : nat => returnGen (Var p0)));
      (1000 - weight_var, bindGen arbitrary (fun p0 : bool => returnGen (Bool p0)))]
  | S size' =>
      let weight_var := match (size,(stack1, stack2)) with 
         | (1, (0, 11)) => 636
         | (1, (0, 12)) => 464
         | (1, (0, 13)) => 462
         | (2, (0, 0)) => 242
         | _ => 500
         end in
      let weight_bool := match (size,(stack1, stack2)) with 
         | (1, (0, 11)) => 492
         | (1, (0, 12)) => 456
         | (1, (0, 13)) => 557
         | (2, (0, 0)) => 409
         | _ => 500
         end in
      let weight_abs := match (size,(stack1, stack2)) with 
         | (1, (0, 11)) => 487
         | (1, (0, 12)) => 609
         | (1, (0, 13)) => 511
         | (2, (0, 0)) => 766
         | _ => 500
         end in
      let weight_app := match (size,(stack1, stack2)) with 
         | (1, (0, 11)) => 352
         | (1, (0, 12)) => 453
         | (1, (0, 13)) => 465
         | (2, (0, 0)) => 399
         | _ => 500
         end in
      freq [
      (weight_var,

         let weight_1 := match (size,(stack1, stack2)) with 
         | (1, (0, 11)) => 493
         | (1, (0, 12)) => 497
         | (1, (0, 13)) => 493
         | (2, (0, 0)) => 503
         | _ => 500
         end in
        bindGen (freq [ (weight_1, returnGen 1); (1000-weight_1, returnGen 0)])
        (fun n1 : nat =>  
         let weight_2 := match (size,(stack1, stack2)) with 
         | (1, (0, 11)) => 478
         | (1, (0, 12)) => 509
         | (1, (0, 13)) => 491
         | (2, (0, 0)) => 495
         | _ => 500
         end in
        bindGen (freq [ (weight_2, returnGen 2); (1000-weight_2, returnGen 0)])
        (fun n2 : nat =>  
         let weight_4 := match (size,(stack1, stack2)) with 
         | (1, (0, 11)) => 437
         | (1, (0, 12)) => 508
         | (1, (0, 13)) => 494
         | (2, (0, 0)) => 501
         | _ => 500
         end in
        bindGen (freq [ (weight_4, returnGen 4); (1000-weight_4, returnGen 0)])
        (fun n4 : nat =>  
         let weight_8 := match (size,(stack1, stack2)) with 
         | (1, (0, 11)) => 521
         | (1, (0, 12)) => 501
         | (1, (0, 13)) => 501
         | (2, (0, 0)) => 498
         | _ => 500
         end in
        bindGen (freq [ (weight_8, returnGen 8); (1000-weight_8, returnGen 0)])
        (fun n8 : nat =>  
         let weight_16 := match (size,(stack1, stack2)) with 
         | (1, (0, 11)) => 430
         | (1, (0, 12)) => 497
         | (1, (0, 13)) => 509
         | (2, (0, 0)) => 483
         | _ => 500
         end in
        bindGen (freq [ (weight_16, returnGen 16); (1000-weight_16, returnGen 0)])
        (fun n16 : nat =>  
         let weight_32 := match (size,(stack1, stack2)) with 
         | (1, (0, 11)) => 492
         | (1, (0, 12)) => 500
         | (1, (0, 13)) => 497
         | (2, (0, 0)) => 500
         | _ => 500
         end in
        bindGen (freq [ (weight_32, returnGen 32); (1000-weight_32, returnGen 0)])
        (fun n32 : nat =>  
        let p1 := n1+n2+n4+n8+n16+n32 in
        returnGen (Var p1))
      ))))));
      (weight_bool,
        let weight_true := match (size,(stack1, stack2)) with 
         | (1, (0, 11)) => 452
         | (1, (0, 12)) => 497
         | (1, (0, 13)) => 511
         | (2, (0, 0)) => 464
         | _ => 500
         end in
        freq [ (weight_true, returnGen (Bool true)); (1000 - weight_true, returnGen (Bool false))]
      );
      (weight_abs,
      bindGen (manual_gen_typ 1 (stack2 : nat) 10)
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
  manual_gen_expr 2 0 0.
  
Definition test_prop_SinglePreserve :=
  forAll gSized (fun (e: Expr) =>
    prop_SinglePreserve e).

(*! QuickChick test_prop_SinglePreserve. *)
  
Definition test_prop_MultiPreserve :=
  forAll gSized (fun (e: Expr) =>
    prop_MultiPreserve e).
  
(*! QuickChick test_prop_MultiPreserve. *)


