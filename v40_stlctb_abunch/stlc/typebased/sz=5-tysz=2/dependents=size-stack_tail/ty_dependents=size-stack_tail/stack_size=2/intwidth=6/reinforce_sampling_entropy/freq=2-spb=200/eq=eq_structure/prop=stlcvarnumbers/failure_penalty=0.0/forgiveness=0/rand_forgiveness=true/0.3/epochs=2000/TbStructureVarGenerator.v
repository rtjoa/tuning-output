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
         | (0, (11, 11)) => 230
         | (0, (11, 12)) => 731
         | (0, (11, 13)) => 722
         | (0, (12, 11)) => 591
         | (0, (12, 12)) => 553
         | (0, (12, 13)) => 513
         | (0, (13, 11)) => 597
         | (0, (13, 12)) => 588
         | (0, (13, 13)) => 427
         | _ => 500
         end in
      freq [ (weight_var, bindGen arbitrary (fun p0 : nat => returnGen (Var p0)));
      (1000 - weight_var, bindGen arbitrary (fun p0 : bool => returnGen (Bool p0)))]
  | S size' =>
      let weight_var := match (size,(stack1, stack2)) with 
         | (1, (11, 11)) => 1
         | (1, (11, 12)) => 0
         | (1, (11, 13)) => 0
         | (1, (12, 11)) => 0
         | (1, (12, 12)) => 0
         | (1, (12, 13)) => 0
         | (1, (13, 11)) => 0
         | (1, (13, 12)) => 0
         | (1, (13, 13)) => 0
         | (2, (11, 11)) => 5
         | (2, (11, 12)) => 0
         | (2, (11, 13)) => 0
         | (2, (12, 11)) => 0
         | (2, (12, 12)) => 0
         | (2, (12, 13)) => 0
         | (2, (13, 11)) => 0
         | (2, (13, 12)) => 0
         | (2, (13, 13)) => 0
         | (3, (11, 11)) => 26
         | (3, (11, 12)) => 13
         | (3, (11, 13)) => 13
         | (3, (12, 11)) => 0
         | (3, (12, 12)) => 0
         | (3, (12, 13)) => 0
         | (3, (13, 11)) => 0
         | (3, (13, 12)) => 0
         | (3, (13, 13)) => 0
         | (4, (0, 11)) => 6
         | (4, (0, 12)) => 0
         | (4, (0, 13)) => 0
         | (5, (0, 0)) => 0
         | _ => 500
         end in
      let weight_bool := match (size,(stack1, stack2)) with 
         | (1, (11, 11)) => 135
         | (1, (11, 12)) => 213
         | (1, (11, 13)) => 422
         | (1, (12, 11)) => 396
         | (1, (12, 12)) => 278
         | (1, (12, 13)) => 74
         | (1, (13, 11)) => 293
         | (1, (13, 12)) => 512
         | (1, (13, 13)) => 223
         | (2, (11, 11)) => 69
         | (2, (11, 12)) => 26
         | (2, (11, 13)) => 12
         | (2, (12, 11)) => 6
         | (2, (12, 12)) => 177
         | (2, (12, 13)) => 180
         | (2, (13, 11)) => 10
         | (2, (13, 12)) => 224
         | (2, (13, 13)) => 170
         | (3, (11, 11)) => 116
         | (3, (11, 12)) => 126
         | (3, (11, 13)) => 148
         | (3, (12, 11)) => 2
         | (3, (12, 12)) => 5
         | (3, (12, 13)) => 30
         | (3, (13, 11)) => 6
         | (3, (13, 12)) => 11
         | (3, (13, 13)) => 13
         | (4, (0, 11)) => 17
         | (4, (0, 12)) => 1
         | (4, (0, 13)) => 1
         | (5, (0, 0)) => 0
         | _ => 500
         end in
      let weight_abs := match (size,(stack1, stack2)) with 
         | (1, (11, 11)) => 450
         | (1, (11, 12)) => 479
         | (1, (11, 13)) => 409
         | (1, (12, 11)) => 516
         | (1, (12, 12)) => 647
         | (1, (12, 13)) => 668
         | (1, (13, 11)) => 396
         | (1, (13, 12)) => 669
         | (1, (13, 13)) => 768
         | (2, (11, 11)) => 207
         | (2, (11, 12)) => 65
         | (2, (11, 13)) => 31
         | (2, (12, 11)) => 275
         | (2, (12, 12)) => 953
         | (2, (12, 13)) => 953
         | (2, (13, 11)) => 44
         | (2, (13, 12)) => 953
         | (2, (13, 13)) => 953
         | (3, (11, 11)) => 445
         | (3, (11, 12)) => 633
         | (3, (11, 13)) => 611
         | (3, (12, 11)) => 18
         | (3, (12, 12)) => 923
         | (3, (12, 13)) => 918
         | (3, (13, 11)) => 35
         | (3, (13, 12)) => 853
         | (3, (13, 13)) => 884
         | (4, (0, 11)) => 156
         | (4, (0, 12)) => 287
         | (4, (0, 13)) => 147
         | (5, (0, 0)) => 1
         | _ => 500
         end in
      let weight_app := match (size,(stack1, stack2)) with 
         | (1, (11, 11)) => 922
         | (1, (11, 12)) => 953
         | (1, (11, 13)) => 952
         | (1, (12, 11)) => 950
         | (1, (12, 12)) => 929
         | (1, (12, 13)) => 933
         | (1, (13, 11)) => 951
         | (1, (13, 12)) => 916
         | (1, (13, 13)) => 914
         | (2, (11, 11)) => 916
         | (2, (11, 12)) => 946
         | (2, (11, 13)) => 950
         | (2, (12, 11)) => 946
         | (2, (12, 12)) => 0
         | (2, (12, 13)) => 1
         | (2, (13, 11)) => 950
         | (2, (13, 12)) => 0
         | (2, (13, 13)) => 0
         | (3, (11, 11)) => 876
         | (3, (11, 12)) => 862
         | (3, (11, 13)) => 863
         | (3, (12, 11)) => 951
         | (3, (12, 12)) => 856
         | (3, (12, 13)) => 848
         | (3, (13, 11)) => 947
         | (3, (13, 12)) => 922
         | (3, (13, 13)) => 908
         | (4, (0, 11)) => 925
         | (4, (0, 12)) => 957
         | (4, (0, 13)) => 958
         | (5, (0, 0)) => 964
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
      (weight_bool,
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


