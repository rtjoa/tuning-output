From QuickChick Require Import QuickChick. Import QcNotation.
From Coq Require Import Bool ZArith List. Import ListNotations.
From ExtLib Require Import Monad.
From ExtLib.Data.Monads Require Import OptionMonad.
Import MonadNotation.

From STLC Require Import Impl Spec.

Fixpoint genTyp (size : nat) (stack1 : nat) (stack2 : nat) : G (Typ) :=
  match size with
  | O  => 
    (* Frequency1 (single-branch) *) 
    (returnGen (TBool ))
  | S size1 => 
    (* Frequency2 *) (freq [
      (* TBool *) (match (size, stack1, stack2) with
      | (1, 2, 1) => 50
      | (1, 2, 4) => 50
      | (2, 0, 2) => 50
      | (2, 3, 2) => 50
      | (2, 5, 2) => 50
      | (2, 6, 2) => 50
      | _ => 500
      end,
      (returnGen (TBool ))); 
      (* TFun *) (match (size, stack1, stack2) with
      | (1, 2, 1) => 50
      | (1, 2, 4) => 50
      | (2, 0, 2) => 50
      | (2, 3, 2) => 50
      | (2, 5, 2) => 50
      | (2, 6, 2) => 50
      | _ => 500
      end,
      (bindGen (genTyp size1 stack2 1) 
      (fun p1 => 
        (bindGen (genTyp size1 stack2 4) 
        (fun p2 => 
          (returnGen (TFun p1 p2)))))))])
  end.

Fixpoint genExpr (size : nat) (stack1 : nat) (stack2 : nat) : G (Expr) :=
  match size with
  | O  => 
    (* Frequency3 *) (freq [
      (* Var *) (match (size, stack1, stack2) with
      | (0, 3, 3) => 90
      | (0, 3, 5) => 59
      | (0, 3, 6) => 64
      | (0, 5, 3) => 90
      | (0, 5, 5) => 39
      | (0, 5, 6) => 63
      | (0, 6, 3) => 90
      | (0, 6, 5) => 59
      | (0, 6, 6) => 60
      | _ => 500
      end,
      (bindGen 
      (* GenNat1 *)
      (let _weight_1 := match (size, stack1, stack2) with
      | (0, 3, 3) => 50
      | (0, 3, 5) => 50
      | (0, 3, 6) => 50
      | (0, 5, 3) => 50
      | (0, 5, 5) => 50
      | (0, 5, 6) => 50
      | (0, 6, 3) => 50
      | (0, 6, 5) => 50
      | (0, 6, 6) => 50
      | _ => 500
      end
      in
      bindGen (freq [
        (_weight_1, returnGen 1);
        (100-_weight_1, returnGen 0)
      ]) (fun n1 =>
      (let _weight_2 := match (size, stack1, stack2) with
      | (0, 3, 3) => 50
      | (0, 3, 5) => 50
      | (0, 3, 6) => 50
      | (0, 5, 3) => 50
      | (0, 5, 5) => 50
      | (0, 5, 6) => 50
      | (0, 6, 3) => 50
      | (0, 6, 5) => 50
      | (0, 6, 6) => 50
      | _ => 500
      end
      in
      bindGen (freq [
        (_weight_2, returnGen 2);
        (100-_weight_2, returnGen 0)
      ]) (fun n2 =>
      (let _weight_4 := match (size, stack1, stack2) with
      | (0, 3, 3) => 50
      | (0, 3, 5) => 50
      | (0, 3, 6) => 50
      | (0, 5, 3) => 50
      | (0, 5, 5) => 50
      | (0, 5, 6) => 50
      | (0, 6, 3) => 50
      | (0, 6, 5) => 50
      | (0, 6, 6) => 50
      | _ => 500
      end
      in
      bindGen (freq [
        (_weight_4, returnGen 4);
        (100-_weight_4, returnGen 0)
      ]) (fun n4 =>
        returnGen (n1 + n2 + n4)
      )))))) 
      (fun p1 => 
        (returnGen (Var p1))))); 
      (* Bool *) (match (size, stack1, stack2) with
      | (0, 3, 3) => 10
      | (0, 3, 5) => 66
      | (0, 3, 6) => 55
      | (0, 5, 3) => 10
      | (0, 5, 5) => 73
      | (0, 5, 6) => 40
      | (0, 6, 3) => 10
      | (0, 6, 5) => 68
      | (0, 6, 6) => 49
      | _ => 500
      end,
      (bindGen 
      (* GenBool1 *) (let _weight_true := match (size, stack1, stack2) with
      | (0, 3, 3) => 50
      | (0, 3, 5) => 50
      | (0, 3, 6) => 50
      | (0, 5, 3) => 50
      | (0, 5, 5) => 50
      | (0, 5, 6) => 50
      | (0, 6, 3) => 50
      | (0, 6, 5) => 50
      | (0, 6, 6) => 50
      | _ => 500
      end
      in
      freq [
        (_weight_true, returnGen true);
        (100-_weight_true, returnGen false)
      ]) 
      (fun p1 => 
        (returnGen (Bool p1)))))])
  | S size1 => 
    (* Frequency4 *) (freq [
      (* Var *) (match (size, stack1, stack2) with
      | (1, 3, 3) => 89
      | (1, 3, 5) => 38
      | (1, 3, 6) => 35
      | (1, 5, 3) => 88
      | (1, 5, 5) => 43
      | (1, 5, 6) => 39
      | (1, 6, 3) => 88
      | (1, 6, 5) => 55
      | (1, 6, 6) => 46
      | (2, 3, 3) => 21
      | (2, 3, 5) => 11
      | (2, 3, 6) => 10
      | (2, 5, 3) => 37
      | (2, 5, 5) => 15
      | (2, 5, 6) => 17
      | (2, 6, 3) => 34
      | (2, 6, 5) => 17
      | (2, 6, 6) => 10
      | (3, 3, 3) => 10
      | (3, 3, 5) => 10
      | (3, 3, 6) => 10
      | (3, 5, 3) => 11
      | (3, 5, 5) => 10
      | (3, 5, 6) => 10
      | (3, 6, 3) => 10
      | (3, 6, 5) => 11
      | (3, 6, 6) => 10
      | (4, 0, 3) => 10
      | (4, 0, 5) => 10
      | (4, 0, 6) => 10
      | (5, 0, 0) => 10
      | _ => 500
      end,
      (bindGen 
      (* GenNat2 *)
      (let _weight_1 := match (size, stack1, stack2) with
      | (1, 3, 3) => 50
      | (1, 3, 5) => 50
      | (1, 3, 6) => 50
      | (1, 5, 3) => 50
      | (1, 5, 5) => 50
      | (1, 5, 6) => 50
      | (1, 6, 3) => 50
      | (1, 6, 5) => 50
      | (1, 6, 6) => 50
      | (2, 3, 3) => 50
      | (2, 3, 5) => 50
      | (2, 3, 6) => 50
      | (2, 5, 3) => 50
      | (2, 5, 5) => 50
      | (2, 5, 6) => 50
      | (2, 6, 3) => 50
      | (2, 6, 5) => 50
      | (2, 6, 6) => 50
      | (3, 3, 3) => 50
      | (3, 3, 5) => 50
      | (3, 3, 6) => 50
      | (3, 5, 3) => 50
      | (3, 5, 5) => 50
      | (3, 5, 6) => 50
      | (3, 6, 3) => 50
      | (3, 6, 5) => 50
      | (3, 6, 6) => 50
      | (4, 0, 3) => 50
      | (4, 0, 5) => 50
      | (4, 0, 6) => 50
      | (5, 0, 0) => 50
      | _ => 500
      end
      in
      bindGen (freq [
        (_weight_1, returnGen 1);
        (100-_weight_1, returnGen 0)
      ]) (fun n1 =>
      (let _weight_2 := match (size, stack1, stack2) with
      | (1, 3, 3) => 50
      | (1, 3, 5) => 50
      | (1, 3, 6) => 50
      | (1, 5, 3) => 50
      | (1, 5, 5) => 50
      | (1, 5, 6) => 50
      | (1, 6, 3) => 50
      | (1, 6, 5) => 50
      | (1, 6, 6) => 50
      | (2, 3, 3) => 50
      | (2, 3, 5) => 50
      | (2, 3, 6) => 50
      | (2, 5, 3) => 50
      | (2, 5, 5) => 50
      | (2, 5, 6) => 50
      | (2, 6, 3) => 50
      | (2, 6, 5) => 50
      | (2, 6, 6) => 50
      | (3, 3, 3) => 50
      | (3, 3, 5) => 50
      | (3, 3, 6) => 50
      | (3, 5, 3) => 50
      | (3, 5, 5) => 50
      | (3, 5, 6) => 50
      | (3, 6, 3) => 50
      | (3, 6, 5) => 50
      | (3, 6, 6) => 50
      | (4, 0, 3) => 50
      | (4, 0, 5) => 50
      | (4, 0, 6) => 50
      | (5, 0, 0) => 50
      | _ => 500
      end
      in
      bindGen (freq [
        (_weight_2, returnGen 2);
        (100-_weight_2, returnGen 0)
      ]) (fun n2 =>
      (let _weight_4 := match (size, stack1, stack2) with
      | (1, 3, 3) => 50
      | (1, 3, 5) => 50
      | (1, 3, 6) => 50
      | (1, 5, 3) => 50
      | (1, 5, 5) => 50
      | (1, 5, 6) => 50
      | (1, 6, 3) => 50
      | (1, 6, 5) => 50
      | (1, 6, 6) => 50
      | (2, 3, 3) => 50
      | (2, 3, 5) => 50
      | (2, 3, 6) => 50
      | (2, 5, 3) => 50
      | (2, 5, 5) => 50
      | (2, 5, 6) => 50
      | (2, 6, 3) => 50
      | (2, 6, 5) => 50
      | (2, 6, 6) => 50
      | (3, 3, 3) => 50
      | (3, 3, 5) => 50
      | (3, 3, 6) => 50
      | (3, 5, 3) => 50
      | (3, 5, 5) => 50
      | (3, 5, 6) => 50
      | (3, 6, 3) => 50
      | (3, 6, 5) => 50
      | (3, 6, 6) => 50
      | (4, 0, 3) => 50
      | (4, 0, 5) => 50
      | (4, 0, 6) => 50
      | (5, 0, 0) => 50
      | _ => 500
      end
      in
      bindGen (freq [
        (_weight_4, returnGen 4);
        (100-_weight_4, returnGen 0)
      ]) (fun n4 =>
        returnGen (n1 + n2 + n4)
      )))))) 
      (fun p1 => 
        (returnGen (Var p1))))); 
      (* Bool *) (match (size, stack1, stack2) with
      | (1, 3, 3) => 10
      | (1, 3, 5) => 62
      | (1, 3, 6) => 31
      | (1, 5, 3) => 10
      | (1, 5, 5) => 28
      | (1, 5, 6) => 66
      | (1, 6, 3) => 10
      | (1, 6, 5) => 40
      | (1, 6, 6) => 26
      | (2, 3, 3) => 10
      | (2, 3, 5) => 15
      | (2, 3, 6) => 20
      | (2, 5, 3) => 10
      | (2, 5, 5) => 17
      | (2, 5, 6) => 14
      | (2, 6, 3) => 10
      | (2, 6, 5) => 16
      | (2, 6, 6) => 23
      | (3, 3, 3) => 10
      | (3, 3, 5) => 10
      | (3, 3, 6) => 73
      | (3, 5, 3) => 10
      | (3, 5, 5) => 10
      | (3, 5, 6) => 10
      | (3, 6, 3) => 10
      | (3, 6, 5) => 10
      | (3, 6, 6) => 78
      | (4, 0, 3) => 10
      | (4, 0, 5) => 10
      | (4, 0, 6) => 10
      | (5, 0, 0) => 10
      | _ => 500
      end,
      (bindGen 
      (* GenBool2 *) (let _weight_true := match (size, stack1, stack2) with
      | (1, 3, 3) => 50
      | (1, 3, 5) => 50
      | (1, 3, 6) => 50
      | (1, 5, 3) => 50
      | (1, 5, 5) => 50
      | (1, 5, 6) => 50
      | (1, 6, 3) => 50
      | (1, 6, 5) => 50
      | (1, 6, 6) => 50
      | (2, 3, 3) => 50
      | (2, 3, 5) => 50
      | (2, 3, 6) => 50
      | (2, 5, 3) => 50
      | (2, 5, 5) => 50
      | (2, 5, 6) => 50
      | (2, 6, 3) => 50
      | (2, 6, 5) => 50
      | (2, 6, 6) => 50
      | (3, 3, 3) => 50
      | (3, 3, 5) => 50
      | (3, 3, 6) => 50
      | (3, 5, 3) => 50
      | (3, 5, 5) => 50
      | (3, 5, 6) => 50
      | (3, 6, 3) => 50
      | (3, 6, 5) => 50
      | (3, 6, 6) => 50
      | (4, 0, 3) => 50
      | (4, 0, 5) => 50
      | (4, 0, 6) => 50
      | (5, 0, 0) => 50
      | _ => 500
      end
      in
      freq [
        (_weight_true, returnGen true);
        (100-_weight_true, returnGen false)
      ]) 
      (fun p1 => 
        (returnGen (Bool p1))))); 
      (* Abs *) (match (size, stack1, stack2) with
      | (1, 3, 3) => 90
      | (1, 3, 5) => 82
      | (1, 3, 6) => 90
      | (1, 5, 3) => 90
      | (1, 5, 5) => 84
      | (1, 5, 6) => 75
      | (1, 6, 3) => 90
      | (1, 6, 5) => 81
      | (1, 6, 6) => 88
      | (2, 3, 3) => 90
      | (2, 3, 5) => 57
      | (2, 3, 6) => 63
      | (2, 5, 3) => 90
      | (2, 5, 5) => 57
      | (2, 5, 6) => 40
      | (2, 6, 3) => 90
      | (2, 6, 5) => 27
      | (2, 6, 6) => 63
      | (3, 3, 3) => 90
      | (3, 3, 5) => 22
      | (3, 3, 6) => 90
      | (3, 5, 3) => 56
      | (3, 5, 5) => 25
      | (3, 5, 6) => 10
      | (3, 6, 3) => 90
      | (3, 6, 5) => 12
      | (3, 6, 6) => 90
      | (4, 0, 3) => 90
      | (4, 0, 5) => 11
      | (4, 0, 6) => 90
      | (5, 0, 0) => 90
      | _ => 500
      end,
      (bindGen (genTyp 2 stack2 2) 
      (fun p1 => 
        (bindGen (genExpr size1 stack2 5) 
        (fun p2 => 
          (returnGen (Abs p1 p2))))))); 
      (* App *) (match (size, stack1, stack2) with
      | (1, 3, 3) => 59
      | (1, 3, 5) => 18
      | (1, 3, 6) => 11
      | (1, 5, 3) => 76
      | (1, 5, 5) => 11
      | (1, 5, 6) => 19
      | (1, 6, 3) => 76
      | (1, 6, 5) => 22
      | (1, 6, 6) => 12
      | (2, 3, 3) => 90
      | (2, 3, 5) => 88
      | (2, 3, 6) => 89
      | (2, 5, 3) => 90
      | (2, 5, 5) => 81
      | (2, 5, 6) => 89
      | (2, 6, 3) => 90
      | (2, 6, 5) => 87
      | (2, 6, 6) => 89
      | (3, 3, 3) => 10
      | (3, 3, 5) => 90
      | (3, 3, 6) => 10
      | (3, 5, 3) => 90
      | (3, 5, 5) => 90
      | (3, 5, 6) => 90
      | (3, 6, 3) => 10
      | (3, 6, 5) => 90
      | (3, 6, 6) => 10
      | (4, 0, 3) => 54
      | (4, 0, 5) => 90
      | (4, 0, 6) => 10
      | (5, 0, 0) => 90
      | _ => 500
      end,
      (bindGen (genExpr size1 stack2 3) 
      (fun p1 => 
        (bindGen (genExpr size1 stack2 6) 
        (fun p2 => 
          (returnGen (App p1 p2)))))))])
  end.

Definition gSized :=
  (genExpr 5 0 0).

Definition test_prop_SinglePreserve :=
forAll gSized (fun (e: Expr) =>
  prop_SinglePreserve e).

(*! QuickChick test_prop_SinglePreserve. *)

Definition test_prop_MultiPreserve :=
forAll gSized (fun (e: Expr) =>
  prop_MultiPreserve e).

(*! QuickChick test_prop_MultiPreserve. *)
          
