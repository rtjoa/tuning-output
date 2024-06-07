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
      end,
      (bindGen 
      arbitrary 
      (fun p1 => 
        (returnGen (Var p1))))); 
      (* Bool *) (match (size, stack1, stack2) with
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
      end,
      (bindGen 
      arbitrary 
      (fun p1 => 
        (returnGen (Bool p1)))))])
  | S size1 => 
    (* Frequency4 *) (freq [
      (* Var *) (match (size, stack1, stack2) with
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
      end,
      (bindGen 
      arbitrary 
      (fun p1 => 
        (returnGen (Var p1))))); 
      (* Bool *) (match (size, stack1, stack2) with
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
      end,
      (bindGen 
      arbitrary 
      (fun p1 => 
        (returnGen (Bool p1))))); 
      (* Abs *) (match (size, stack1, stack2) with
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
      end,
      (bindGen (genTyp 2 stack2 2) 
      (fun p1 => 
        (bindGen (genExpr size1 stack2 5) 
        (fun p2 => 
          (returnGen (Abs p1 p2))))))); 
      (* App *) (match (size, stack1, stack2) with
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
          
