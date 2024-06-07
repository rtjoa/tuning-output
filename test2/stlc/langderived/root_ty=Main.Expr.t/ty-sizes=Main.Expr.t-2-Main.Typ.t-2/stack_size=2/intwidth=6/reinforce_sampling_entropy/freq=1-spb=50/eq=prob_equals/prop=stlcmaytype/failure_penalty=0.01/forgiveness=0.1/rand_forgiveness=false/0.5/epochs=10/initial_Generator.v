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
      (let _weight_8 := match (size, stack1, stack2) with
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
        (_weight_8, returnGen 8);
        (100-_weight_8, returnGen 0)
      ]) (fun n8 =>
      (let _weight_16 := match (size, stack1, stack2) with
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
        (_weight_16, returnGen 16);
        (100-_weight_16, returnGen 0)
      ]) (fun n16 =>
      (let _weight_32 := match (size, stack1, stack2) with
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
        (_weight_32, returnGen 32);
        (100-_weight_32, returnGen 0)
      ]) (fun n32 =>
        returnGen (n1 + n2 + n4 + n8 + n16 + n32)
      )))))))))))) 
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
      | (1, 0, 3) => 50
      | (1, 0, 5) => 50
      | (1, 0, 6) => 50
      | (2, 0, 0) => 50
      | _ => 500
      end,
      (bindGen 
      (* GenNat2 *)
      (let _weight_1 := match (size, stack1, stack2) with
      | (1, 0, 3) => 50
      | (1, 0, 5) => 50
      | (1, 0, 6) => 50
      | (2, 0, 0) => 50
      | _ => 500
      end
      in
      bindGen (freq [
        (_weight_1, returnGen 1);
        (100-_weight_1, returnGen 0)
      ]) (fun n1 =>
      (let _weight_2 := match (size, stack1, stack2) with
      | (1, 0, 3) => 50
      | (1, 0, 5) => 50
      | (1, 0, 6) => 50
      | (2, 0, 0) => 50
      | _ => 500
      end
      in
      bindGen (freq [
        (_weight_2, returnGen 2);
        (100-_weight_2, returnGen 0)
      ]) (fun n2 =>
      (let _weight_4 := match (size, stack1, stack2) with
      | (1, 0, 3) => 50
      | (1, 0, 5) => 50
      | (1, 0, 6) => 50
      | (2, 0, 0) => 50
      | _ => 500
      end
      in
      bindGen (freq [
        (_weight_4, returnGen 4);
        (100-_weight_4, returnGen 0)
      ]) (fun n4 =>
      (let _weight_8 := match (size, stack1, stack2) with
      | (1, 0, 3) => 50
      | (1, 0, 5) => 50
      | (1, 0, 6) => 50
      | (2, 0, 0) => 50
      | _ => 500
      end
      in
      bindGen (freq [
        (_weight_8, returnGen 8);
        (100-_weight_8, returnGen 0)
      ]) (fun n8 =>
      (let _weight_16 := match (size, stack1, stack2) with
      | (1, 0, 3) => 50
      | (1, 0, 5) => 50
      | (1, 0, 6) => 50
      | (2, 0, 0) => 50
      | _ => 500
      end
      in
      bindGen (freq [
        (_weight_16, returnGen 16);
        (100-_weight_16, returnGen 0)
      ]) (fun n16 =>
      (let _weight_32 := match (size, stack1, stack2) with
      | (1, 0, 3) => 50
      | (1, 0, 5) => 50
      | (1, 0, 6) => 50
      | (2, 0, 0) => 50
      | _ => 500
      end
      in
      bindGen (freq [
        (_weight_32, returnGen 32);
        (100-_weight_32, returnGen 0)
      ]) (fun n32 =>
        returnGen (n1 + n2 + n4 + n8 + n16 + n32)
      )))))))))))) 
      (fun p1 => 
        (returnGen (Var p1))))); 
      (* Bool *) (match (size, stack1, stack2) with
      | (1, 0, 3) => 50
      | (1, 0, 5) => 50
      | (1, 0, 6) => 50
      | (2, 0, 0) => 50
      | _ => 500
      end,
      (bindGen 
      (* GenBool2 *) (let _weight_true := match (size, stack1, stack2) with
      | (1, 0, 3) => 50
      | (1, 0, 5) => 50
      | (1, 0, 6) => 50
      | (2, 0, 0) => 50
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
      | (1, 0, 3) => 50
      | (1, 0, 5) => 50
      | (1, 0, 6) => 50
      | (2, 0, 0) => 50
      | _ => 500
      end,
      (bindGen (genTyp 2 stack2 2) 
      (fun p1 => 
        (bindGen (genExpr size1 stack2 5) 
        (fun p2 => 
          (returnGen (Abs p1 p2))))))); 
      (* App *) (match (size, stack1, stack2) with
      | (1, 0, 3) => 50
      | (1, 0, 5) => 50
      | (1, 0, 6) => 50
      | (2, 0, 0) => 50
      | _ => 500
      end,
      (bindGen (genExpr size1 stack2 3) 
      (fun p1 => 
        (bindGen (genExpr size1 stack2 6) 
        (fun p2 => 
          (returnGen (App p1 p2)))))))])
  end.

Definition gSized :=
  (genExpr 2 0 0).

Definition test_prop_SinglePreserve :=
forAll gSized (fun (e: Expr) =>
  prop_SinglePreserve e).

(*! QuickChick test_prop_SinglePreserve. *)

Definition test_prop_MultiPreserve :=
forAll gSized (fun (e: Expr) =>
  prop_MultiPreserve e).

(*! QuickChick test_prop_MultiPreserve. *)
          
