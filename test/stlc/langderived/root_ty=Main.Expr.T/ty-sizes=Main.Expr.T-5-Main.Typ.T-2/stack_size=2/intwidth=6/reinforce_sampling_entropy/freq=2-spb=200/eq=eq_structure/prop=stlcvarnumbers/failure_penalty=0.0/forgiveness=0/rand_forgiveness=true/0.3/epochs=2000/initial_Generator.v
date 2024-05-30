From QuickChick Require Import QuickChick. Import QcNotation.
From Coq Require Import Bool ZArith List. Import ListNotations.
From ExtLib Require Import Monad.
From ExtLib.Data.Monads Require Import OptionMonad.
Import MonadNotation.

From STLC Require Import Impl Spec.

Fixpoint genTyp (size : nat) (stack1 : nat) (stack2 : nat) : Typ :=
  match size with
  | O  => 
    (* Frequency4 *) (freq [
      (match (size, stack1, stack2) with
      | (0, 5, 5) => 50
      | (0, 5, 6) => 50
      | (0, 6, 5) => 50
      | (0, 6, 6) => 50
      | _ => 500
      end,(TBool ))])
  | S size1 => 
    (* Frequency3 *) (freq [
      (match (size, stack1, stack2) with
      | (1, 4, 5) => 50
      | (1, 4, 6) => 50
      | (2, 0, 4) => 50
      | (2, 1, 4) => 50
      | (2, 2, 4) => 50
      | (2, 3, 4) => 50
      | _ => 500
      end,(TBool )); 
      (match (size, stack1, stack2) with
      | (1, 4, 5) => 50
      | (1, 4, 6) => 50
      | (2, 0, 4) => 50
      | (2, 1, 4) => 50
      | (2, 2, 4) => 50
      | (2, 3, 4) => 50
      | _ => 500
      end,
      (bindGen (genTyp size1 stack2 6) 
      (fun p1 => 
        (bindGen (genTyp size1 stack2 5) 
        (fun p2 => (TFun p1 p2))))))])
  end.

Fixpoint genExpr (size : nat) (stack1 : nat) (stack2 : nat) : Expr :=
  match size with
  | O  => 
    (* Frequency2 *) (freq [
      (match (size, stack1, stack2) with
      | (0, 1, 1) => 50
      | (0, 1, 2) => 50
      | (0, 1, 3) => 50
      | (0, 2, 1) => 50
      | (0, 2, 2) => 50
      | (0, 2, 3) => 50
      | (0, 3, 1) => 50
      | (0, 3, 2) => 50
      | (0, 3, 3) => 50
      | _ => 500
      end,
      (bindGen 
      (* GenNat2 *) (let _weight_1 := match (size, stack1, stack2) with
      | (0, 1, 1) => 50
      | (0, 1, 2) => 50
      | (0, 1, 3) => 50
      | (0, 2, 1) => 50
      | (0, 2, 2) => 50
      | (0, 2, 3) => 50
      | (0, 3, 1) => 50
      | (0, 3, 2) => 50
      | (0, 3, 3) => 50
      | _ => 500
      end
      in
      bindGen (freq [
        (_weight_1, returnGen 1);
        (100-_weight_1, returnGen 0)
      ]) (fun n1 =>
      (* GenNat2 *) (let _weight_2 := match (size, stack1, stack2) with
      | (0, 1, 1) => 50
      | (0, 1, 2) => 50
      | (0, 1, 3) => 50
      | (0, 2, 1) => 50
      | (0, 2, 2) => 50
      | (0, 2, 3) => 50
      | (0, 3, 1) => 50
      | (0, 3, 2) => 50
      | (0, 3, 3) => 50
      | _ => 500
      end
      in
      bindGen (freq [
        (_weight_2, returnGen 2);
        (100-_weight_2, returnGen 0)
      ]) (fun n2 =>
      (* GenNat2 *) (let _weight_4 := match (size, stack1, stack2) with
      | (0, 1, 1) => 50
      | (0, 1, 2) => 50
      | (0, 1, 3) => 50
      | (0, 2, 1) => 50
      | (0, 2, 2) => 50
      | (0, 2, 3) => 50
      | (0, 3, 1) => 50
      | (0, 3, 2) => 50
      | (0, 3, 3) => 50
      | _ => 500
      end
      in
      bindGen (freq [
        (_weight_4, returnGen 4);
        (100-_weight_4, returnGen 0)
      ]) (fun n4 =>
      (* GenNat2 *) (let _weight_8 := match (size, stack1, stack2) with
      | (0, 1, 1) => 50
      | (0, 1, 2) => 50
      | (0, 1, 3) => 50
      | (0, 2, 1) => 50
      | (0, 2, 2) => 50
      | (0, 2, 3) => 50
      | (0, 3, 1) => 50
      | (0, 3, 2) => 50
      | (0, 3, 3) => 50
      | _ => 500
      end
      in
      bindGen (freq [
        (_weight_8, returnGen 8);
        (100-_weight_8, returnGen 0)
      ]) (fun n8 =>
      (* GenNat2 *) (let _weight_16 := match (size, stack1, stack2) with
      | (0, 1, 1) => 50
      | (0, 1, 2) => 50
      | (0, 1, 3) => 50
      | (0, 2, 1) => 50
      | (0, 2, 2) => 50
      | (0, 2, 3) => 50
      | (0, 3, 1) => 50
      | (0, 3, 2) => 50
      | (0, 3, 3) => 50
      | _ => 500
      end
      in
      bindGen (freq [
        (_weight_16, returnGen 16);
        (100-_weight_16, returnGen 0)
      ]) (fun n16 =>
      (* GenNat2 *) (let _weight_32 := match (size, stack1, stack2) with
      | (0, 1, 1) => 50
      | (0, 1, 2) => 50
      | (0, 1, 3) => 50
      | (0, 2, 1) => 50
      | (0, 2, 2) => 50
      | (0, 2, 3) => 50
      | (0, 3, 1) => 50
      | (0, 3, 2) => 50
      | (0, 3, 3) => 50
      | _ => 500
      end
      in
      bindGen (freq [
        (_weight_32, returnGen 32);
        (100-_weight_32, returnGen 0)
      ]) (fun n32 =>
        n1 + n2 + n4 + n8 + n16 + n32
      ))))))) 
      (fun p1 => (Var p1)))); 
      (match (size, stack1, stack2) with
      | (0, 1, 1) => 50
      | (0, 1, 2) => 50
      | (0, 1, 3) => 50
      | (0, 2, 1) => 50
      | (0, 2, 2) => 50
      | (0, 2, 3) => 50
      | (0, 3, 1) => 50
      | (0, 3, 2) => 50
      | (0, 3, 3) => 50
      | _ => 500
      end,
      (bindGen 
      (* GenBool2 *) (let _weight_true := match (size, stack1, stack2) with
      | (0, 1, 1) => 50
      | (0, 1, 2) => 50
      | (0, 1, 3) => 50
      | (0, 2, 1) => 50
      | (0, 2, 2) => 50
      | (0, 2, 3) => 50
      | (0, 3, 1) => 50
      | (0, 3, 2) => 50
      | (0, 3, 3) => 50
      | _ => 500
      end
      in
      freq [
        (_weight_true, returnGen true);
        (100-_weight_true, returnGen false)
      ]) 
      (fun p1 => (Bool p1))))])
  | S size1 => 
    (* Frequency1 *) (freq [
      (match (size, stack1, stack2) with
      | (1, 1, 1) => 50
      | (1, 1, 2) => 50
      | (1, 1, 3) => 50
      | (1, 2, 1) => 50
      | (1, 2, 2) => 50
      | (1, 2, 3) => 50
      | (1, 3, 1) => 50
      | (1, 3, 2) => 50
      | (1, 3, 3) => 50
      | (2, 1, 1) => 50
      | (2, 1, 2) => 50
      | (2, 1, 3) => 50
      | (2, 2, 1) => 50
      | (2, 2, 2) => 50
      | (2, 2, 3) => 50
      | (2, 3, 1) => 50
      | (2, 3, 2) => 50
      | (2, 3, 3) => 50
      | (3, 1, 1) => 50
      | (3, 1, 2) => 50
      | (3, 1, 3) => 50
      | (3, 2, 1) => 50
      | (3, 2, 2) => 50
      | (3, 2, 3) => 50
      | (3, 3, 1) => 50
      | (3, 3, 2) => 50
      | (3, 3, 3) => 50
      | (4, 0, 1) => 50
      | (4, 0, 2) => 50
      | (4, 0, 3) => 50
      | (5, 0, 0) => 50
      | _ => 500
      end,
      (bindGen 
      (* GenNat1 *) (let _weight_1 := match (size, stack1, stack2) with
      | (1, 1, 1) => 50
      | (1, 1, 2) => 50
      | (1, 1, 3) => 50
      | (1, 2, 1) => 50
      | (1, 2, 2) => 50
      | (1, 2, 3) => 50
      | (1, 3, 1) => 50
      | (1, 3, 2) => 50
      | (1, 3, 3) => 50
      | (2, 1, 1) => 50
      | (2, 1, 2) => 50
      | (2, 1, 3) => 50
      | (2, 2, 1) => 50
      | (2, 2, 2) => 50
      | (2, 2, 3) => 50
      | (2, 3, 1) => 50
      | (2, 3, 2) => 50
      | (2, 3, 3) => 50
      | (3, 1, 1) => 50
      | (3, 1, 2) => 50
      | (3, 1, 3) => 50
      | (3, 2, 1) => 50
      | (3, 2, 2) => 50
      | (3, 2, 3) => 50
      | (3, 3, 1) => 50
      | (3, 3, 2) => 50
      | (3, 3, 3) => 50
      | (4, 0, 1) => 50
      | (4, 0, 2) => 50
      | (4, 0, 3) => 50
      | (5, 0, 0) => 50
      | _ => 500
      end
      in
      bindGen (freq [
        (_weight_1, returnGen 1);
        (100-_weight_1, returnGen 0)
      ]) (fun n1 =>
      (* GenNat1 *) (let _weight_2 := match (size, stack1, stack2) with
      | (1, 1, 1) => 50
      | (1, 1, 2) => 50
      | (1, 1, 3) => 50
      | (1, 2, 1) => 50
      | (1, 2, 2) => 50
      | (1, 2, 3) => 50
      | (1, 3, 1) => 50
      | (1, 3, 2) => 50
      | (1, 3, 3) => 50
      | (2, 1, 1) => 50
      | (2, 1, 2) => 50
      | (2, 1, 3) => 50
      | (2, 2, 1) => 50
      | (2, 2, 2) => 50
      | (2, 2, 3) => 50
      | (2, 3, 1) => 50
      | (2, 3, 2) => 50
      | (2, 3, 3) => 50
      | (3, 1, 1) => 50
      | (3, 1, 2) => 50
      | (3, 1, 3) => 50
      | (3, 2, 1) => 50
      | (3, 2, 2) => 50
      | (3, 2, 3) => 50
      | (3, 3, 1) => 50
      | (3, 3, 2) => 50
      | (3, 3, 3) => 50
      | (4, 0, 1) => 50
      | (4, 0, 2) => 50
      | (4, 0, 3) => 50
      | (5, 0, 0) => 50
      | _ => 500
      end
      in
      bindGen (freq [
        (_weight_2, returnGen 2);
        (100-_weight_2, returnGen 0)
      ]) (fun n2 =>
      (* GenNat1 *) (let _weight_4 := match (size, stack1, stack2) with
      | (1, 1, 1) => 50
      | (1, 1, 2) => 50
      | (1, 1, 3) => 50
      | (1, 2, 1) => 50
      | (1, 2, 2) => 50
      | (1, 2, 3) => 50
      | (1, 3, 1) => 50
      | (1, 3, 2) => 50
      | (1, 3, 3) => 50
      | (2, 1, 1) => 50
      | (2, 1, 2) => 50
      | (2, 1, 3) => 50
      | (2, 2, 1) => 50
      | (2, 2, 2) => 50
      | (2, 2, 3) => 50
      | (2, 3, 1) => 50
      | (2, 3, 2) => 50
      | (2, 3, 3) => 50
      | (3, 1, 1) => 50
      | (3, 1, 2) => 50
      | (3, 1, 3) => 50
      | (3, 2, 1) => 50
      | (3, 2, 2) => 50
      | (3, 2, 3) => 50
      | (3, 3, 1) => 50
      | (3, 3, 2) => 50
      | (3, 3, 3) => 50
      | (4, 0, 1) => 50
      | (4, 0, 2) => 50
      | (4, 0, 3) => 50
      | (5, 0, 0) => 50
      | _ => 500
      end
      in
      bindGen (freq [
        (_weight_4, returnGen 4);
        (100-_weight_4, returnGen 0)
      ]) (fun n4 =>
      (* GenNat1 *) (let _weight_8 := match (size, stack1, stack2) with
      | (1, 1, 1) => 50
      | (1, 1, 2) => 50
      | (1, 1, 3) => 50
      | (1, 2, 1) => 50
      | (1, 2, 2) => 50
      | (1, 2, 3) => 50
      | (1, 3, 1) => 50
      | (1, 3, 2) => 50
      | (1, 3, 3) => 50
      | (2, 1, 1) => 50
      | (2, 1, 2) => 50
      | (2, 1, 3) => 50
      | (2, 2, 1) => 50
      | (2, 2, 2) => 50
      | (2, 2, 3) => 50
      | (2, 3, 1) => 50
      | (2, 3, 2) => 50
      | (2, 3, 3) => 50
      | (3, 1, 1) => 50
      | (3, 1, 2) => 50
      | (3, 1, 3) => 50
      | (3, 2, 1) => 50
      | (3, 2, 2) => 50
      | (3, 2, 3) => 50
      | (3, 3, 1) => 50
      | (3, 3, 2) => 50
      | (3, 3, 3) => 50
      | (4, 0, 1) => 50
      | (4, 0, 2) => 50
      | (4, 0, 3) => 50
      | (5, 0, 0) => 50
      | _ => 500
      end
      in
      bindGen (freq [
        (_weight_8, returnGen 8);
        (100-_weight_8, returnGen 0)
      ]) (fun n8 =>
      (* GenNat1 *) (let _weight_16 := match (size, stack1, stack2) with
      | (1, 1, 1) => 50
      | (1, 1, 2) => 50
      | (1, 1, 3) => 50
      | (1, 2, 1) => 50
      | (1, 2, 2) => 50
      | (1, 2, 3) => 50
      | (1, 3, 1) => 50
      | (1, 3, 2) => 50
      | (1, 3, 3) => 50
      | (2, 1, 1) => 50
      | (2, 1, 2) => 50
      | (2, 1, 3) => 50
      | (2, 2, 1) => 50
      | (2, 2, 2) => 50
      | (2, 2, 3) => 50
      | (2, 3, 1) => 50
      | (2, 3, 2) => 50
      | (2, 3, 3) => 50
      | (3, 1, 1) => 50
      | (3, 1, 2) => 50
      | (3, 1, 3) => 50
      | (3, 2, 1) => 50
      | (3, 2, 2) => 50
      | (3, 2, 3) => 50
      | (3, 3, 1) => 50
      | (3, 3, 2) => 50
      | (3, 3, 3) => 50
      | (4, 0, 1) => 50
      | (4, 0, 2) => 50
      | (4, 0, 3) => 50
      | (5, 0, 0) => 50
      | _ => 500
      end
      in
      bindGen (freq [
        (_weight_16, returnGen 16);
        (100-_weight_16, returnGen 0)
      ]) (fun n16 =>
      (* GenNat1 *) (let _weight_32 := match (size, stack1, stack2) with
      | (1, 1, 1) => 50
      | (1, 1, 2) => 50
      | (1, 1, 3) => 50
      | (1, 2, 1) => 50
      | (1, 2, 2) => 50
      | (1, 2, 3) => 50
      | (1, 3, 1) => 50
      | (1, 3, 2) => 50
      | (1, 3, 3) => 50
      | (2, 1, 1) => 50
      | (2, 1, 2) => 50
      | (2, 1, 3) => 50
      | (2, 2, 1) => 50
      | (2, 2, 2) => 50
      | (2, 2, 3) => 50
      | (2, 3, 1) => 50
      | (2, 3, 2) => 50
      | (2, 3, 3) => 50
      | (3, 1, 1) => 50
      | (3, 1, 2) => 50
      | (3, 1, 3) => 50
      | (3, 2, 1) => 50
      | (3, 2, 2) => 50
      | (3, 2, 3) => 50
      | (3, 3, 1) => 50
      | (3, 3, 2) => 50
      | (3, 3, 3) => 50
      | (4, 0, 1) => 50
      | (4, 0, 2) => 50
      | (4, 0, 3) => 50
      | (5, 0, 0) => 50
      | _ => 500
      end
      in
      bindGen (freq [
        (_weight_32, returnGen 32);
        (100-_weight_32, returnGen 0)
      ]) (fun n32 =>
        n1 + n2 + n4 + n8 + n16 + n32
      ))))))) 
      (fun p1 => (Var p1)))); 
      (match (size, stack1, stack2) with
      | (1, 1, 1) => 50
      | (1, 1, 2) => 50
      | (1, 1, 3) => 50
      | (1, 2, 1) => 50
      | (1, 2, 2) => 50
      | (1, 2, 3) => 50
      | (1, 3, 1) => 50
      | (1, 3, 2) => 50
      | (1, 3, 3) => 50
      | (2, 1, 1) => 50
      | (2, 1, 2) => 50
      | (2, 1, 3) => 50
      | (2, 2, 1) => 50
      | (2, 2, 2) => 50
      | (2, 2, 3) => 50
      | (2, 3, 1) => 50
      | (2, 3, 2) => 50
      | (2, 3, 3) => 50
      | (3, 1, 1) => 50
      | (3, 1, 2) => 50
      | (3, 1, 3) => 50
      | (3, 2, 1) => 50
      | (3, 2, 2) => 50
      | (3, 2, 3) => 50
      | (3, 3, 1) => 50
      | (3, 3, 2) => 50
      | (3, 3, 3) => 50
      | (4, 0, 1) => 50
      | (4, 0, 2) => 50
      | (4, 0, 3) => 50
      | (5, 0, 0) => 50
      | _ => 500
      end,
      (bindGen 
      (* GenBool1 *) (let _weight_true := match (size, stack1, stack2) with
      | (1, 1, 1) => 50
      | (1, 1, 2) => 50
      | (1, 1, 3) => 50
      | (1, 2, 1) => 50
      | (1, 2, 2) => 50
      | (1, 2, 3) => 50
      | (1, 3, 1) => 50
      | (1, 3, 2) => 50
      | (1, 3, 3) => 50
      | (2, 1, 1) => 50
      | (2, 1, 2) => 50
      | (2, 1, 3) => 50
      | (2, 2, 1) => 50
      | (2, 2, 2) => 50
      | (2, 2, 3) => 50
      | (2, 3, 1) => 50
      | (2, 3, 2) => 50
      | (2, 3, 3) => 50
      | (3, 1, 1) => 50
      | (3, 1, 2) => 50
      | (3, 1, 3) => 50
      | (3, 2, 1) => 50
      | (3, 2, 2) => 50
      | (3, 2, 3) => 50
      | (3, 3, 1) => 50
      | (3, 3, 2) => 50
      | (3, 3, 3) => 50
      | (4, 0, 1) => 50
      | (4, 0, 2) => 50
      | (4, 0, 3) => 50
      | (5, 0, 0) => 50
      | _ => 500
      end
      in
      freq [
        (_weight_true, returnGen true);
        (100-_weight_true, returnGen false)
      ]) 
      (fun p1 => (Bool p1)))); 
      (match (size, stack1, stack2) with
      | (1, 1, 1) => 50
      | (1, 1, 2) => 50
      | (1, 1, 3) => 50
      | (1, 2, 1) => 50
      | (1, 2, 2) => 50
      | (1, 2, 3) => 50
      | (1, 3, 1) => 50
      | (1, 3, 2) => 50
      | (1, 3, 3) => 50
      | (2, 1, 1) => 50
      | (2, 1, 2) => 50
      | (2, 1, 3) => 50
      | (2, 2, 1) => 50
      | (2, 2, 2) => 50
      | (2, 2, 3) => 50
      | (2, 3, 1) => 50
      | (2, 3, 2) => 50
      | (2, 3, 3) => 50
      | (3, 1, 1) => 50
      | (3, 1, 2) => 50
      | (3, 1, 3) => 50
      | (3, 2, 1) => 50
      | (3, 2, 2) => 50
      | (3, 2, 3) => 50
      | (3, 3, 1) => 50
      | (3, 3, 2) => 50
      | (3, 3, 3) => 50
      | (4, 0, 1) => 50
      | (4, 0, 2) => 50
      | (4, 0, 3) => 50
      | (5, 0, 0) => 50
      | _ => 500
      end,
      (bindGen (genTyp 2 stack2 4) 
      (fun p1 => 
        (bindGen (genExpr size1 stack2 3) 
        (fun p2 => (Abs p1 p2)))))); 
      (match (size, stack1, stack2) with
      | (1, 1, 1) => 50
      | (1, 1, 2) => 50
      | (1, 1, 3) => 50
      | (1, 2, 1) => 50
      | (1, 2, 2) => 50
      | (1, 2, 3) => 50
      | (1, 3, 1) => 50
      | (1, 3, 2) => 50
      | (1, 3, 3) => 50
      | (2, 1, 1) => 50
      | (2, 1, 2) => 50
      | (2, 1, 3) => 50
      | (2, 2, 1) => 50
      | (2, 2, 2) => 50
      | (2, 2, 3) => 50
      | (2, 3, 1) => 50
      | (2, 3, 2) => 50
      | (2, 3, 3) => 50
      | (3, 1, 1) => 50
      | (3, 1, 2) => 50
      | (3, 1, 3) => 50
      | (3, 2, 1) => 50
      | (3, 2, 2) => 50
      | (3, 2, 3) => 50
      | (3, 3, 1) => 50
      | (3, 3, 2) => 50
      | (3, 3, 3) => 50
      | (4, 0, 1) => 50
      | (4, 0, 2) => 50
      | (4, 0, 3) => 50
      | (5, 0, 0) => 50
      | _ => 500
      end,
      (bindGen (genExpr size1 stack2 2) 
      (fun p1 => 
        (bindGen (genExpr size1 stack2 1) 
        (fun p2 => (App p1 p2))))))])
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
          