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
      | (0, 3, 5) => 81
      | (0, 3, 6) => 81
      | (0, 5, 3) => 88
      | (0, 5, 5) => 58
      | (0, 5, 6) => 53
      | (0, 6, 3) => 90
      | (0, 6, 5) => 73
      | (0, 6, 6) => 67
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
      | (0, 3, 3) => 0
      | (0, 3, 5) => 77
      | (0, 3, 6) => 76
      | (0, 5, 3) => 0
      | (0, 5, 5) => 64
      | (0, 5, 6) => 65
      | (0, 6, 3) => 0
      | (0, 6, 5) => 80
      | (0, 6, 6) => 82
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
      | (1, 3, 3) => 35
      | (1, 3, 5) => 31
      | (1, 3, 6) => 67
      | (1, 5, 3) => 51
      | (1, 5, 5) => 30
      | (1, 5, 6) => 40
      | (1, 6, 3) => 52
      | (1, 6, 5) => 33
      | (1, 6, 6) => 60
      | (2, 3, 3) => 4
      | (2, 3, 5) => 11
      | (2, 3, 6) => 2
      | (2, 5, 3) => 56
      | (2, 5, 5) => 50
      | (2, 5, 6) => 40
      | (2, 6, 3) => 2
      | (2, 6, 5) => 12
      | (2, 6, 6) => 3
      | (3, 3, 3) => 47
      | (3, 3, 5) => 52
      | (3, 3, 6) => 47
      | (3, 5, 3) => 0
      | (3, 5, 5) => 20
      | (3, 5, 6) => 0
      | (3, 6, 3) => 48
      | (3, 6, 5) => 48
      | (3, 6, 6) => 48
      | (4, 0, 3) => 22
      | (4, 0, 5) => 0
      | (4, 0, 6) => 23
      | (5, 0, 0) => 0
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
      (let _weight_8 := match (size, stack1, stack2) with
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
        (_weight_8, returnGen 8);
        (100-_weight_8, returnGen 0)
      ]) (fun n8 =>
      (let _weight_16 := match (size, stack1, stack2) with
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
        (_weight_16, returnGen 16);
        (100-_weight_16, returnGen 0)
      ]) (fun n16 =>
      (let _weight_32 := match (size, stack1, stack2) with
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
        (_weight_32, returnGen 32);
        (100-_weight_32, returnGen 0)
      ]) (fun n32 =>
        returnGen (n1 + n2 + n4 + n8 + n16 + n32)
      )))))))))))) 
      (fun p1 => 
        (returnGen (Var p1))))); 
      (* Bool *) (match (size, stack1, stack2) with
      | (1, 3, 3) => 0
      | (1, 3, 5) => 31
      | (1, 3, 6) => 35
      | (1, 5, 3) => 1
      | (1, 5, 5) => 45
      | (1, 5, 6) => 52
      | (1, 6, 3) => 0
      | (1, 6, 5) => 42
      | (1, 6, 6) => 50
      | (2, 3, 3) => 0
      | (2, 3, 5) => 8
      | (2, 3, 6) => 5
      | (2, 5, 3) => 10
      | (2, 5, 5) => 42
      | (2, 5, 6) => 52
      | (2, 6, 3) => 0
      | (2, 6, 5) => 16
      | (2, 6, 6) => 3
      | (3, 3, 3) => 47
      | (3, 3, 5) => 44
      | (3, 3, 6) => 52
      | (3, 5, 3) => 0
      | (3, 5, 5) => 23
      | (3, 5, 6) => 0
      | (3, 6, 3) => 48
      | (3, 6, 5) => 50
      | (3, 6, 6) => 52
      | (4, 0, 3) => 22
      | (4, 0, 5) => 0
      | (4, 0, 6) => 61
      | (5, 0, 0) => 0
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
      | (1, 3, 3) => 80
      | (1, 3, 5) => 82
      | (1, 3, 6) => 87
      | (1, 5, 3) => 80
      | (1, 5, 5) => 68
      | (1, 5, 6) => 63
      | (1, 6, 3) => 91
      | (1, 6, 5) => 74
      | (1, 6, 6) => 88
      | (2, 3, 3) => 31
      | (2, 3, 5) => 35
      | (2, 3, 6) => 20
      | (2, 5, 3) => 65
      | (2, 5, 5) => 55
      | (2, 5, 6) => 48
      | (2, 6, 3) => 15
      | (2, 6, 5) => 31
      | (2, 6, 6) => 15
      | (3, 3, 3) => 57
      | (3, 3, 5) => 54
      | (3, 3, 6) => 53
      | (3, 5, 3) => 2
      | (3, 5, 5) => 59
      | (3, 5, 6) => 1
      | (3, 6, 3) => 54
      | (3, 6, 5) => 49
      | (3, 6, 6) => 51
      | (4, 0, 3) => 83
      | (4, 0, 5) => 0
      | (4, 0, 6) => 72
      | (5, 0, 0) => 96
      | _ => 500
      end,
      (bindGen (genTyp 2 stack2 2) 
      (fun p1 => 
        (bindGen (genExpr size1 stack2 5) 
        (fun p2 => 
          (returnGen (Abs p1 p2))))))); 
      (* App *) (match (size, stack1, stack2) with
      | (1, 3, 3) => 94
      | (1, 3, 5) => 67
      | (1, 3, 6) => 83
      | (1, 5, 3) => 66
      | (1, 5, 5) => 52
      | (1, 5, 6) => 46
      | (1, 6, 3) => 88
      | (1, 6, 5) => 74
      | (1, 6, 6) => 79
      | (2, 3, 3) => 94
      | (2, 3, 5) => 87
      | (2, 3, 6) => 92
      | (2, 5, 3) => 63
      | (2, 5, 5) => 53
      | (2, 5, 6) => 59
      | (2, 6, 3) => 95
      | (2, 6, 5) => 86
      | (2, 6, 6) => 93
      | (3, 3, 3) => 48
      | (3, 3, 5) => 50
      | (3, 3, 6) => 47
      | (3, 5, 3) => 95
      | (3, 5, 5) => 76
      | (3, 5, 6) => 95
      | (3, 6, 3) => 50
      | (3, 6, 5) => 54
      | (3, 6, 6) => 50
      | (4, 0, 3) => 30
      | (4, 0, 5) => 96
      | (4, 0, 6) => 29
      | (5, 0, 0) => 0
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
          
