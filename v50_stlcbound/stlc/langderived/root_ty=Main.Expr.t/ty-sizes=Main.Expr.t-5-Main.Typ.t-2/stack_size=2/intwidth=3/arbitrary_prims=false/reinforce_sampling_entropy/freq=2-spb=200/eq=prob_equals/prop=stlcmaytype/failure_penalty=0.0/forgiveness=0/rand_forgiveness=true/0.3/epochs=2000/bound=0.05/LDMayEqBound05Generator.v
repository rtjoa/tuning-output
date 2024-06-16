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
      | (1, 2, 1) => 95
      | (1, 2, 4) => 93
      | (2, 0, 2) => 12
      | (2, 3, 2) => 34
      | (2, 5, 2) => 18
      | (2, 6, 2) => 26
      | _ => 500
      end,
      (returnGen (TBool ))); 
      (* TFun *) (match (size, stack1, stack2) with
      | (1, 2, 1) => 63
      | (1, 2, 4) => 90
      | (2, 0, 2) => 91
      | (2, 3, 2) => 94
      | (2, 5, 2) => 92
      | (2, 6, 2) => 94
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
      | (0, 3, 3) => 95
      | (0, 3, 5) => 93
      | (0, 3, 6) => 92
      | (0, 5, 3) => 95
      | (0, 5, 5) => 92
      | (0, 5, 6) => 85
      | (0, 6, 3) => 95
      | (0, 6, 5) => 95
      | (0, 6, 6) => 90
      | _ => 500
      end,
      (bindGen 
      (* GenNat1 *)
      (let _weight_1 := match (size, stack1, stack2) with
      | (0, 3, 3) => 24
      | (0, 3, 5) => 5
      | (0, 3, 6) => 40
      | (0, 5, 3) => 65
      | (0, 5, 5) => 73
      | (0, 5, 6) => 6
      | (0, 6, 3) => 62
      | (0, 6, 5) => 21
      | (0, 6, 6) => 20
      | _ => 500
      end
      in
      bindGen (freq [
        (_weight_1, returnGen 1);
        (100-_weight_1, returnGen 0)
      ]) (fun n1 =>
      (let _weight_2 := match (size, stack1, stack2) with
      | (0, 3, 3) => 43
      | (0, 3, 5) => 88
      | (0, 3, 6) => 19
      | (0, 5, 3) => 64
      | (0, 5, 5) => 57
      | (0, 5, 6) => 92
      | (0, 6, 3) => 13
      | (0, 6, 5) => 88
      | (0, 6, 6) => 45
      | _ => 500
      end
      in
      bindGen (freq [
        (_weight_2, returnGen 2);
        (100-_weight_2, returnGen 0)
      ]) (fun n2 =>
      (let _weight_4 := match (size, stack1, stack2) with
      | (0, 3, 3) => 65
      | (0, 3, 5) => 91
      | (0, 3, 6) => 24
      | (0, 5, 3) => 59
      | (0, 5, 5) => 21
      | (0, 5, 6) => 55
      | (0, 6, 3) => 15
      | (0, 6, 5) => 55
      | (0, 6, 6) => 25
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
      | (0, 3, 3) => 5
      | (0, 3, 5) => 15
      | (0, 3, 6) => 14
      | (0, 5, 3) => 5
      | (0, 5, 5) => 52
      | (0, 5, 6) => 20
      | (0, 6, 3) => 5
      | (0, 6, 5) => 5
      | (0, 6, 6) => 12
      | _ => 500
      end,
      (bindGen 
      (* GenBool1 *) (let _weight_true := match (size, stack1, stack2) with
      | (0, 3, 3) => 50
      | (0, 3, 5) => 62
      | (0, 3, 6) => 46
      | (0, 5, 3) => 50
      | (0, 5, 5) => 49
      | (0, 5, 6) => 85
      | (0, 6, 3) => 50
      | (0, 6, 5) => 8
      | (0, 6, 6) => 79
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
      | (1, 3, 3) => 88
      | (1, 3, 5) => 34
      | (1, 3, 6) => 38
      | (1, 5, 3) => 54
      | (1, 5, 5) => 6
      | (1, 5, 6) => 16
      | (1, 6, 3) => 28
      | (1, 6, 5) => 10
      | (1, 6, 6) => 26
      | (2, 3, 3) => 13
      | (2, 3, 5) => 6
      | (2, 3, 6) => 6
      | (2, 5, 3) => 5
      | (2, 5, 5) => 6
      | (2, 5, 6) => 6
      | (2, 6, 3) => 11
      | (2, 6, 5) => 15
      | (2, 6, 6) => 9
      | (3, 3, 3) => 5
      | (3, 3, 5) => 5
      | (3, 3, 6) => 5
      | (3, 5, 3) => 5
      | (3, 5, 5) => 5
      | (3, 5, 6) => 5
      | (3, 6, 3) => 5
      | (3, 6, 5) => 5
      | (3, 6, 6) => 5
      | (4, 0, 3) => 5
      | (4, 0, 5) => 5
      | (4, 0, 6) => 5
      | (5, 0, 0) => 5
      | _ => 500
      end,
      (bindGen 
      (* GenNat2 *)
      (let _weight_1 := match (size, stack1, stack2) with
      | (1, 3, 3) => 20
      | (1, 3, 5) => 80
      | (1, 3, 6) => 90
      | (1, 5, 3) => 66
      | (1, 5, 5) => 84
      | (1, 5, 6) => 61
      | (1, 6, 3) => 30
      | (1, 6, 5) => 75
      | (1, 6, 6) => 85
      | (2, 3, 3) => 40
      | (2, 3, 5) => 37
      | (2, 3, 6) => 91
      | (2, 5, 3) => 27
      | (2, 5, 5) => 81
      | (2, 5, 6) => 77
      | (2, 6, 3) => 17
      | (2, 6, 5) => 89
      | (2, 6, 6) => 45
      | (3, 3, 3) => 50
      | (3, 3, 5) => 37
      | (3, 3, 6) => 50
      | (3, 5, 3) => 27
      | (3, 5, 5) => 42
      | (3, 5, 6) => 56
      | (3, 6, 3) => 50
      | (3, 6, 5) => 23
      | (3, 6, 6) => 50
      | (4, 0, 3) => 50
      | (4, 0, 5) => 51
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
      | (1, 3, 3) => 38
      | (1, 3, 5) => 84
      | (1, 3, 6) => 63
      | (1, 5, 3) => 16
      | (1, 5, 5) => 14
      | (1, 5, 6) => 67
      | (1, 6, 3) => 66
      | (1, 6, 5) => 27
      | (1, 6, 6) => 53
      | (2, 3, 3) => 19
      | (2, 3, 5) => 28
      | (2, 3, 6) => 74
      | (2, 5, 3) => 47
      | (2, 5, 5) => 50
      | (2, 5, 6) => 94
      | (2, 6, 3) => 10
      | (2, 6, 5) => 80
      | (2, 6, 6) => 36
      | (3, 3, 3) => 50
      | (3, 3, 5) => 40
      | (3, 3, 6) => 50
      | (3, 5, 3) => 69
      | (3, 5, 5) => 53
      | (3, 5, 6) => 93
      | (3, 6, 3) => 50
      | (3, 6, 5) => 18
      | (3, 6, 6) => 50
      | (4, 0, 3) => 50
      | (4, 0, 5) => 53
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
      | (1, 3, 3) => 80
      | (1, 3, 5) => 14
      | (1, 3, 6) => 55
      | (1, 5, 3) => 38
      | (1, 5, 5) => 36
      | (1, 5, 6) => 61
      | (1, 6, 3) => 5
      | (1, 6, 5) => 91
      | (1, 6, 6) => 40
      | (2, 3, 3) => 20
      | (2, 3, 5) => 66
      | (2, 3, 6) => 43
      | (2, 5, 3) => 73
      | (2, 5, 5) => 23
      | (2, 5, 6) => 41
      | (2, 6, 3) => 35
      | (2, 6, 5) => 37
      | (2, 6, 6) => 12
      | (3, 3, 3) => 50
      | (3, 3, 5) => 51
      | (3, 3, 6) => 50
      | (3, 5, 3) => 53
      | (3, 5, 5) => 46
      | (3, 5, 6) => 67
      | (3, 6, 3) => 50
      | (3, 6, 5) => 84
      | (3, 6, 6) => 50
      | (4, 0, 3) => 50
      | (4, 0, 5) => 54
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
      | (1, 3, 3) => 5
      | (1, 3, 5) => 35
      | (1, 3, 6) => 7
      | (1, 5, 3) => 5
      | (1, 5, 5) => 40
      | (1, 5, 6) => 6
      | (1, 6, 3) => 5
      | (1, 6, 5) => 6
      | (1, 6, 6) => 7
      | (2, 3, 3) => 5
      | (2, 3, 5) => 6
      | (2, 3, 6) => 6
      | (2, 5, 3) => 5
      | (2, 5, 5) => 5
      | (2, 5, 6) => 5
      | (2, 6, 3) => 5
      | (2, 6, 5) => 5
      | (2, 6, 6) => 5
      | (3, 3, 3) => 5
      | (3, 3, 5) => 5
      | (3, 3, 6) => 11
      | (3, 5, 3) => 5
      | (3, 5, 5) => 5
      | (3, 5, 6) => 5
      | (3, 6, 3) => 5
      | (3, 6, 5) => 5
      | (3, 6, 6) => 9
      | (4, 0, 3) => 5
      | (4, 0, 5) => 5
      | (4, 0, 6) => 5
      | (5, 0, 0) => 5
      | _ => 500
      end,
      (bindGen 
      (* GenBool2 *) (let _weight_true := match (size, stack1, stack2) with
      | (1, 3, 3) => 50
      | (1, 3, 5) => 34
      | (1, 3, 6) => 17
      | (1, 5, 3) => 50
      | (1, 5, 5) => 68
      | (1, 5, 6) => 22
      | (1, 6, 3) => 50
      | (1, 6, 5) => 39
      | (1, 6, 6) => 24
      | (2, 3, 3) => 50
      | (2, 3, 5) => 46
      | (2, 3, 6) => 68
      | (2, 5, 3) => 50
      | (2, 5, 5) => 62
      | (2, 5, 6) => 69
      | (2, 6, 3) => 50
      | (2, 6, 5) => 53
      | (2, 6, 6) => 81
      | (3, 3, 3) => 50
      | (3, 3, 5) => 92
      | (3, 3, 6) => 12
      | (3, 5, 3) => 50
      | (3, 5, 5) => 53
      | (3, 5, 6) => 27
      | (3, 6, 3) => 50
      | (3, 6, 5) => 81
      | (3, 6, 6) => 81
      | (4, 0, 3) => 50
      | (4, 0, 5) => 46
      | (4, 0, 6) => 7
      | (5, 0, 0) => 57
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
      | (1, 3, 3) => 95
      | (1, 3, 5) => 94
      | (1, 3, 6) => 95
      | (1, 5, 3) => 95
      | (1, 5, 5) => 92
      | (1, 5, 6) => 94
      | (1, 6, 3) => 95
      | (1, 6, 5) => 94
      | (1, 6, 6) => 94
      | (2, 3, 3) => 95
      | (2, 3, 5) => 25
      | (2, 3, 6) => 83
      | (2, 5, 3) => 95
      | (2, 5, 5) => 49
      | (2, 5, 6) => 84
      | (2, 6, 3) => 95
      | (2, 6, 5) => 89
      | (2, 6, 6) => 78
      | (3, 3, 3) => 95
      | (3, 3, 5) => 7
      | (3, 3, 6) => 95
      | (3, 5, 3) => 17
      | (3, 5, 5) => 8
      | (3, 5, 6) => 9
      | (3, 6, 3) => 95
      | (3, 6, 5) => 5
      | (3, 6, 6) => 95
      | (4, 0, 3) => 95
      | (4, 0, 5) => 5
      | (4, 0, 6) => 95
      | (5, 0, 0) => 95
      | _ => 500
      end,
      (bindGen (genTyp 2 stack2 2) 
      (fun p1 => 
        (bindGen (genExpr size1 stack2 5) 
        (fun p2 => 
          (returnGen (Abs p1 p2))))))); 
      (* App *) (match (size, stack1, stack2) with
      | (1, 3, 3) => 89
      | (1, 3, 5) => 6
      | (1, 3, 6) => 30
      | (1, 5, 3) => 92
      | (1, 5, 5) => 11
      | (1, 5, 6) => 6
      | (1, 6, 3) => 84
      | (1, 6, 5) => 27
      | (1, 6, 6) => 23
      | (2, 3, 3) => 95
      | (2, 3, 5) => 95
      | (2, 3, 6) => 94
      | (2, 5, 3) => 95
      | (2, 5, 5) => 91
      | (2, 5, 6) => 95
      | (2, 6, 3) => 95
      | (2, 6, 5) => 86
      | (2, 6, 6) => 94
      | (3, 3, 3) => 5
      | (3, 3, 5) => 95
      | (3, 3, 6) => 5
      | (3, 5, 3) => 95
      | (3, 5, 5) => 95
      | (3, 5, 6) => 95
      | (3, 6, 3) => 5
      | (3, 6, 5) => 95
      | (3, 6, 6) => 5
      | (4, 0, 3) => 66
      | (4, 0, 5) => 95
      | (4, 0, 6) => 14
      | (5, 0, 0) => 95
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
          
