From QuickChick Require Import QuickChick. Import QcNotation.
From Coq Require Import Bool ZArith List. Import ListNotations.
From ExtLib Require Import Monad.
From ExtLib.Data.Monads Require Import OptionMonad.
Import MonadNotation.

From STLC Require Import Impl Spec.

Inductive LeafCtorExpr :=
  | LeafCtorExpr_Var
  | LeafCtorExpr_Bool.

Inductive CtorTyp :=
  | CtorTyp_TBool
  | CtorTyp_TFun.

Inductive CtorExpr :=
  | CtorExpr_Var
  | CtorExpr_Bool
  | CtorExpr_Abs
  | CtorExpr_App.

Inductive LeafCtorTyp :=
  | LeafCtorTyp_TBool.

Inductive TupCtorTypLeafCtorExpr :=
  | MkCtorTypLeafCtorExpr : CtorTyp -> LeafCtorExpr -> TupCtorTypLeafCtorExpr.

Inductive TupLeafCtorTypLeafCtorTyp :=
  | MkLeafCtorTypLeafCtorTyp : LeafCtorTyp -> LeafCtorTyp -> TupLeafCtorTypLeafCtorTyp.

Inductive TupCtorTypCtorExpr :=
  | MkCtorTypCtorExpr : CtorTyp -> CtorExpr -> TupCtorTypCtorExpr.

Inductive TupCtorExprCtorExpr :=
  | MkCtorExprCtorExpr : CtorExpr -> CtorExpr -> TupCtorExprCtorExpr.

Inductive TupLeafCtorExprLeafCtorExpr :=
  | MkLeafCtorExprLeafCtorExpr : LeafCtorExpr -> LeafCtorExpr -> TupLeafCtorExprLeafCtorExpr.

Inductive TupCtorTypCtorTyp :=
  | MkCtorTypCtorTyp : CtorTyp -> CtorTyp -> TupCtorTypCtorTyp.

Definition genLeafTyp (chosen_ctor : LeafCtorTyp) (stack1 : nat) (stack2 : nat) : G (Typ) :=
  match chosen_ctor with
  | LeafCtorTyp_TBool => 
    (returnGen (TBool ))
  end.

Fixpoint genTyp (size : nat) (chosen_ctor : CtorTyp) (stack1 : nat) (stack2 : nat) : G (Typ) :=
  match size with
  | O  => match chosen_ctor with
    | CtorTyp_TBool => 
      (returnGen (TBool ))
    | CtorTyp_TFun => 
      (bindGen 
      (* Frequency2 (single-branch) *) 
      (returnGen (MkLeafCtorTypLeafCtorTyp LeafCtorTyp_TBool LeafCtorTyp_TBool)) 
      (fun param_variantis => (let '(MkLeafCtorTypLeafCtorTyp ctor1 ctor2) := param_variantis in

        (bindGen (genLeafTyp ctor1 stack2 1) 
        (fun p1 => 
          (bindGen (genLeafTyp ctor2 stack2 7) 
          (fun p2 => 
            (returnGen (TFun p1 p2)))))))))
    end
  | S size1 => match chosen_ctor with
    | CtorTyp_TBool => 
      (returnGen (TBool ))
    | CtorTyp_TFun => 
      (bindGen 
      (* Frequency3 *) (freq [
        (* 1 *) (match (size, stack1, stack2) with
        | (1, 0, 5) => 61
        | (1, 11, 3) => 48
        | (1, 11, 5) => 55
        | (1, 12, 3) => 52
        | (1, 12, 5) => 53
        | (1, 6, 3) => 57
        | (1, 6, 5) => 57
        | _ => 500
        end,
        (returnGen (MkCtorTypCtorTyp CtorTyp_TBool CtorTyp_TBool))); 
        (* 2 *) (match (size, stack1, stack2) with
        | (1, 0, 5) => 57
        | (1, 11, 3) => 50
        | (1, 11, 5) => 48
        | (1, 12, 3) => 49
        | (1, 12, 5) => 49
        | (1, 6, 3) => 49
        | (1, 6, 5) => 47
        | _ => 500
        end,
        (returnGen (MkCtorTypCtorTyp CtorTyp_TFun CtorTyp_TBool))); 
        (* 3 *) (match (size, stack1, stack2) with
        | (1, 0, 5) => 54
        | (1, 11, 3) => 48
        | (1, 11, 5) => 77
        | (1, 12, 3) => 49
        | (1, 12, 5) => 49
        | (1, 6, 3) => 48
        | (1, 6, 5) => 51
        | _ => 500
        end,
        (returnGen (MkCtorTypCtorTyp CtorTyp_TBool CtorTyp_TFun))); 
        (* 4 *) (match (size, stack1, stack2) with
        | (1, 0, 5) => 47
        | (1, 11, 3) => 63
        | (1, 11, 5) => 50
        | (1, 12, 3) => 49
        | (1, 12, 5) => 49
        | (1, 6, 3) => 46
        | (1, 6, 5) => 45
        | _ => 500
        end,
        (returnGen (MkCtorTypCtorTyp CtorTyp_TFun CtorTyp_TFun)))]) 
      (fun param_variantis => (let '(MkCtorTypCtorTyp ctor1 ctor2) := param_variantis in

        (bindGen (genTyp size1 ctor1 stack2 2) 
        (fun p1 => 
          (bindGen (genTyp size1 ctor2 stack2 8) 
          (fun p2 => 
            (returnGen (TFun p1 p2)))))))))
    end
  end.

Definition genLeafExpr (chosen_ctor : LeafCtorExpr) (stack1 : nat) (stack2 : nat) : G (Expr) :=
  match chosen_ctor with
  | LeafCtorExpr_Var => 
    (bindGen 
    (* GenNat1 *)
    (let _weight_1 := match (stack1, stack2) with
    | (11, 10) => 51
    | (11, 4) => 40
    | (11, 9) => 18
    | (12, 10) => 50
    | (12, 4) => 49
    | (12, 9) => 45
    | (6, 10) => 49
    | (6, 4) => 50
    | (6, 9) => 44
    | _ => 500
    end
    in
    bindGen (freq [
      (_weight_1, returnGen 1);
      (100-_weight_1, returnGen 0)
    ]) (fun n1 =>
    (let _weight_2 := match (stack1, stack2) with
    | (11, 10) => 49
    | (11, 4) => 54
    | (11, 9) => 22
    | (12, 10) => 50
    | (12, 4) => 49
    | (12, 9) => 51
    | (6, 10) => 51
    | (6, 4) => 49
    | (6, 9) => 54
    | _ => 500
    end
    in
    bindGen (freq [
      (_weight_2, returnGen 2);
      (100-_weight_2, returnGen 0)
    ]) (fun n2 =>
    (let _weight_4 := match (stack1, stack2) with
    | (11, 10) => 36
    | (11, 4) => 10
    | (11, 9) => 10
    | (12, 10) => 50
    | (12, 4) => 47
    | (12, 9) => 42
    | (6, 10) => 49
    | (6, 4) => 47
    | (6, 9) => 13
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
      (returnGen (Var p1))))
  | LeafCtorExpr_Bool => 
    (bindGen 
    (* GenBool1 *) (let _weight_true := match (stack1, stack2) with
    | (11, 10) => 48
    | (11, 4) => 50
    | (11, 9) => 40
    | (12, 10) => 49
    | (12, 4) => 50
    | (12, 9) => 52
    | (6, 10) => 50
    | (6, 4) => 50
    | (6, 9) => 56
    | _ => 500
    end
    in
    freq [
      (_weight_true, returnGen true);
      (100-_weight_true, returnGen false)
    ]) 
    (fun p1 => 
      (returnGen (Bool p1))))
  end.

Fixpoint genExpr (size : nat) (chosen_ctor : CtorExpr) (stack1 : nat) (stack2 : nat) : G (Expr) :=
  match size with
  | O  => match chosen_ctor with
    | CtorExpr_Var => 
      (bindGen 
      (* GenNat2 *)
      (let _weight_1 := match (stack1, stack2) with
      | (11, 11) => 53
      | (11, 12) => 40
      | (11, 6) => 33
      | (12, 11) => 49
      | (12, 12) => 50
      | (12, 6) => 51
      | (6, 11) => 36
      | (6, 12) => 50
      | (6, 6) => 49
      | _ => 500
      end
      in
      bindGen (freq [
        (_weight_1, returnGen 1);
        (100-_weight_1, returnGen 0)
      ]) (fun n1 =>
      (let _weight_2 := match (stack1, stack2) with
      | (11, 11) => 34
      | (11, 12) => 33
      | (11, 6) => 42
      | (12, 11) => 50
      | (12, 12) => 50
      | (12, 6) => 49
      | (6, 11) => 45
      | (6, 12) => 50
      | (6, 6) => 49
      | _ => 500
      end
      in
      bindGen (freq [
        (_weight_2, returnGen 2);
        (100-_weight_2, returnGen 0)
      ]) (fun n2 =>
      (let _weight_4 := match (stack1, stack2) with
      | (11, 11) => 10
      | (11, 12) => 23
      | (11, 6) => 21
      | (12, 11) => 47
      | (12, 12) => 50
      | (12, 6) => 49
      | (6, 11) => 29
      | (6, 12) => 50
      | (6, 6) => 49
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
        (returnGen (Var p1))))
    | CtorExpr_Bool => 
      (bindGen 
      (* GenBool2 *) (let _weight_true := match (stack1, stack2) with
      | (11, 11) => 44
      | (11, 12) => 48
      | (11, 6) => 50
      | (12, 11) => 51
      | (12, 12) => 51
      | (12, 6) => 50
      | (6, 11) => 57
      | (6, 12) => 50
      | (6, 6) => 50
      | _ => 500
      end
      in
      freq [
        (_weight_true, returnGen true);
        (100-_weight_true, returnGen false)
      ]) 
      (fun p1 => 
        (returnGen (Bool p1))))
    | CtorExpr_Abs => 
      (bindGen 
      (* Frequency4 *) (freq [
        (* 1 *) (match (stack1, stack2) with
        | (11, 11) => 19
        | (11, 12) => 51
        | (11, 6) => 66
        | (12, 11) => 50
        | (12, 12) => 50
        | (12, 6) => 51
        | (6, 11) => 46
        | (6, 12) => 50
        | (6, 6) => 50
        | _ => 500
        end,
        (returnGen (MkCtorTypLeafCtorExpr CtorTyp_TBool LeafCtorExpr_Var))); 
        (* 2 *) (match (stack1, stack2) with
        | (11, 11) => 66
        | (11, 12) => 45
        | (11, 6) => 18
        | (12, 11) => 50
        | (12, 12) => 50
        | (12, 6) => 48
        | (6, 11) => 50
        | (6, 12) => 50
        | (6, 6) => 50
        | _ => 500
        end,
        (returnGen (MkCtorTypLeafCtorExpr CtorTyp_TFun LeafCtorExpr_Var))); 
        (* 3 *) (match (stack1, stack2) with
        | (11, 11) => 13
        | (11, 12) => 58
        | (11, 6) => 75
        | (12, 11) => 51
        | (12, 12) => 50
        | (12, 6) => 53
        | (6, 11) => 45
        | (6, 12) => 50
        | (6, 6) => 50
        | _ => 500
        end,
        (returnGen (MkCtorTypLeafCtorExpr CtorTyp_TBool LeafCtorExpr_Bool))); 
        (* 4 *) (match (stack1, stack2) with
        | (11, 11) => 81
        | (11, 12) => 45
        | (11, 6) => 19
        | (12, 11) => 50
        | (12, 12) => 50
        | (12, 6) => 48
        | (6, 11) => 58
        | (6, 12) => 50
        | (6, 6) => 50
        | _ => 500
        end,
        (returnGen (MkCtorTypLeafCtorExpr CtorTyp_TFun LeafCtorExpr_Bool)))]) 
      (fun param_variantis => (let '(MkCtorTypLeafCtorExpr ctor1 ctor2) := param_variantis in

        (bindGen (genTyp 1 ctor1 stack2 3) 
        (fun p1 => 
          (bindGen (genLeafExpr ctor2 stack2 9) 
          (fun p2 => 
            (returnGen (Abs p1 p2)))))))))
    | CtorExpr_App => 
      (bindGen 
      (* Frequency5 *) (freq [
        (* 1 *) (match (stack1, stack2) with
        | (11, 11) => 33
        | (11, 12) => 49
        | (11, 6) => 50
        | (12, 11) => 50
        | (12, 12) => 50
        | (12, 6) => 50
        | (6, 11) => 51
        | (6, 12) => 50
        | (6, 6) => 50
        | _ => 500
        end,
        (returnGen (MkLeafCtorExprLeafCtorExpr LeafCtorExpr_Var LeafCtorExpr_Var))); 
        (* 2 *) (match (stack1, stack2) with
        | (11, 11) => 21
        | (11, 12) => 49
        | (11, 6) => 49
        | (12, 11) => 50
        | (12, 12) => 50
        | (12, 6) => 50
        | (6, 11) => 50
        | (6, 12) => 50
        | (6, 6) => 50
        | _ => 500
        end,
        (returnGen (MkLeafCtorExprLeafCtorExpr LeafCtorExpr_Bool LeafCtorExpr_Var))); 
        (* 3 *) (match (stack1, stack2) with
        | (11, 11) => 83
        | (11, 12) => 52
        | (11, 6) => 52
        | (12, 11) => 51
        | (12, 12) => 50
        | (12, 6) => 50
        | (6, 11) => 50
        | (6, 12) => 50
        | (6, 6) => 50
        | _ => 500
        end,
        (returnGen (MkLeafCtorExprLeafCtorExpr LeafCtorExpr_Var LeafCtorExpr_Bool))); 
        (* 4 *) (match (stack1, stack2) with
        | (11, 11) => 21
        | (11, 12) => 49
        | (11, 6) => 49
        | (12, 11) => 50
        | (12, 12) => 50
        | (12, 6) => 50
        | (6, 11) => 50
        | (6, 12) => 50
        | (6, 6) => 50
        | _ => 500
        end,
        (returnGen (MkLeafCtorExprLeafCtorExpr LeafCtorExpr_Bool LeafCtorExpr_Bool)))]) 
      (fun param_variantis => (let '(MkLeafCtorExprLeafCtorExpr ctor1 ctor2) := param_variantis in

        (bindGen (genLeafExpr ctor1 stack2 4) 
        (fun p1 => 
          (bindGen (genLeafExpr ctor2 stack2 10) 
          (fun p2 => 
            (returnGen (App p1 p2)))))))))
    end
  | S size1 => match chosen_ctor with
    | CtorExpr_Var => 
      (bindGen 
      (* GenNat3 *)
      (let _weight_1 := match (size, stack1, stack2) with
      | (1, 11, 11) => 12
      | (1, 11, 12) => 56
      | (1, 11, 6) => 51
      | (1, 12, 11) => 50
      | (1, 12, 12) => 50
      | (1, 12, 6) => 50
      | (1, 6, 11) => 52
      | (1, 6, 12) => 50
      | (1, 6, 6) => 49
      | (2, 11, 11) => 61
      | (2, 11, 12) => 40
      | (2, 11, 6) => 36
      | (2, 12, 11) => 49
      | (2, 12, 12) => 50
      | (2, 12, 6) => 50
      | (2, 6, 11) => 40
      | (2, 6, 12) => 50
      | (2, 6, 6) => 50
      | (3, 0, 11) => 10
      | (3, 0, 12) => 50
      | (3, 0, 6) => 50
      | (4, 0, 0) => 50
      | _ => 500
      end
      in
      bindGen (freq [
        (_weight_1, returnGen 1);
        (100-_weight_1, returnGen 0)
      ]) (fun n1 =>
      (let _weight_2 := match (size, stack1, stack2) with
      | (1, 11, 11) => 12
      | (1, 11, 12) => 29
      | (1, 11, 6) => 28
      | (1, 12, 11) => 50
      | (1, 12, 12) => 50
      | (1, 12, 6) => 50
      | (1, 6, 11) => 28
      | (1, 6, 12) => 50
      | (1, 6, 6) => 49
      | (2, 11, 11) => 10
      | (2, 11, 12) => 40
      | (2, 11, 6) => 36
      | (2, 12, 11) => 49
      | (2, 12, 12) => 50
      | (2, 12, 6) => 50
      | (2, 6, 11) => 40
      | (2, 6, 12) => 50
      | (2, 6, 6) => 50
      | (3, 0, 11) => 10
      | (3, 0, 12) => 50
      | (3, 0, 6) => 50
      | (4, 0, 0) => 50
      | _ => 500
      end
      in
      bindGen (freq [
        (_weight_2, returnGen 2);
        (100-_weight_2, returnGen 0)
      ]) (fun n2 =>
      (let _weight_4 := match (size, stack1, stack2) with
      | (1, 11, 11) => 10
      | (1, 11, 12) => 29
      | (1, 11, 6) => 28
      | (1, 12, 11) => 50
      | (1, 12, 12) => 50
      | (1, 12, 6) => 50
      | (1, 6, 11) => 28
      | (1, 6, 12) => 50
      | (1, 6, 6) => 49
      | (2, 11, 11) => 10
      | (2, 11, 12) => 40
      | (2, 11, 6) => 36
      | (2, 12, 11) => 49
      | (2, 12, 12) => 50
      | (2, 12, 6) => 50
      | (2, 6, 11) => 40
      | (2, 6, 12) => 50
      | (2, 6, 6) => 50
      | (3, 0, 11) => 10
      | (3, 0, 12) => 50
      | (3, 0, 6) => 50
      | (4, 0, 0) => 50
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
        (returnGen (Var p1))))
    | CtorExpr_Bool => 
      (bindGen 
      (* GenBool3 *) (let _weight_true := match (size, stack1, stack2) with
      | (1, 11, 11) => 42
      | (1, 11, 12) => 43
      | (1, 11, 6) => 50
      | (1, 12, 11) => 49
      | (1, 12, 12) => 51
      | (1, 12, 6) => 50
      | (1, 6, 11) => 46
      | (1, 6, 12) => 50
      | (1, 6, 6) => 50
      | (2, 11, 11) => 48
      | (2, 11, 12) => 54
      | (2, 11, 6) => 50
      | (2, 12, 11) => 47
      | (2, 12, 12) => 51
      | (2, 12, 6) => 50
      | (2, 6, 11) => 53
      | (2, 6, 12) => 50
      | (2, 6, 6) => 50
      | (3, 0, 11) => 55
      | (3, 0, 12) => 52
      | (3, 0, 6) => 50
      | (4, 0, 0) => 48
      | _ => 500
      end
      in
      freq [
        (_weight_true, returnGen true);
        (100-_weight_true, returnGen false)
      ]) 
      (fun p1 => 
        (returnGen (Bool p1))))
    | CtorExpr_Abs => 
      (bindGen 
      (* Frequency6 *) (freq [
        (* 1 *) (match (size, stack1, stack2) with
        | (1, 11, 11) => 15
        | (1, 11, 12) => 50
        | (1, 11, 6) => 48
        | (1, 12, 11) => 50
        | (1, 12, 12) => 50
        | (1, 12, 6) => 50
        | (1, 6, 11) => 48
        | (1, 6, 12) => 50
        | (1, 6, 6) => 50
        | (2, 11, 11) => 11
        | (2, 11, 12) => 49
        | (2, 11, 6) => 50
        | (2, 12, 11) => 51
        | (2, 12, 12) => 50
        | (2, 12, 6) => 50
        | (2, 6, 11) => 46
        | (2, 6, 12) => 50
        | (2, 6, 6) => 50
        | (3, 0, 11) => 10
        | (3, 0, 12) => 50
        | (3, 0, 6) => 33
        | (4, 0, 0) => 10
        | _ => 500
        end,
        (returnGen (MkCtorTypCtorExpr CtorTyp_TBool CtorExpr_Var))); 
        (* 2 *) (match (size, stack1, stack2) with
        | (1, 11, 11) => 22
        | (1, 11, 12) => 49
        | (1, 11, 6) => 31
        | (1, 12, 11) => 50
        | (1, 12, 12) => 50
        | (1, 12, 6) => 50
        | (1, 6, 11) => 47
        | (1, 6, 12) => 50
        | (1, 6, 6) => 50
        | (2, 11, 11) => 10
        | (2, 11, 12) => 49
        | (2, 11, 6) => 27
        | (2, 12, 11) => 50
        | (2, 12, 12) => 50
        | (2, 12, 6) => 50
        | (2, 6, 11) => 53
        | (2, 6, 12) => 50
        | (2, 6, 6) => 50
        | (3, 0, 11) => 10
        | (3, 0, 12) => 49
        | (3, 0, 6) => 26
        | (4, 0, 0) => 10
        | _ => 500
        end,
        (returnGen (MkCtorTypCtorExpr CtorTyp_TFun CtorExpr_Var))); 
        (* 3 *) (match (size, stack1, stack2) with
        | (1, 11, 11) => 16
        | (1, 11, 12) => 56
        | (1, 11, 6) => 73
        | (1, 12, 11) => 52
        | (1, 12, 12) => 50
        | (1, 12, 6) => 52
        | (1, 6, 11) => 53
        | (1, 6, 12) => 50
        | (1, 6, 6) => 50
        | (2, 11, 11) => 14
        | (2, 11, 12) => 53
        | (2, 11, 6) => 75
        | (2, 12, 11) => 50
        | (2, 12, 12) => 50
        | (2, 12, 6) => 50
        | (2, 6, 11) => 51
        | (2, 6, 12) => 50
        | (2, 6, 6) => 50
        | (3, 0, 11) => 10
        | (3, 0, 12) => 54
        | (3, 0, 6) => 80
        | (4, 0, 0) => 10
        | _ => 500
        end,
        (returnGen (MkCtorTypCtorExpr CtorTyp_TBool CtorExpr_Bool))); 
        (* 4 *) (match (size, stack1, stack2) with
        | (1, 11, 11) => 45
        | (1, 11, 12) => 48
        | (1, 11, 6) => 32
        | (1, 12, 11) => 50
        | (1, 12, 12) => 50
        | (1, 12, 6) => 50
        | (1, 6, 11) => 57
        | (1, 6, 12) => 50
        | (1, 6, 6) => 50
        | (2, 11, 11) => 23
        | (2, 11, 12) => 51
        | (2, 11, 6) => 28
        | (2, 12, 11) => 50
        | (2, 12, 12) => 50
        | (2, 12, 6) => 50
        | (2, 6, 11) => 52
        | (2, 6, 12) => 50
        | (2, 6, 6) => 50
        | (3, 0, 11) => 10
        | (3, 0, 12) => 49
        | (3, 0, 6) => 26
        | (4, 0, 0) => 10
        | _ => 500
        end,
        (returnGen (MkCtorTypCtorExpr CtorTyp_TFun CtorExpr_Bool))); 
        (* 5 *) (match (size, stack1, stack2) with
        | (1, 11, 11) => 90
        | (1, 11, 12) => 49
        | (1, 11, 6) => 81
        | (1, 12, 11) => 50
        | (1, 12, 12) => 50
        | (1, 12, 6) => 50
        | (1, 6, 11) => 52
        | (1, 6, 12) => 50
        | (1, 6, 6) => 50
        | (2, 11, 11) => 89
        | (2, 11, 12) => 51
        | (2, 11, 6) => 80
        | (2, 12, 11) => 50
        | (2, 12, 12) => 50
        | (2, 12, 6) => 50
        | (2, 6, 11) => 58
        | (2, 6, 12) => 50
        | (2, 6, 6) => 50
        | (3, 0, 11) => 90
        | (3, 0, 12) => 50
        | (3, 0, 6) => 82
        | (4, 0, 0) => 90
        | _ => 500
        end,
        (returnGen (MkCtorTypCtorExpr CtorTyp_TBool CtorExpr_Abs))); 
        (* 6 *) (match (size, stack1, stack2) with
        | (1, 11, 11) => 90
        | (1, 11, 12) => 48
        | (1, 11, 6) => 30
        | (1, 12, 11) => 50
        | (1, 12, 12) => 50
        | (1, 12, 6) => 50
        | (1, 6, 11) => 61
        | (1, 6, 12) => 50
        | (1, 6, 6) => 50
        | (2, 11, 11) => 90
        | (2, 11, 12) => 49
        | (2, 11, 6) => 30
        | (2, 12, 11) => 50
        | (2, 12, 12) => 50
        | (2, 12, 6) => 50
        | (2, 6, 11) => 59
        | (2, 6, 12) => 50
        | (2, 6, 6) => 50
        | (3, 0, 11) => 90
        | (3, 0, 12) => 49
        | (3, 0, 6) => 28
        | (4, 0, 0) => 90
        | _ => 500
        end,
        (returnGen (MkCtorTypCtorExpr CtorTyp_TFun CtorExpr_Abs))); 
        (* 7 *) (match (size, stack1, stack2) with
        | (1, 11, 11) => 10
        | (1, 11, 12) => 49
        | (1, 11, 6) => 28
        | (1, 12, 11) => 50
        | (1, 12, 12) => 50
        | (1, 12, 6) => 50
        | (1, 6, 11) => 38
        | (1, 6, 12) => 50
        | (1, 6, 6) => 50
        | (2, 11, 11) => 10
        | (2, 11, 12) => 49
        | (2, 11, 6) => 31
        | (2, 12, 11) => 50
        | (2, 12, 12) => 50
        | (2, 12, 6) => 50
        | (2, 6, 11) => 38
        | (2, 6, 12) => 50
        | (2, 6, 6) => 50
        | (3, 0, 11) => 10
        | (3, 0, 12) => 49
        | (3, 0, 6) => 28
        | (4, 0, 0) => 10
        | _ => 500
        end,
        (returnGen (MkCtorTypCtorExpr CtorTyp_TBool CtorExpr_App))); 
        (* 8 *) (match (size, stack1, stack2) with
        | (1, 11, 11) => 10
        | (1, 11, 12) => 49
        | (1, 11, 6) => 27
        | (1, 12, 11) => 50
        | (1, 12, 12) => 50
        | (1, 12, 6) => 50
        | (1, 6, 11) => 40
        | (1, 6, 12) => 50
        | (1, 6, 6) => 50
        | (2, 11, 11) => 10
        | (2, 11, 12) => 49
        | (2, 11, 6) => 27
        | (2, 12, 11) => 50
        | (2, 12, 12) => 50
        | (2, 12, 6) => 50
        | (2, 6, 11) => 40
        | (2, 6, 12) => 50
        | (2, 6, 6) => 50
        | (3, 0, 11) => 10
        | (3, 0, 12) => 49
        | (3, 0, 6) => 26
        | (4, 0, 0) => 10
        | _ => 500
        end,
        (returnGen (MkCtorTypCtorExpr CtorTyp_TFun CtorExpr_App)))]) 
      (fun param_variantis => (let '(MkCtorTypCtorExpr ctor1 ctor2) := param_variantis in

        (bindGen (genTyp 1 ctor1 stack2 5) 
        (fun p1 => 
          (bindGen (genExpr size1 ctor2 stack2 11) 
          (fun p2 => 
            (returnGen (Abs p1 p2)))))))))
    | CtorExpr_App => 
      (bindGen 
      (* Frequency7 *) (freq [
        (* 1 *) (match (size, stack1, stack2) with
        | (1, 11, 11) => 40
        | (1, 11, 12) => 50
        | (1, 11, 6) => 50
        | (1, 12, 11) => 50
        | (1, 12, 12) => 50
        | (1, 12, 6) => 50
        | (1, 6, 11) => 50
        | (1, 6, 12) => 50
        | (1, 6, 6) => 50
        | (2, 11, 11) => 37
        | (2, 11, 12) => 50
        | (2, 11, 6) => 50
        | (2, 12, 11) => 50
        | (2, 12, 12) => 50
        | (2, 12, 6) => 50
        | (2, 6, 11) => 50
        | (2, 6, 12) => 50
        | (2, 6, 6) => 50
        | (3, 0, 11) => 35
        | (3, 0, 12) => 50
        | (3, 0, 6) => 50
        | (4, 0, 0) => 36
        | _ => 500
        end,
        (returnGen (MkCtorExprCtorExpr CtorExpr_Var CtorExpr_Var))); 
        (* 2 *) (match (size, stack1, stack2) with
        | (1, 11, 11) => 34
        | (1, 11, 12) => 50
        | (1, 11, 6) => 50
        | (1, 12, 11) => 50
        | (1, 12, 12) => 50
        | (1, 12, 6) => 50
        | (1, 6, 11) => 50
        | (1, 6, 12) => 50
        | (1, 6, 6) => 50
        | (2, 11, 11) => 35
        | (2, 11, 12) => 50
        | (2, 11, 6) => 50
        | (2, 12, 11) => 50
        | (2, 12, 12) => 50
        | (2, 12, 6) => 50
        | (2, 6, 11) => 50
        | (2, 6, 12) => 50
        | (2, 6, 6) => 50
        | (3, 0, 11) => 35
        | (3, 0, 12) => 50
        | (3, 0, 6) => 50
        | (4, 0, 0) => 36
        | _ => 500
        end,
        (returnGen (MkCtorExprCtorExpr CtorExpr_Bool CtorExpr_Var))); 
        (* 3 *) (match (size, stack1, stack2) with
        | (1, 11, 11) => 63
        | (1, 11, 12) => 50
        | (1, 11, 6) => 50
        | (1, 12, 11) => 50
        | (1, 12, 12) => 50
        | (1, 12, 6) => 50
        | (1, 6, 11) => 51
        | (1, 6, 12) => 50
        | (1, 6, 6) => 50
        | (2, 11, 11) => 58
        | (2, 11, 12) => 50
        | (2, 11, 6) => 50
        | (2, 12, 11) => 50
        | (2, 12, 12) => 50
        | (2, 12, 6) => 50
        | (2, 6, 11) => 51
        | (2, 6, 12) => 50
        | (2, 6, 6) => 50
        | (3, 0, 11) => 45
        | (3, 0, 12) => 50
        | (3, 0, 6) => 50
        | (4, 0, 0) => 36
        | _ => 500
        end,
        (returnGen (MkCtorExprCtorExpr CtorExpr_Abs CtorExpr_Var))); 
        (* 4 *) (match (size, stack1, stack2) with
        | (1, 11, 11) => 34
        | (1, 11, 12) => 50
        | (1, 11, 6) => 50
        | (1, 12, 11) => 50
        | (1, 12, 12) => 50
        | (1, 12, 6) => 50
        | (1, 6, 11) => 50
        | (1, 6, 12) => 50
        | (1, 6, 6) => 50
        | (2, 11, 11) => 35
        | (2, 11, 12) => 50
        | (2, 11, 6) => 50
        | (2, 12, 11) => 50
        | (2, 12, 12) => 50
        | (2, 12, 6) => 50
        | (2, 6, 11) => 50
        | (2, 6, 12) => 50
        | (2, 6, 6) => 50
        | (3, 0, 11) => 35
        | (3, 0, 12) => 50
        | (3, 0, 6) => 50
        | (4, 0, 0) => 36
        | _ => 500
        end,
        (returnGen (MkCtorExprCtorExpr CtorExpr_App CtorExpr_Var))); 
        (* 5 *) (match (size, stack1, stack2) with
        | (1, 11, 11) => 59
        | (1, 11, 12) => 50
        | (1, 11, 6) => 50
        | (1, 12, 11) => 50
        | (1, 12, 12) => 50
        | (1, 12, 6) => 50
        | (1, 6, 11) => 50
        | (1, 6, 12) => 50
        | (1, 6, 6) => 50
        | (2, 11, 11) => 57
        | (2, 11, 12) => 50
        | (2, 11, 6) => 51
        | (2, 12, 11) => 50
        | (2, 12, 12) => 50
        | (2, 12, 6) => 50
        | (2, 6, 11) => 50
        | (2, 6, 12) => 50
        | (2, 6, 6) => 50
        | (3, 0, 11) => 51
        | (3, 0, 12) => 50
        | (3, 0, 6) => 50
        | (4, 0, 0) => 36
        | _ => 500
        end,
        (returnGen (MkCtorExprCtorExpr CtorExpr_Var CtorExpr_Bool))); 
        (* 6 *) (match (size, stack1, stack2) with
        | (1, 11, 11) => 34
        | (1, 11, 12) => 50
        | (1, 11, 6) => 50
        | (1, 12, 11) => 50
        | (1, 12, 12) => 50
        | (1, 12, 6) => 50
        | (1, 6, 11) => 50
        | (1, 6, 12) => 50
        | (1, 6, 6) => 50
        | (2, 11, 11) => 35
        | (2, 11, 12) => 50
        | (2, 11, 6) => 50
        | (2, 12, 11) => 50
        | (2, 12, 12) => 50
        | (2, 12, 6) => 50
        | (2, 6, 11) => 50
        | (2, 6, 12) => 50
        | (2, 6, 6) => 50
        | (3, 0, 11) => 35
        | (3, 0, 12) => 50
        | (3, 0, 6) => 50
        | (4, 0, 0) => 36
        | _ => 500
        end,
        (returnGen (MkCtorExprCtorExpr CtorExpr_Bool CtorExpr_Bool))); 
        (* 7 *) (match (size, stack1, stack2) with
        | (1, 11, 11) => 90
        | (1, 11, 12) => 56
        | (1, 11, 6) => 50
        | (1, 12, 11) => 50
        | (1, 12, 12) => 50
        | (1, 12, 6) => 50
        | (1, 6, 11) => 52
        | (1, 6, 12) => 50
        | (1, 6, 6) => 50
        | (2, 11, 11) => 90
        | (2, 11, 12) => 52
        | (2, 11, 6) => 50
        | (2, 12, 11) => 50
        | (2, 12, 12) => 50
        | (2, 12, 6) => 50
        | (2, 6, 11) => 53
        | (2, 6, 12) => 50
        | (2, 6, 6) => 50
        | (3, 0, 11) => 90
        | (3, 0, 12) => 50
        | (3, 0, 6) => 50
        | (4, 0, 0) => 90
        | _ => 500
        end,
        (returnGen (MkCtorExprCtorExpr CtorExpr_Abs CtorExpr_Bool))); 
        (* 8 *) (match (size, stack1, stack2) with
        | (1, 11, 11) => 36
        | (1, 11, 12) => 50
        | (1, 11, 6) => 50
        | (1, 12, 11) => 50
        | (1, 12, 12) => 50
        | (1, 12, 6) => 50
        | (1, 6, 11) => 50
        | (1, 6, 12) => 50
        | (1, 6, 6) => 50
        | (2, 11, 11) => 37
        | (2, 11, 12) => 50
        | (2, 11, 6) => 50
        | (2, 12, 11) => 50
        | (2, 12, 12) => 50
        | (2, 12, 6) => 50
        | (2, 6, 11) => 50
        | (2, 6, 12) => 50
        | (2, 6, 6) => 50
        | (3, 0, 11) => 36
        | (3, 0, 12) => 50
        | (3, 0, 6) => 50
        | (4, 0, 0) => 36
        | _ => 500
        end,
        (returnGen (MkCtorExprCtorExpr CtorExpr_App CtorExpr_Bool))); 
        (* 9 *) (match (size, stack1, stack2) with
        | (1, 11, 11) => 45
        | (1, 11, 12) => 50
        | (1, 11, 6) => 50
        | (1, 12, 11) => 50
        | (1, 12, 12) => 50
        | (1, 12, 6) => 50
        | (1, 6, 11) => 50
        | (1, 6, 12) => 50
        | (1, 6, 6) => 50
        | (2, 11, 11) => 39
        | (2, 11, 12) => 50
        | (2, 11, 6) => 50
        | (2, 12, 11) => 50
        | (2, 12, 12) => 50
        | (2, 12, 6) => 50
        | (2, 6, 11) => 50
        | (2, 6, 12) => 50
        | (2, 6, 6) => 50
        | (3, 0, 11) => 36
        | (3, 0, 12) => 50
        | (3, 0, 6) => 50
        | (4, 0, 0) => 36
        | _ => 500
        end,
        (returnGen (MkCtorExprCtorExpr CtorExpr_Var CtorExpr_Abs))); 
        (* 10 *) (match (size, stack1, stack2) with
        | (1, 11, 11) => 34
        | (1, 11, 12) => 50
        | (1, 11, 6) => 50
        | (1, 12, 11) => 50
        | (1, 12, 12) => 50
        | (1, 12, 6) => 50
        | (1, 6, 11) => 50
        | (1, 6, 12) => 50
        | (1, 6, 6) => 50
        | (2, 11, 11) => 35
        | (2, 11, 12) => 50
        | (2, 11, 6) => 50
        | (2, 12, 11) => 50
        | (2, 12, 12) => 50
        | (2, 12, 6) => 50
        | (2, 6, 11) => 50
        | (2, 6, 12) => 50
        | (2, 6, 6) => 50
        | (3, 0, 11) => 35
        | (3, 0, 12) => 50
        | (3, 0, 6) => 50
        | (4, 0, 0) => 36
        | _ => 500
        end,
        (returnGen (MkCtorExprCtorExpr CtorExpr_Bool CtorExpr_Abs))); 
        (* 11 *) (match (size, stack1, stack2) with
        | (1, 11, 11) => 44
        | (1, 11, 12) => 50
        | (1, 11, 6) => 50
        | (1, 12, 11) => 50
        | (1, 12, 12) => 50
        | (1, 12, 6) => 50
        | (1, 6, 11) => 50
        | (1, 6, 12) => 50
        | (1, 6, 6) => 50
        | (2, 11, 11) => 44
        | (2, 11, 12) => 50
        | (2, 11, 6) => 50
        | (2, 12, 11) => 50
        | (2, 12, 12) => 50
        | (2, 12, 6) => 50
        | (2, 6, 11) => 50
        | (2, 6, 12) => 50
        | (2, 6, 6) => 50
        | (3, 0, 11) => 42
        | (3, 0, 12) => 50
        | (3, 0, 6) => 50
        | (4, 0, 0) => 42
        | _ => 500
        end,
        (returnGen (MkCtorExprCtorExpr CtorExpr_Abs CtorExpr_Abs))); 
        (* 12 *) (match (size, stack1, stack2) with
        | (1, 11, 11) => 34
        | (1, 11, 12) => 50
        | (1, 11, 6) => 50
        | (1, 12, 11) => 50
        | (1, 12, 12) => 50
        | (1, 12, 6) => 50
        | (1, 6, 11) => 50
        | (1, 6, 12) => 50
        | (1, 6, 6) => 50
        | (2, 11, 11) => 35
        | (2, 11, 12) => 50
        | (2, 11, 6) => 50
        | (2, 12, 11) => 50
        | (2, 12, 12) => 50
        | (2, 12, 6) => 50
        | (2, 6, 11) => 50
        | (2, 6, 12) => 50
        | (2, 6, 6) => 50
        | (3, 0, 11) => 35
        | (3, 0, 12) => 50
        | (3, 0, 6) => 50
        | (4, 0, 0) => 36
        | _ => 500
        end,
        (returnGen (MkCtorExprCtorExpr CtorExpr_App CtorExpr_Abs))); 
        (* 13 *) (match (size, stack1, stack2) with
        | (1, 11, 11) => 34
        | (1, 11, 12) => 50
        | (1, 11, 6) => 50
        | (1, 12, 11) => 50
        | (1, 12, 12) => 50
        | (1, 12, 6) => 50
        | (1, 6, 11) => 50
        | (1, 6, 12) => 50
        | (1, 6, 6) => 50
        | (2, 11, 11) => 37
        | (2, 11, 12) => 50
        | (2, 11, 6) => 50
        | (2, 12, 11) => 50
        | (2, 12, 12) => 50
        | (2, 12, 6) => 50
        | (2, 6, 11) => 50
        | (2, 6, 12) => 50
        | (2, 6, 6) => 50
        | (3, 0, 11) => 36
        | (3, 0, 12) => 50
        | (3, 0, 6) => 50
        | (4, 0, 0) => 36
        | _ => 500
        end,
        (returnGen (MkCtorExprCtorExpr CtorExpr_Var CtorExpr_App))); 
        (* 14 *) (match (size, stack1, stack2) with
        | (1, 11, 11) => 34
        | (1, 11, 12) => 50
        | (1, 11, 6) => 50
        | (1, 12, 11) => 50
        | (1, 12, 12) => 50
        | (1, 12, 6) => 50
        | (1, 6, 11) => 50
        | (1, 6, 12) => 50
        | (1, 6, 6) => 50
        | (2, 11, 11) => 35
        | (2, 11, 12) => 50
        | (2, 11, 6) => 50
        | (2, 12, 11) => 50
        | (2, 12, 12) => 50
        | (2, 12, 6) => 50
        | (2, 6, 11) => 50
        | (2, 6, 12) => 50
        | (2, 6, 6) => 50
        | (3, 0, 11) => 35
        | (3, 0, 12) => 50
        | (3, 0, 6) => 50
        | (4, 0, 0) => 36
        | _ => 500
        end,
        (returnGen (MkCtorExprCtorExpr CtorExpr_Bool CtorExpr_App))); 
        (* 15 *) (match (size, stack1, stack2) with
        | (1, 11, 11) => 36
        | (1, 11, 12) => 50
        | (1, 11, 6) => 50
        | (1, 12, 11) => 50
        | (1, 12, 12) => 50
        | (1, 12, 6) => 50
        | (1, 6, 11) => 50
        | (1, 6, 12) => 50
        | (1, 6, 6) => 50
        | (2, 11, 11) => 41
        | (2, 11, 12) => 50
        | (2, 11, 6) => 50
        | (2, 12, 11) => 50
        | (2, 12, 12) => 50
        | (2, 12, 6) => 50
        | (2, 6, 11) => 50
        | (2, 6, 12) => 50
        | (2, 6, 6) => 50
        | (3, 0, 11) => 36
        | (3, 0, 12) => 50
        | (3, 0, 6) => 50
        | (4, 0, 0) => 36
        | _ => 500
        end,
        (returnGen (MkCtorExprCtorExpr CtorExpr_Abs CtorExpr_App))); 
        (* 16 *) (match (size, stack1, stack2) with
        | (1, 11, 11) => 34
        | (1, 11, 12) => 50
        | (1, 11, 6) => 50
        | (1, 12, 11) => 50
        | (1, 12, 12) => 50
        | (1, 12, 6) => 50
        | (1, 6, 11) => 50
        | (1, 6, 12) => 50
        | (1, 6, 6) => 50
        | (2, 11, 11) => 35
        | (2, 11, 12) => 50
        | (2, 11, 6) => 50
        | (2, 12, 11) => 50
        | (2, 12, 12) => 50
        | (2, 12, 6) => 50
        | (2, 6, 11) => 50
        | (2, 6, 12) => 50
        | (2, 6, 6) => 50
        | (3, 0, 11) => 35
        | (3, 0, 12) => 50
        | (3, 0, 6) => 50
        | (4, 0, 0) => 36
        | _ => 500
        end,
        (returnGen (MkCtorExprCtorExpr CtorExpr_App CtorExpr_App)))]) 
      (fun param_variantis => (let '(MkCtorExprCtorExpr ctor1 ctor2) := param_variantis in

        (bindGen (genExpr size1 ctor1 stack2 6) 
        (fun p1 => 
          (bindGen (genExpr size1 ctor2 stack2 12) 
          (fun p2 => 
            (returnGen (App p1 p2)))))))))
    end
  end.

Definition gSized :=

  (bindGen 
  (* Frequency1 *) (freq [
    (* 1 *) (match (tt) with
    | tt => 10
    end,
    (returnGen CtorExpr_Var)); 
    (* 2 *) (match (tt) with
    | tt => 10
    end,
    (returnGen CtorExpr_Bool)); 
    (* 3 *) (match (tt) with
    | tt => 90
    end,
    (returnGen CtorExpr_Abs)); 
    (* 4 *) (match (tt) with
    | tt => 10
    end,
    (returnGen CtorExpr_App))]) 
  (fun init_ctor => (genExpr 4 init_ctor 0 0))).

Definition test_prop_SinglePreserve :=
forAll gSized (fun (e: Expr) =>
  prop_SinglePreserve e).

(*! QuickChick test_prop_SinglePreserve. *)

Definition test_prop_MultiPreserve :=
forAll gSized (fun (e: Expr) =>
  prop_MultiPreserve e).

(*! QuickChick test_prop_MultiPreserve. *)
          
