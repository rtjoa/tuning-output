From QuickChick Require Import QuickChick. Import QcNotation.
From Coq Require Import Bool ZArith List. Import ListNotations.
From ExtLib Require Import Monad.
From ExtLib.Data.Monads Require Import OptionMonad.
Import MonadNotation.

From STLC Require Import Impl Spec.

Inductive LeafCtorTyp :=
  | LeafCtorTyp_TBool.

Inductive CtorTyp :=
  | CtorTyp_TBool
  | CtorTyp_TFun.

Inductive LeafCtorExpr :=
  | LeafCtorExpr_Var
  | LeafCtorExpr_Bool.

Inductive CtorExpr :=
  | CtorExpr_Var
  | CtorExpr_Bool
  | CtorExpr_Abs
  | CtorExpr_App.

Inductive TupCtorTypLeafCtorExpr :=
  | MkCtorTypLeafCtorExpr : CtorTyp -> LeafCtorExpr -> TupCtorTypLeafCtorExpr.

Inductive TupCtorTypCtorExpr :=
  | MkCtorTypCtorExpr : CtorTyp -> CtorExpr -> TupCtorTypCtorExpr.

Inductive TupCtorTypCtorTyp :=
  | MkCtorTypCtorTyp : CtorTyp -> CtorTyp -> TupCtorTypCtorTyp.

Inductive TupLeafCtorExprLeafCtorExpr :=
  | MkLeafCtorExprLeafCtorExpr : LeafCtorExpr -> LeafCtorExpr -> TupLeafCtorExprLeafCtorExpr.

Inductive TupLeafCtorTypLeafCtorTyp :=
  | MkLeafCtorTypLeafCtorTyp : LeafCtorTyp -> LeafCtorTyp -> TupLeafCtorTypLeafCtorTyp.

Inductive TupCtorExprCtorExpr :=
  | MkCtorExprCtorExpr : CtorExpr -> CtorExpr -> TupCtorExprCtorExpr.

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
        | (1, 0, 5) => 50
        | (1, 11, 3) => 50
        | (1, 11, 5) => 50
        | (1, 12, 3) => 50
        | (1, 12, 5) => 50
        | (1, 6, 3) => 50
        | (1, 6, 5) => 50
        | _ => 500
        end,
        (returnGen (MkCtorTypCtorTyp CtorTyp_TBool CtorTyp_TBool))); 
        (* 2 *) (match (size, stack1, stack2) with
        | (1, 0, 5) => 50
        | (1, 11, 3) => 50
        | (1, 11, 5) => 50
        | (1, 12, 3) => 50
        | (1, 12, 5) => 50
        | (1, 6, 3) => 50
        | (1, 6, 5) => 50
        | _ => 500
        end,
        (returnGen (MkCtorTypCtorTyp CtorTyp_TFun CtorTyp_TBool))); 
        (* 3 *) (match (size, stack1, stack2) with
        | (1, 0, 5) => 50
        | (1, 11, 3) => 50
        | (1, 11, 5) => 50
        | (1, 12, 3) => 50
        | (1, 12, 5) => 50
        | (1, 6, 3) => 50
        | (1, 6, 5) => 50
        | _ => 500
        end,
        (returnGen (MkCtorTypCtorTyp CtorTyp_TBool CtorTyp_TFun))); 
        (* 4 *) (match (size, stack1, stack2) with
        | (1, 0, 5) => 50
        | (1, 11, 3) => 50
        | (1, 11, 5) => 50
        | (1, 12, 3) => 50
        | (1, 12, 5) => 50
        | (1, 6, 3) => 50
        | (1, 6, 5) => 50
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
    | (11, 10) => 50
    | (11, 4) => 50
    | (11, 9) => 50
    | (12, 10) => 50
    | (12, 4) => 50
    | (12, 9) => 50
    | (6, 10) => 50
    | (6, 4) => 50
    | (6, 9) => 50
    | _ => 500
    end
    in
    bindGen (freq [
      (_weight_1, returnGen 1);
      (100-_weight_1, returnGen 0)
    ]) (fun n1 =>
    (let _weight_2 := match (stack1, stack2) with
    | (11, 10) => 50
    | (11, 4) => 50
    | (11, 9) => 50
    | (12, 10) => 50
    | (12, 4) => 50
    | (12, 9) => 50
    | (6, 10) => 50
    | (6, 4) => 50
    | (6, 9) => 50
    | _ => 500
    end
    in
    bindGen (freq [
      (_weight_2, returnGen 2);
      (100-_weight_2, returnGen 0)
    ]) (fun n2 =>
    (let _weight_4 := match (stack1, stack2) with
    | (11, 10) => 50
    | (11, 4) => 50
    | (11, 9) => 50
    | (12, 10) => 50
    | (12, 4) => 50
    | (12, 9) => 50
    | (6, 10) => 50
    | (6, 4) => 50
    | (6, 9) => 50
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
    | (11, 10) => 50
    | (11, 4) => 50
    | (11, 9) => 50
    | (12, 10) => 50
    | (12, 4) => 50
    | (12, 9) => 50
    | (6, 10) => 50
    | (6, 4) => 50
    | (6, 9) => 50
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
      | (11, 11) => 50
      | (11, 12) => 50
      | (11, 6) => 50
      | (12, 11) => 50
      | (12, 12) => 50
      | (12, 6) => 50
      | (6, 11) => 50
      | (6, 12) => 50
      | (6, 6) => 50
      | _ => 500
      end
      in
      bindGen (freq [
        (_weight_1, returnGen 1);
        (100-_weight_1, returnGen 0)
      ]) (fun n1 =>
      (let _weight_2 := match (stack1, stack2) with
      | (11, 11) => 50
      | (11, 12) => 50
      | (11, 6) => 50
      | (12, 11) => 50
      | (12, 12) => 50
      | (12, 6) => 50
      | (6, 11) => 50
      | (6, 12) => 50
      | (6, 6) => 50
      | _ => 500
      end
      in
      bindGen (freq [
        (_weight_2, returnGen 2);
        (100-_weight_2, returnGen 0)
      ]) (fun n2 =>
      (let _weight_4 := match (stack1, stack2) with
      | (11, 11) => 50
      | (11, 12) => 50
      | (11, 6) => 50
      | (12, 11) => 50
      | (12, 12) => 50
      | (12, 6) => 50
      | (6, 11) => 50
      | (6, 12) => 50
      | (6, 6) => 50
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
      | (11, 11) => 50
      | (11, 12) => 50
      | (11, 6) => 50
      | (12, 11) => 50
      | (12, 12) => 50
      | (12, 6) => 50
      | (6, 11) => 50
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
        | (11, 11) => 50
        | (11, 12) => 50
        | (11, 6) => 50
        | (12, 11) => 50
        | (12, 12) => 50
        | (12, 6) => 50
        | (6, 11) => 50
        | (6, 12) => 50
        | (6, 6) => 50
        | _ => 500
        end,
        (returnGen (MkCtorTypLeafCtorExpr CtorTyp_TBool LeafCtorExpr_Var))); 
        (* 2 *) (match (stack1, stack2) with
        | (11, 11) => 50
        | (11, 12) => 50
        | (11, 6) => 50
        | (12, 11) => 50
        | (12, 12) => 50
        | (12, 6) => 50
        | (6, 11) => 50
        | (6, 12) => 50
        | (6, 6) => 50
        | _ => 500
        end,
        (returnGen (MkCtorTypLeafCtorExpr CtorTyp_TFun LeafCtorExpr_Var))); 
        (* 3 *) (match (stack1, stack2) with
        | (11, 11) => 50
        | (11, 12) => 50
        | (11, 6) => 50
        | (12, 11) => 50
        | (12, 12) => 50
        | (12, 6) => 50
        | (6, 11) => 50
        | (6, 12) => 50
        | (6, 6) => 50
        | _ => 500
        end,
        (returnGen (MkCtorTypLeafCtorExpr CtorTyp_TBool LeafCtorExpr_Bool))); 
        (* 4 *) (match (stack1, stack2) with
        | (11, 11) => 50
        | (11, 12) => 50
        | (11, 6) => 50
        | (12, 11) => 50
        | (12, 12) => 50
        | (12, 6) => 50
        | (6, 11) => 50
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
        | (11, 11) => 50
        | (11, 12) => 50
        | (11, 6) => 50
        | (12, 11) => 50
        | (12, 12) => 50
        | (12, 6) => 50
        | (6, 11) => 50
        | (6, 12) => 50
        | (6, 6) => 50
        | _ => 500
        end,
        (returnGen (MkLeafCtorExprLeafCtorExpr LeafCtorExpr_Var LeafCtorExpr_Var))); 
        (* 2 *) (match (stack1, stack2) with
        | (11, 11) => 50
        | (11, 12) => 50
        | (11, 6) => 50
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
        | (11, 11) => 50
        | (11, 12) => 50
        | (11, 6) => 50
        | (12, 11) => 50
        | (12, 12) => 50
        | (12, 6) => 50
        | (6, 11) => 50
        | (6, 12) => 50
        | (6, 6) => 50
        | _ => 500
        end,
        (returnGen (MkLeafCtorExprLeafCtorExpr LeafCtorExpr_Var LeafCtorExpr_Bool))); 
        (* 4 *) (match (stack1, stack2) with
        | (11, 11) => 50
        | (11, 12) => 50
        | (11, 6) => 50
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
      | (1, 11, 11) => 50
      | (1, 11, 12) => 50
      | (1, 11, 6) => 50
      | (1, 12, 11) => 50
      | (1, 12, 12) => 50
      | (1, 12, 6) => 50
      | (1, 6, 11) => 50
      | (1, 6, 12) => 50
      | (1, 6, 6) => 50
      | (2, 11, 11) => 50
      | (2, 11, 12) => 50
      | (2, 11, 6) => 50
      | (2, 12, 11) => 50
      | (2, 12, 12) => 50
      | (2, 12, 6) => 50
      | (2, 6, 11) => 50
      | (2, 6, 12) => 50
      | (2, 6, 6) => 50
      | (3, 0, 11) => 50
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
      | (1, 11, 11) => 50
      | (1, 11, 12) => 50
      | (1, 11, 6) => 50
      | (1, 12, 11) => 50
      | (1, 12, 12) => 50
      | (1, 12, 6) => 50
      | (1, 6, 11) => 50
      | (1, 6, 12) => 50
      | (1, 6, 6) => 50
      | (2, 11, 11) => 50
      | (2, 11, 12) => 50
      | (2, 11, 6) => 50
      | (2, 12, 11) => 50
      | (2, 12, 12) => 50
      | (2, 12, 6) => 50
      | (2, 6, 11) => 50
      | (2, 6, 12) => 50
      | (2, 6, 6) => 50
      | (3, 0, 11) => 50
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
      | (1, 11, 11) => 50
      | (1, 11, 12) => 50
      | (1, 11, 6) => 50
      | (1, 12, 11) => 50
      | (1, 12, 12) => 50
      | (1, 12, 6) => 50
      | (1, 6, 11) => 50
      | (1, 6, 12) => 50
      | (1, 6, 6) => 50
      | (2, 11, 11) => 50
      | (2, 11, 12) => 50
      | (2, 11, 6) => 50
      | (2, 12, 11) => 50
      | (2, 12, 12) => 50
      | (2, 12, 6) => 50
      | (2, 6, 11) => 50
      | (2, 6, 12) => 50
      | (2, 6, 6) => 50
      | (3, 0, 11) => 50
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
      | (1, 11, 11) => 50
      | (1, 11, 12) => 50
      | (1, 11, 6) => 50
      | (1, 12, 11) => 50
      | (1, 12, 12) => 50
      | (1, 12, 6) => 50
      | (1, 6, 11) => 50
      | (1, 6, 12) => 50
      | (1, 6, 6) => 50
      | (2, 11, 11) => 50
      | (2, 11, 12) => 50
      | (2, 11, 6) => 50
      | (2, 12, 11) => 50
      | (2, 12, 12) => 50
      | (2, 12, 6) => 50
      | (2, 6, 11) => 50
      | (2, 6, 12) => 50
      | (2, 6, 6) => 50
      | (3, 0, 11) => 50
      | (3, 0, 12) => 50
      | (3, 0, 6) => 50
      | (4, 0, 0) => 50
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
        | (1, 11, 11) => 48
        | (1, 11, 12) => 41
        | (1, 11, 6) => 41
        | (1, 12, 11) => 48
        | (1, 12, 12) => 38
        | (1, 12, 6) => 38
        | (1, 6, 11) => 48
        | (1, 6, 12) => 38
        | (1, 6, 6) => 38
        | (2, 11, 11) => 52
        | (2, 11, 12) => 50
        | (2, 11, 6) => 50
        | (2, 12, 11) => 42
        | (2, 12, 12) => 45
        | (2, 12, 6) => 45
        | (2, 6, 11) => 42
        | (2, 6, 12) => 45
        | (2, 6, 6) => 45
        | (3, 0, 11) => 48
        | (3, 0, 12) => 13
        | (3, 0, 6) => 13
        | (4, 0, 0) => 46
        | _ => 500
        end,
        (returnGen (MkCtorTypCtorExpr CtorTyp_TBool CtorExpr_Var))); 
        (* 2 *) (match (size, stack1, stack2) with
        | (1, 11, 11) => 48
        | (1, 11, 12) => 41
        | (1, 11, 6) => 41
        | (1, 12, 11) => 48
        | (1, 12, 12) => 38
        | (1, 12, 6) => 38
        | (1, 6, 11) => 48
        | (1, 6, 12) => 38
        | (1, 6, 6) => 38
        | (2, 11, 11) => 52
        | (2, 11, 12) => 50
        | (2, 11, 6) => 50
        | (2, 12, 11) => 42
        | (2, 12, 12) => 45
        | (2, 12, 6) => 45
        | (2, 6, 11) => 42
        | (2, 6, 12) => 45
        | (2, 6, 6) => 45
        | (3, 0, 11) => 48
        | (3, 0, 12) => 13
        | (3, 0, 6) => 13
        | (4, 0, 0) => 46
        | _ => 500
        end,
        (returnGen (MkCtorTypCtorExpr CtorTyp_TFun CtorExpr_Var))); 
        (* 3 *) (match (size, stack1, stack2) with
        | (1, 11, 11) => 48
        | (1, 11, 12) => 41
        | (1, 11, 6) => 41
        | (1, 12, 11) => 48
        | (1, 12, 12) => 38
        | (1, 12, 6) => 38
        | (1, 6, 11) => 48
        | (1, 6, 12) => 38
        | (1, 6, 6) => 38
        | (2, 11, 11) => 52
        | (2, 11, 12) => 50
        | (2, 11, 6) => 50
        | (2, 12, 11) => 42
        | (2, 12, 12) => 45
        | (2, 12, 6) => 45
        | (2, 6, 11) => 42
        | (2, 6, 12) => 45
        | (2, 6, 6) => 45
        | (3, 0, 11) => 48
        | (3, 0, 12) => 13
        | (3, 0, 6) => 13
        | (4, 0, 0) => 46
        | _ => 500
        end,
        (returnGen (MkCtorTypCtorExpr CtorTyp_TBool CtorExpr_Bool))); 
        (* 4 *) (match (size, stack1, stack2) with
        | (1, 11, 11) => 48
        | (1, 11, 12) => 41
        | (1, 11, 6) => 41
        | (1, 12, 11) => 48
        | (1, 12, 12) => 38
        | (1, 12, 6) => 38
        | (1, 6, 11) => 48
        | (1, 6, 12) => 38
        | (1, 6, 6) => 38
        | (2, 11, 11) => 52
        | (2, 11, 12) => 50
        | (2, 11, 6) => 50
        | (2, 12, 11) => 42
        | (2, 12, 12) => 45
        | (2, 12, 6) => 45
        | (2, 6, 11) => 42
        | (2, 6, 12) => 45
        | (2, 6, 6) => 45
        | (3, 0, 11) => 48
        | (3, 0, 12) => 13
        | (3, 0, 6) => 13
        | (4, 0, 0) => 46
        | _ => 500
        end,
        (returnGen (MkCtorTypCtorExpr CtorTyp_TFun CtorExpr_Bool))); 
        (* 5 *) (match (size, stack1, stack2) with
        | (1, 11, 11) => 51
        | (1, 11, 12) => 51
        | (1, 11, 6) => 51
        | (1, 12, 11) => 51
        | (1, 12, 12) => 49
        | (1, 12, 6) => 49
        | (1, 6, 11) => 51
        | (1, 6, 12) => 49
        | (1, 6, 6) => 49
        | (2, 11, 11) => 48
        | (2, 11, 12) => 50
        | (2, 11, 6) => 50
        | (2, 12, 11) => 50
        | (2, 12, 12) => 49
        | (2, 12, 6) => 49
        | (2, 6, 11) => 50
        | (2, 6, 12) => 49
        | (2, 6, 6) => 49
        | (3, 0, 11) => 55
        | (3, 0, 12) => 18
        | (3, 0, 6) => 18
        | (4, 0, 0) => 44
        | _ => 500
        end,
        (returnGen (MkCtorTypCtorExpr CtorTyp_TBool CtorExpr_Abs))); 
        (* 6 *) (match (size, stack1, stack2) with
        | (1, 11, 11) => 51
        | (1, 11, 12) => 51
        | (1, 11, 6) => 51
        | (1, 12, 11) => 51
        | (1, 12, 12) => 49
        | (1, 12, 6) => 49
        | (1, 6, 11) => 51
        | (1, 6, 12) => 49
        | (1, 6, 6) => 49
        | (2, 11, 11) => 48
        | (2, 11, 12) => 50
        | (2, 11, 6) => 50
        | (2, 12, 11) => 50
        | (2, 12, 12) => 49
        | (2, 12, 6) => 49
        | (2, 6, 11) => 50
        | (2, 6, 12) => 49
        | (2, 6, 6) => 49
        | (3, 0, 11) => 55
        | (3, 0, 12) => 18
        | (3, 0, 6) => 18
        | (4, 0, 0) => 44
        | _ => 500
        end,
        (returnGen (MkCtorTypCtorExpr CtorTyp_TFun CtorExpr_Abs))); 
        (* 7 *) (match (size, stack1, stack2) with
        | (1, 11, 11) => 54
        | (1, 11, 12) => 63
        | (1, 11, 6) => 63
        | (1, 12, 11) => 52
        | (1, 12, 12) => 68
        | (1, 12, 6) => 68
        | (1, 6, 11) => 52
        | (1, 6, 12) => 68
        | (1, 6, 6) => 68
        | (2, 11, 11) => 48
        | (2, 11, 12) => 50
        | (2, 11, 6) => 50
        | (2, 12, 11) => 63
        | (2, 12, 12) => 60
        | (2, 12, 6) => 60
        | (2, 6, 11) => 63
        | (2, 6, 12) => 60
        | (2, 6, 6) => 60
        | (3, 0, 11) => 48
        | (3, 0, 12) => 87
        | (3, 0, 6) => 87
        | (4, 0, 0) => 61
        | _ => 500
        end,
        (returnGen (MkCtorTypCtorExpr CtorTyp_TBool CtorExpr_App))); 
        (* 8 *) (match (size, stack1, stack2) with
        | (1, 11, 11) => 54
        | (1, 11, 12) => 63
        | (1, 11, 6) => 63
        | (1, 12, 11) => 52
        | (1, 12, 12) => 68
        | (1, 12, 6) => 68
        | (1, 6, 11) => 52
        | (1, 6, 12) => 68
        | (1, 6, 6) => 68
        | (2, 11, 11) => 48
        | (2, 11, 12) => 50
        | (2, 11, 6) => 50
        | (2, 12, 11) => 63
        | (2, 12, 12) => 60
        | (2, 12, 6) => 60
        | (2, 6, 11) => 63
        | (2, 6, 12) => 60
        | (2, 6, 6) => 60
        | (3, 0, 11) => 48
        | (3, 0, 12) => 87
        | (3, 0, 6) => 87
        | (4, 0, 0) => 61
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
        | (1, 11, 11) => 47
        | (1, 11, 12) => 38
        | (1, 11, 6) => 38
        | (1, 12, 11) => 47
        | (1, 12, 12) => 1
        | (1, 12, 6) => 1
        | (1, 6, 11) => 47
        | (1, 6, 12) => 1
        | (1, 6, 6) => 1
        | (2, 11, 11) => 50
        | (2, 11, 12) => 50
        | (2, 11, 6) => 50
        | (2, 12, 11) => 27
        | (2, 12, 12) => 2
        | (2, 12, 6) => 2
        | (2, 6, 11) => 27
        | (2, 6, 12) => 2
        | (2, 6, 6) => 2
        | (3, 0, 11) => 56
        | (3, 0, 12) => 1
        | (3, 0, 6) => 1
        | (4, 0, 0) => 1
        | _ => 500
        end,
        (returnGen (MkCtorExprCtorExpr CtorExpr_Var CtorExpr_Var))); 
        (* 2 *) (match (size, stack1, stack2) with
        | (1, 11, 11) => 47
        | (1, 11, 12) => 38
        | (1, 11, 6) => 38
        | (1, 12, 11) => 47
        | (1, 12, 12) => 1
        | (1, 12, 6) => 1
        | (1, 6, 11) => 47
        | (1, 6, 12) => 1
        | (1, 6, 6) => 1
        | (2, 11, 11) => 50
        | (2, 11, 12) => 50
        | (2, 11, 6) => 50
        | (2, 12, 11) => 27
        | (2, 12, 12) => 2
        | (2, 12, 6) => 2
        | (2, 6, 11) => 27
        | (2, 6, 12) => 2
        | (2, 6, 6) => 2
        | (3, 0, 11) => 56
        | (3, 0, 12) => 1
        | (3, 0, 6) => 1
        | (4, 0, 0) => 1
        | _ => 500
        end,
        (returnGen (MkCtorExprCtorExpr CtorExpr_Bool CtorExpr_Var))); 
        (* 3 *) (match (size, stack1, stack2) with
        | (1, 11, 11) => 48
        | (1, 11, 12) => 45
        | (1, 11, 6) => 45
        | (1, 12, 11) => 48
        | (1, 12, 12) => 1
        | (1, 12, 6) => 1
        | (1, 6, 11) => 48
        | (1, 6, 12) => 1
        | (1, 6, 6) => 1
        | (2, 11, 11) => 50
        | (2, 11, 12) => 49
        | (2, 11, 6) => 49
        | (2, 12, 11) => 34
        | (2, 12, 12) => 3
        | (2, 12, 6) => 3
        | (2, 6, 11) => 34
        | (2, 6, 12) => 3
        | (2, 6, 6) => 3
        | (3, 0, 11) => 46
        | (3, 0, 12) => 2
        | (3, 0, 6) => 2
        | (4, 0, 0) => 2
        | _ => 500
        end,
        (returnGen (MkCtorExprCtorExpr CtorExpr_Abs CtorExpr_Var))); 
        (* 4 *) (match (size, stack1, stack2) with
        | (1, 11, 11) => 51
        | (1, 11, 12) => 53
        | (1, 11, 6) => 53
        | (1, 12, 11) => 51
        | (1, 12, 12) => 1
        | (1, 12, 6) => 1
        | (1, 6, 11) => 51
        | (1, 6, 12) => 1
        | (1, 6, 6) => 1
        | (2, 11, 11) => 50
        | (2, 11, 12) => 50
        | (2, 11, 6) => 50
        | (2, 12, 11) => 51
        | (2, 12, 12) => 2
        | (2, 12, 6) => 2
        | (2, 6, 11) => 51
        | (2, 6, 12) => 2
        | (2, 6, 6) => 2
        | (3, 0, 11) => 48
        | (3, 0, 12) => 2
        | (3, 0, 6) => 2
        | (4, 0, 0) => 5
        | _ => 500
        end,
        (returnGen (MkCtorExprCtorExpr CtorExpr_App CtorExpr_Var))); 
        (* 5 *) (match (size, stack1, stack2) with
        | (1, 11, 11) => 47
        | (1, 11, 12) => 38
        | (1, 11, 6) => 38
        | (1, 12, 11) => 47
        | (1, 12, 12) => 1
        | (1, 12, 6) => 1
        | (1, 6, 11) => 47
        | (1, 6, 12) => 1
        | (1, 6, 6) => 1
        | (2, 11, 11) => 50
        | (2, 11, 12) => 50
        | (2, 11, 6) => 50
        | (2, 12, 11) => 27
        | (2, 12, 12) => 2
        | (2, 12, 6) => 2
        | (2, 6, 11) => 27
        | (2, 6, 12) => 2
        | (2, 6, 6) => 2
        | (3, 0, 11) => 56
        | (3, 0, 12) => 1
        | (3, 0, 6) => 1
        | (4, 0, 0) => 1
        | _ => 500
        end,
        (returnGen (MkCtorExprCtorExpr CtorExpr_Var CtorExpr_Bool))); 
        (* 6 *) (match (size, stack1, stack2) with
        | (1, 11, 11) => 47
        | (1, 11, 12) => 38
        | (1, 11, 6) => 38
        | (1, 12, 11) => 47
        | (1, 12, 12) => 1
        | (1, 12, 6) => 1
        | (1, 6, 11) => 47
        | (1, 6, 12) => 1
        | (1, 6, 6) => 1
        | (2, 11, 11) => 50
        | (2, 11, 12) => 50
        | (2, 11, 6) => 50
        | (2, 12, 11) => 27
        | (2, 12, 12) => 2
        | (2, 12, 6) => 2
        | (2, 6, 11) => 27
        | (2, 6, 12) => 2
        | (2, 6, 6) => 2
        | (3, 0, 11) => 56
        | (3, 0, 12) => 1
        | (3, 0, 6) => 1
        | (4, 0, 0) => 1
        | _ => 500
        end,
        (returnGen (MkCtorExprCtorExpr CtorExpr_Bool CtorExpr_Bool))); 
        (* 7 *) (match (size, stack1, stack2) with
        | (1, 11, 11) => 48
        | (1, 11, 12) => 45
        | (1, 11, 6) => 45
        | (1, 12, 11) => 48
        | (1, 12, 12) => 1
        | (1, 12, 6) => 1
        | (1, 6, 11) => 48
        | (1, 6, 12) => 1
        | (1, 6, 6) => 1
        | (2, 11, 11) => 50
        | (2, 11, 12) => 49
        | (2, 11, 6) => 49
        | (2, 12, 11) => 34
        | (2, 12, 12) => 3
        | (2, 12, 6) => 3
        | (2, 6, 11) => 34
        | (2, 6, 12) => 3
        | (2, 6, 6) => 3
        | (3, 0, 11) => 46
        | (3, 0, 12) => 2
        | (3, 0, 6) => 2
        | (4, 0, 0) => 2
        | _ => 500
        end,
        (returnGen (MkCtorExprCtorExpr CtorExpr_Abs CtorExpr_Bool))); 
        (* 8 *) (match (size, stack1, stack2) with
        | (1, 11, 11) => 51
        | (1, 11, 12) => 53
        | (1, 11, 6) => 53
        | (1, 12, 11) => 51
        | (1, 12, 12) => 1
        | (1, 12, 6) => 1
        | (1, 6, 11) => 51
        | (1, 6, 12) => 1
        | (1, 6, 6) => 1
        | (2, 11, 11) => 50
        | (2, 11, 12) => 50
        | (2, 11, 6) => 50
        | (2, 12, 11) => 51
        | (2, 12, 12) => 2
        | (2, 12, 6) => 2
        | (2, 6, 11) => 51
        | (2, 6, 12) => 2
        | (2, 6, 6) => 2
        | (3, 0, 11) => 48
        | (3, 0, 12) => 2
        | (3, 0, 6) => 2
        | (4, 0, 0) => 5
        | _ => 500
        end,
        (returnGen (MkCtorExprCtorExpr CtorExpr_App CtorExpr_Bool))); 
        (* 9 *) (match (size, stack1, stack2) with
        | (1, 11, 11) => 48
        | (1, 11, 12) => 45
        | (1, 11, 6) => 45
        | (1, 12, 11) => 48
        | (1, 12, 12) => 1
        | (1, 12, 6) => 1
        | (1, 6, 11) => 48
        | (1, 6, 12) => 1
        | (1, 6, 6) => 1
        | (2, 11, 11) => 50
        | (2, 11, 12) => 49
        | (2, 11, 6) => 49
        | (2, 12, 11) => 34
        | (2, 12, 12) => 3
        | (2, 12, 6) => 3
        | (2, 6, 11) => 34
        | (2, 6, 12) => 3
        | (2, 6, 6) => 3
        | (3, 0, 11) => 46
        | (3, 0, 12) => 2
        | (3, 0, 6) => 2
        | (4, 0, 0) => 2
        | _ => 500
        end,
        (returnGen (MkCtorExprCtorExpr CtorExpr_Var CtorExpr_Abs))); 
        (* 10 *) (match (size, stack1, stack2) with
        | (1, 11, 11) => 48
        | (1, 11, 12) => 45
        | (1, 11, 6) => 45
        | (1, 12, 11) => 48
        | (1, 12, 12) => 1
        | (1, 12, 6) => 1
        | (1, 6, 11) => 48
        | (1, 6, 12) => 1
        | (1, 6, 6) => 1
        | (2, 11, 11) => 50
        | (2, 11, 12) => 49
        | (2, 11, 6) => 49
        | (2, 12, 11) => 34
        | (2, 12, 12) => 3
        | (2, 12, 6) => 3
        | (2, 6, 11) => 34
        | (2, 6, 12) => 3
        | (2, 6, 6) => 3
        | (3, 0, 11) => 46
        | (3, 0, 12) => 2
        | (3, 0, 6) => 2
        | (4, 0, 0) => 2
        | _ => 500
        end,
        (returnGen (MkCtorExprCtorExpr CtorExpr_Bool CtorExpr_Abs))); 
        (* 11 *) (match (size, stack1, stack2) with
        | (1, 11, 11) => 51
        | (1, 11, 12) => 53
        | (1, 11, 6) => 53
        | (1, 12, 11) => 51
        | (1, 12, 12) => 1
        | (1, 12, 6) => 1
        | (1, 6, 11) => 51
        | (1, 6, 12) => 1
        | (1, 6, 6) => 1
        | (2, 11, 11) => 50
        | (2, 11, 12) => 50
        | (2, 11, 6) => 50
        | (2, 12, 11) => 52
        | (2, 12, 12) => 3
        | (2, 12, 6) => 3
        | (2, 6, 11) => 52
        | (2, 6, 12) => 3
        | (2, 6, 6) => 3
        | (3, 0, 11) => 47
        | (3, 0, 12) => 4
        | (3, 0, 6) => 4
        | (4, 0, 0) => 25
        | _ => 500
        end,
        (returnGen (MkCtorExprCtorExpr CtorExpr_Abs CtorExpr_Abs))); 
        (* 12 *) (match (size, stack1, stack2) with
        | (1, 11, 11) => 54
        | (1, 11, 12) => 61
        | (1, 11, 6) => 61
        | (1, 12, 11) => 53
        | (1, 12, 12) => 7
        | (1, 12, 6) => 7
        | (1, 6, 11) => 53
        | (1, 6, 12) => 7
        | (1, 6, 6) => 7
        | (2, 11, 11) => 50
        | (2, 11, 12) => 51
        | (2, 11, 6) => 51
        | (2, 12, 11) => 73
        | (2, 12, 12) => 3
        | (2, 12, 6) => 3
        | (2, 6, 11) => 73
        | (2, 6, 12) => 3
        | (2, 6, 6) => 3
        | (3, 0, 11) => 49
        | (3, 0, 12) => 2
        | (3, 0, 6) => 2
        | (4, 0, 0) => 5
        | _ => 500
        end,
        (returnGen (MkCtorExprCtorExpr CtorExpr_App CtorExpr_Abs))); 
        (* 13 *) (match (size, stack1, stack2) with
        | (1, 11, 11) => 51
        | (1, 11, 12) => 53
        | (1, 11, 6) => 53
        | (1, 12, 11) => 51
        | (1, 12, 12) => 1
        | (1, 12, 6) => 1
        | (1, 6, 11) => 51
        | (1, 6, 12) => 1
        | (1, 6, 6) => 1
        | (2, 11, 11) => 50
        | (2, 11, 12) => 50
        | (2, 11, 6) => 50
        | (2, 12, 11) => 51
        | (2, 12, 12) => 2
        | (2, 12, 6) => 2
        | (2, 6, 11) => 51
        | (2, 6, 12) => 2
        | (2, 6, 6) => 2
        | (3, 0, 11) => 48
        | (3, 0, 12) => 2
        | (3, 0, 6) => 2
        | (4, 0, 0) => 5
        | _ => 500
        end,
        (returnGen (MkCtorExprCtorExpr CtorExpr_Var CtorExpr_App))); 
        (* 14 *) (match (size, stack1, stack2) with
        | (1, 11, 11) => 51
        | (1, 11, 12) => 53
        | (1, 11, 6) => 53
        | (1, 12, 11) => 51
        | (1, 12, 12) => 1
        | (1, 12, 6) => 1
        | (1, 6, 11) => 51
        | (1, 6, 12) => 1
        | (1, 6, 6) => 1
        | (2, 11, 11) => 50
        | (2, 11, 12) => 50
        | (2, 11, 6) => 50
        | (2, 12, 11) => 51
        | (2, 12, 12) => 2
        | (2, 12, 6) => 2
        | (2, 6, 11) => 51
        | (2, 6, 12) => 2
        | (2, 6, 6) => 2
        | (3, 0, 11) => 48
        | (3, 0, 12) => 2
        | (3, 0, 6) => 2
        | (4, 0, 0) => 5
        | _ => 500
        end,
        (returnGen (MkCtorExprCtorExpr CtorExpr_Bool CtorExpr_App))); 
        (* 15 *) (match (size, stack1, stack2) with
        | (1, 11, 11) => 54
        | (1, 11, 12) => 61
        | (1, 11, 6) => 61
        | (1, 12, 11) => 53
        | (1, 12, 12) => 7
        | (1, 12, 6) => 7
        | (1, 6, 11) => 53
        | (1, 6, 12) => 7
        | (1, 6, 6) => 7
        | (2, 11, 11) => 50
        | (2, 11, 12) => 51
        | (2, 11, 6) => 51
        | (2, 12, 11) => 73
        | (2, 12, 12) => 3
        | (2, 12, 6) => 3
        | (2, 6, 11) => 73
        | (2, 6, 12) => 3
        | (2, 6, 6) => 3
        | (3, 0, 11) => 49
        | (3, 0, 12) => 2
        | (3, 0, 6) => 2
        | (4, 0, 0) => 5
        | _ => 500
        end,
        (returnGen (MkCtorExprCtorExpr CtorExpr_Abs CtorExpr_App))); 
        (* 16 *) (match (size, stack1, stack2) with
        | (1, 11, 11) => 58
        | (1, 11, 12) => 67
        | (1, 11, 6) => 67
        | (1, 12, 11) => 57
        | (1, 12, 12) => 99
        | (1, 12, 6) => 99
        | (1, 6, 11) => 57
        | (1, 6, 12) => 99
        | (1, 6, 6) => 99
        | (2, 11, 11) => 50
        | (2, 11, 12) => 52
        | (2, 11, 6) => 52
        | (2, 12, 11) => 83
        | (2, 12, 12) => 99
        | (2, 12, 6) => 99
        | (2, 6, 11) => 83
        | (2, 6, 12) => 99
        | (2, 6, 6) => 99
        | (3, 0, 11) => 53
        | (3, 0, 12) => 99
        | (3, 0, 6) => 99
        | (4, 0, 0) => 99
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
    | tt => 1
    end,
    (returnGen CtorExpr_Var)); 
    (* 2 *) (match (tt) with
    | tt => 1
    end,
    (returnGen CtorExpr_Bool)); 
    (* 3 *) (match (tt) with
    | tt => 4
    end,
    (returnGen CtorExpr_Abs)); 
    (* 4 *) (match (tt) with
    | tt => 94
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
          
