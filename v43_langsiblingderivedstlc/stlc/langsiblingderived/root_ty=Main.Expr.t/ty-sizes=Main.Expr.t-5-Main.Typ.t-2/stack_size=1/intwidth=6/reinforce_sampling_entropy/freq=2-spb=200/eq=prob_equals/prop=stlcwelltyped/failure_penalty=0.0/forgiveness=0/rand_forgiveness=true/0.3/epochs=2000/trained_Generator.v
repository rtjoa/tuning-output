From QuickChick Require Import QuickChick. Import QcNotation.
From Coq Require Import Bool ZArith List. Import ListNotations.
From ExtLib Require Import Monad.
From ExtLib.Data.Monads Require Import OptionMonad.
Import MonadNotation.

From STLC Require Import Impl Spec.

Inductive CtorExpr :=
  | CtorExpr_Var
  | CtorExpr_Bool
  | CtorExpr_Abs
  | CtorExpr_App.

Inductive LeafCtorExpr :=
  | LeafCtorExpr_Var
  | LeafCtorExpr_Bool.

Inductive CtorTyp :=
  | CtorTyp_TBool
  | CtorTyp_TFun.

Inductive LeafCtorTyp :=
  | LeafCtorTyp_TBool.

Inductive TupLeafCtorExprLeafCtorExpr :=
  | MkLeafCtorExprLeafCtorExpr : LeafCtorExpr -> LeafCtorExpr -> TupLeafCtorExprLeafCtorExpr.

Inductive TupCtorTypCtorExpr :=
  | MkCtorTypCtorExpr : CtorTyp -> CtorExpr -> TupCtorTypCtorExpr.

Inductive TupCtorTypCtorTyp :=
  | MkCtorTypCtorTyp : CtorTyp -> CtorTyp -> TupCtorTypCtorTyp.

Inductive TupCtorTypLeafCtorExpr :=
  | MkCtorTypLeafCtorExpr : CtorTyp -> LeafCtorExpr -> TupCtorTypLeafCtorExpr.

Inductive TupLeafCtorTypLeafCtorTyp :=
  | MkLeafCtorTypLeafCtorTyp : LeafCtorTyp -> LeafCtorTyp -> TupLeafCtorTypLeafCtorTyp.

Inductive TupCtorExprCtorExpr :=
  | MkCtorExprCtorExpr : CtorExpr -> CtorExpr -> TupCtorExprCtorExpr.

Definition genLeafTyp (chosen_ctor : LeafCtorTyp) (stack1 : nat) : G (Typ) :=
  match chosen_ctor with
  | LeafCtorTyp_TBool  => 
    (returnGen (TBool ))
  end.

Fixpoint genTyp (size : nat) (chosen_ctor : CtorTyp) (stack1 : nat) : G (Typ) :=
  match size with
  | O  => match chosen_ctor with
    | CtorTyp_TBool  => 
      (returnGen (TBool ))
    | CtorTyp_TFun  => 
      (bindGen 
      (* Frequency2 (single-branch) *) 
      (returnGen (MkLeafCtorTypLeafCtorTyp (LeafCtorTyp_TBool ) (LeafCtorTyp_TBool ))) 
      (fun param_variantis => (let '(MkLeafCtorTypLeafCtorTyp ctor1 ctor2) := param_variantis in

        (bindGen (genLeafTyp ctor1 1) 
        (fun p1 => 
          (bindGen (genLeafTyp ctor2 7) 
          (fun p2 => 
            (returnGen (TFun p1 p2)))))))))
    end
  | S size1 => match chosen_ctor with
    | CtorTyp_TBool  => 
      (returnGen (TBool ))
    | CtorTyp_TFun  => 
      (bindGen 
      (* Frequency3 *) (freq [
        (* 1 *) (match (size, stack1) with
        | (1, 3) => 59
        | (1, 5) => 75
        | _ => 500
        end,
        (returnGen (MkCtorTypCtorTyp (CtorTyp_TBool ) (CtorTyp_TBool )))); 
        (* 2 *) (match (size, stack1) with
        | (1, 3) => 59
        | (1, 5) => 79
        | _ => 500
        end,
        (returnGen (MkCtorTypCtorTyp (CtorTyp_TFun ) (CtorTyp_TBool )))); 
        (* 3 *) (match (size, stack1) with
        | (1, 3) => 60
        | (1, 5) => 71
        | _ => 500
        end,
        (returnGen (MkCtorTypCtorTyp (CtorTyp_TBool ) (CtorTyp_TFun )))); 
        (* 4 *) (match (size, stack1) with
        | (1, 3) => 60
        | (1, 5) => 77
        | _ => 500
        end,
        (returnGen (MkCtorTypCtorTyp (CtorTyp_TFun ) (CtorTyp_TFun ))))]) 
      (fun param_variantis => (let '(MkCtorTypCtorTyp ctor1 ctor2) := param_variantis in

        (bindGen (genTyp size1 ctor1 2) 
        (fun p1 => 
          (bindGen (genTyp size1 ctor2 8) 
          (fun p2 => 
            (returnGen (TFun p1 p2)))))))))
    end
  end.

Definition genLeafExpr (chosen_ctor : LeafCtorExpr) (stack1 : nat) : G (Expr) :=
  match chosen_ctor with
  | LeafCtorExpr_Var  => 
    (bindGen 
    (* GenNat1 *)
    (let _weight_1 := match (stack1) with
    | (10) => 50
    | (4) => 50
    | (9) => 40
    | _ => 500
    end
    in
    bindGen (freq [
      (_weight_1, returnGen 1);
      (100-_weight_1, returnGen 0)
    ]) (fun n1 =>
    (let _weight_2 := match (stack1) with
    | (10) => 50
    | (4) => 52
    | (9) => 58
    | _ => 500
    end
    in
    bindGen (freq [
      (_weight_2, returnGen 2);
      (100-_weight_2, returnGen 0)
    ]) (fun n2 =>
    (let _weight_4 := match (stack1) with
    | (10) => 50
    | (4) => 44
    | (9) => 0
    | _ => 500
    end
    in
    bindGen (freq [
      (_weight_4, returnGen 4);
      (100-_weight_4, returnGen 0)
    ]) (fun n4 =>
    (let _weight_8 := match (stack1) with
    | (10) => 50
    | (4) => 44
    | (9) => 0
    | _ => 500
    end
    in
    bindGen (freq [
      (_weight_8, returnGen 8);
      (100-_weight_8, returnGen 0)
    ]) (fun n8 =>
    (let _weight_16 := match (stack1) with
    | (10) => 50
    | (4) => 44
    | (9) => 0
    | _ => 500
    end
    in
    bindGen (freq [
      (_weight_16, returnGen 16);
      (100-_weight_16, returnGen 0)
    ]) (fun n16 =>
    (let _weight_32 := match (stack1) with
    | (10) => 50
    | (4) => 44
    | (9) => 0
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
      (returnGen (Var p1))))
  | LeafCtorExpr_Bool  => 
    (bindGen 
    (* GenBool1 *) (let _weight_true := match (stack1) with
    | (10) => 54
    | (4) => 50
    | (9) => 32
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

Fixpoint genExpr (size : nat) (chosen_ctor : CtorExpr) (stack1 : nat) : G (Expr) :=
  match size with
  | O  => match chosen_ctor with
    | CtorExpr_Var  => 
      (bindGen 
      (* GenNat2 *)
      (let _weight_1 := match (stack1) with
      | (11) => 59
      | (12) => 49
      | (6) => 51
      | _ => 500
      end
      in
      bindGen (freq [
        (_weight_1, returnGen 1);
        (100-_weight_1, returnGen 0)
      ]) (fun n1 =>
      (let _weight_2 := match (stack1) with
      | (11) => 52
      | (12) => 49
      | (6) => 49
      | _ => 500
      end
      in
      bindGen (freq [
        (_weight_2, returnGen 2);
        (100-_weight_2, returnGen 0)
      ]) (fun n2 =>
      (let _weight_4 := match (stack1) with
      | (11) => 1
      | (12) => 49
      | (6) => 49
      | _ => 500
      end
      in
      bindGen (freq [
        (_weight_4, returnGen 4);
        (100-_weight_4, returnGen 0)
      ]) (fun n4 =>
      (let _weight_8 := match (stack1) with
      | (11) => 1
      | (12) => 49
      | (6) => 49
      | _ => 500
      end
      in
      bindGen (freq [
        (_weight_8, returnGen 8);
        (100-_weight_8, returnGen 0)
      ]) (fun n8 =>
      (let _weight_16 := match (stack1) with
      | (11) => 1
      | (12) => 49
      | (6) => 49
      | _ => 500
      end
      in
      bindGen (freq [
        (_weight_16, returnGen 16);
        (100-_weight_16, returnGen 0)
      ]) (fun n16 =>
      (let _weight_32 := match (stack1) with
      | (11) => 1
      | (12) => 49
      | (6) => 49
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
        (returnGen (Var p1))))
    | CtorExpr_Bool  => 
      (bindGen 
      (* GenBool2 *) (let _weight_true := match (stack1) with
      | (11) => 52
      | (12) => 56
      | (6) => 50
      | _ => 500
      end
      in
      freq [
        (_weight_true, returnGen true);
        (100-_weight_true, returnGen false)
      ]) 
      (fun p1 => 
        (returnGen (Bool p1))))
    | CtorExpr_Abs  => 
      (bindGen 
      (* Frequency4 *) (freq [
        (* 1 *) (match (stack1) with
        | (11) => 10
        | (12) => 51
        | (6) => 49
        | _ => 500
        end,
        (returnGen (MkCtorTypLeafCtorExpr (CtorTyp_TBool ) (LeafCtorExpr_Var )))); 
        (* 2 *) (match (stack1) with
        | (11) => 88
        | (12) => 49
        | (6) => 46
        | _ => 500
        end,
        (returnGen (MkCtorTypLeafCtorExpr (CtorTyp_TFun ) (LeafCtorExpr_Var )))); 
        (* 3 *) (match (stack1) with
        | (11) => 8
        | (12) => 50
        | (6) => 55
        | _ => 500
        end,
        (returnGen (MkCtorTypLeafCtorExpr (CtorTyp_TBool ) (LeafCtorExpr_Bool )))); 
        (* 4 *) (match (stack1) with
        | (11) => 55
        | (12) => 50
        | (6) => 49
        | _ => 500
        end,
        (returnGen (MkCtorTypLeafCtorExpr (CtorTyp_TFun ) (LeafCtorExpr_Bool ))))]) 
      (fun param_variantis => (let '(MkCtorTypLeafCtorExpr ctor1 ctor2) := param_variantis in

        (bindGen (genTyp 1 ctor1 3) 
        (fun p1 => 
          (bindGen (genLeafExpr ctor2 9) 
          (fun p2 => 
            (returnGen (Abs p1 p2)))))))))
    | CtorExpr_App  => 
      (bindGen 
      (* Frequency5 *) (freq [
        (* 1 *) (match (stack1) with
        | (11) => 49
        | (12) => 50
        | (6) => 50
        | _ => 500
        end,
        (returnGen (MkLeafCtorExprLeafCtorExpr (LeafCtorExpr_Var ) (LeafCtorExpr_Var )))); 
        (* 2 *) (match (stack1) with
        | (11) => 49
        | (12) => 50
        | (6) => 50
        | _ => 500
        end,
        (returnGen (MkLeafCtorExprLeafCtorExpr (LeafCtorExpr_Bool ) (LeafCtorExpr_Var )))); 
        (* 3 *) (match (stack1) with
        | (11) => 54
        | (12) => 50
        | (6) => 50
        | _ => 500
        end,
        (returnGen (MkLeafCtorExprLeafCtorExpr (LeafCtorExpr_Var ) (LeafCtorExpr_Bool )))); 
        (* 4 *) (match (stack1) with
        | (11) => 49
        | (12) => 50
        | (6) => 50
        | _ => 500
        end,
        (returnGen (MkLeafCtorExprLeafCtorExpr (LeafCtorExpr_Bool ) (LeafCtorExpr_Bool ))))]) 
      (fun param_variantis => (let '(MkLeafCtorExprLeafCtorExpr ctor1 ctor2) := param_variantis in

        (bindGen (genLeafExpr ctor1 4) 
        (fun p1 => 
          (bindGen (genLeafExpr ctor2 10) 
          (fun p2 => 
            (returnGen (App p1 p2)))))))))
    end
  | S size1 => match chosen_ctor with
    | CtorExpr_Var  => 
      (bindGen 
      (* GenNat3 *)
      (let _weight_1 := match (size, stack1) with
      | (1, 11) => 16
      | (1, 12) => 50
      | (1, 6) => 51
      | (2, 11) => 49
      | (2, 12) => 50
      | (2, 6) => 49
      | (3, 11) => 41
      | (3, 12) => 50
      | (3, 6) => 50
      | (4, 0) => 50
      | _ => 500
      end
      in
      bindGen (freq [
        (_weight_1, returnGen 1);
        (100-_weight_1, returnGen 0)
      ]) (fun n1 =>
      (let _weight_2 := match (size, stack1) with
      | (1, 11) => 22
      | (1, 12) => 50
      | (1, 6) => 48
      | (2, 11) => 17
      | (2, 12) => 50
      | (2, 6) => 49
      | (3, 11) => 41
      | (3, 12) => 50
      | (3, 6) => 50
      | (4, 0) => 50
      | _ => 500
      end
      in
      bindGen (freq [
        (_weight_2, returnGen 2);
        (100-_weight_2, returnGen 0)
      ]) (fun n2 =>
      (let _weight_4 := match (size, stack1) with
      | (1, 11) => 4
      | (1, 12) => 50
      | (1, 6) => 48
      | (2, 11) => 17
      | (2, 12) => 50
      | (2, 6) => 49
      | (3, 11) => 41
      | (3, 12) => 50
      | (3, 6) => 50
      | (4, 0) => 50
      | _ => 500
      end
      in
      bindGen (freq [
        (_weight_4, returnGen 4);
        (100-_weight_4, returnGen 0)
      ]) (fun n4 =>
      (let _weight_8 := match (size, stack1) with
      | (1, 11) => 4
      | (1, 12) => 50
      | (1, 6) => 48
      | (2, 11) => 17
      | (2, 12) => 50
      | (2, 6) => 49
      | (3, 11) => 41
      | (3, 12) => 50
      | (3, 6) => 50
      | (4, 0) => 50
      | _ => 500
      end
      in
      bindGen (freq [
        (_weight_8, returnGen 8);
        (100-_weight_8, returnGen 0)
      ]) (fun n8 =>
      (let _weight_16 := match (size, stack1) with
      | (1, 11) => 4
      | (1, 12) => 50
      | (1, 6) => 48
      | (2, 11) => 17
      | (2, 12) => 50
      | (2, 6) => 49
      | (3, 11) => 41
      | (3, 12) => 50
      | (3, 6) => 50
      | (4, 0) => 50
      | _ => 500
      end
      in
      bindGen (freq [
        (_weight_16, returnGen 16);
        (100-_weight_16, returnGen 0)
      ]) (fun n16 =>
      (let _weight_32 := match (size, stack1) with
      | (1, 11) => 4
      | (1, 12) => 50
      | (1, 6) => 48
      | (2, 11) => 17
      | (2, 12) => 50
      | (2, 6) => 49
      | (3, 11) => 41
      | (3, 12) => 50
      | (3, 6) => 50
      | (4, 0) => 50
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
        (returnGen (Var p1))))
    | CtorExpr_Bool  => 
      (bindGen 
      (* GenBool3 *) (let _weight_true := match (size, stack1) with
      | (1, 11) => 40
      | (1, 12) => 51
      | (1, 6) => 50
      | (2, 11) => 59
      | (2, 12) => 49
      | (2, 6) => 50
      | (3, 11) => 55
      | (3, 12) => 51
      | (3, 6) => 50
      | (4, 0) => 45
      | _ => 500
      end
      in
      freq [
        (_weight_true, returnGen true);
        (100-_weight_true, returnGen false)
      ]) 
      (fun p1 => 
        (returnGen (Bool p1))))
    | CtorExpr_Abs  => 
      (bindGen 
      (* Frequency6 *) (freq [
        (* 1 *) (match (size, stack1) with
        | (1, 11) => 3
        | (1, 12) => 50
        | (1, 6) => 50
        | (2, 11) => 0
        | (2, 12) => 50
        | (2, 6) => 49
        | (3, 11) => 0
        | (3, 12) => 50
        | (3, 6) => 49
        | (4, 0) => 0
        | _ => 500
        end,
        (returnGen (MkCtorTypCtorExpr (CtorTyp_TBool ) (CtorExpr_Var )))); 
        (* 2 *) (match (size, stack1) with
        | (1, 11) => 12
        | (1, 12) => 50
        | (1, 6) => 49
        | (2, 11) => 0
        | (2, 12) => 50
        | (2, 6) => 49
        | (3, 11) => 0
        | (3, 12) => 50
        | (3, 6) => 49
        | (4, 0) => 0
        | _ => 500
        end,
        (returnGen (MkCtorTypCtorExpr (CtorTyp_TFun ) (CtorExpr_Var )))); 
        (* 3 *) (match (size, stack1) with
        | (1, 11) => 2
        | (1, 12) => 50
        | (1, 6) => 54
        | (2, 11) => 0
        | (2, 12) => 51
        | (2, 6) => 54
        | (3, 11) => 0
        | (3, 12) => 51
        | (3, 6) => 52
        | (4, 0) => 0
        | _ => 500
        end,
        (returnGen (MkCtorTypCtorExpr (CtorTyp_TBool ) (CtorExpr_Bool )))); 
        (* 4 *) (match (size, stack1) with
        | (1, 11) => 4
        | (1, 12) => 50
        | (1, 6) => 49
        | (2, 11) => 2
        | (2, 12) => 50
        | (2, 6) => 49
        | (3, 11) => 0
        | (3, 12) => 50
        | (3, 6) => 49
        | (4, 0) => 0
        | _ => 500
        end,
        (returnGen (MkCtorTypCtorExpr (CtorTyp_TFun ) (CtorExpr_Bool )))); 
        (* 5 *) (match (size, stack1) with
        | (1, 11) => 30
        | (1, 12) => 50
        | (1, 6) => 53
        | (2, 11) => 21
        | (2, 12) => 50
        | (2, 6) => 52
        | (3, 11) => 21
        | (3, 12) => 50
        | (3, 6) => 51
        | (4, 0) => 18
        | _ => 500
        end,
        (returnGen (MkCtorTypCtorExpr (CtorTyp_TBool ) (CtorExpr_Abs )))); 
        (* 6 *) (match (size, stack1) with
        | (1, 11) => 97
        | (1, 12) => 50
        | (1, 6) => 49
        | (2, 11) => 98
        | (2, 12) => 50
        | (2, 6) => 49
        | (3, 11) => 98
        | (3, 12) => 50
        | (3, 6) => 50
        | (4, 0) => 98
        | _ => 500
        end,
        (returnGen (MkCtorTypCtorExpr (CtorTyp_TFun ) (CtorExpr_Abs )))); 
        (* 7 *) (match (size, stack1) with
        | (1, 11) => 0
        | (1, 12) => 50
        | (1, 6) => 49
        | (2, 11) => 0
        | (2, 12) => 50
        | (2, 6) => 49
        | (3, 11) => 0
        | (3, 12) => 50
        | (3, 6) => 49
        | (4, 0) => 0
        | _ => 500
        end,
        (returnGen (MkCtorTypCtorExpr (CtorTyp_TBool ) (CtorExpr_App )))); 
        (* 8 *) (match (size, stack1) with
        | (1, 11) => 0
        | (1, 12) => 50
        | (1, 6) => 49
        | (2, 11) => 0
        | (2, 12) => 50
        | (2, 6) => 49
        | (3, 11) => 0
        | (3, 12) => 50
        | (3, 6) => 49
        | (4, 0) => 0
        | _ => 500
        end,
        (returnGen (MkCtorTypCtorExpr (CtorTyp_TFun ) (CtorExpr_App ))))]) 
      (fun param_variantis => (let '(MkCtorTypCtorExpr ctor1 ctor2) := param_variantis in

        (bindGen (genTyp 1 ctor1 5) 
        (fun p1 => 
          (bindGen (genExpr size1 ctor2 11) 
          (fun p2 => 
            (returnGen (Abs p1 p2)))))))))
    | CtorExpr_App  => 
      (bindGen 
      (* Frequency7 *) (freq [
        (* 1 *) (match (size, stack1) with
        | (1, 11) => 49
        | (1, 12) => 50
        | (1, 6) => 50
        | (2, 11) => 49
        | (2, 12) => 50
        | (2, 6) => 50
        | (3, 11) => 49
        | (3, 12) => 50
        | (3, 6) => 50
        | (4, 0) => 50
        | _ => 500
        end,
        (returnGen (MkCtorExprCtorExpr (CtorExpr_Var ) (CtorExpr_Var )))); 
        (* 2 *) (match (size, stack1) with
        | (1, 11) => 49
        | (1, 12) => 50
        | (1, 6) => 50
        | (2, 11) => 49
        | (2, 12) => 50
        | (2, 6) => 50
        | (3, 11) => 49
        | (3, 12) => 50
        | (3, 6) => 50
        | (4, 0) => 50
        | _ => 500
        end,
        (returnGen (MkCtorExprCtorExpr (CtorExpr_Bool ) (CtorExpr_Var )))); 
        (* 3 *) (match (size, stack1) with
        | (1, 11) => 50
        | (1, 12) => 50
        | (1, 6) => 50
        | (2, 11) => 49
        | (2, 12) => 50
        | (2, 6) => 50
        | (3, 11) => 49
        | (3, 12) => 50
        | (3, 6) => 50
        | (4, 0) => 50
        | _ => 500
        end,
        (returnGen (MkCtorExprCtorExpr (CtorExpr_Abs ) (CtorExpr_Var )))); 
        (* 4 *) (match (size, stack1) with
        | (1, 11) => 49
        | (1, 12) => 50
        | (1, 6) => 50
        | (2, 11) => 49
        | (2, 12) => 50
        | (2, 6) => 50
        | (3, 11) => 49
        | (3, 12) => 50
        | (3, 6) => 50
        | (4, 0) => 50
        | _ => 500
        end,
        (returnGen (MkCtorExprCtorExpr (CtorExpr_App ) (CtorExpr_Var )))); 
        (* 5 *) (match (size, stack1) with
        | (1, 11) => 50
        | (1, 12) => 50
        | (1, 6) => 50
        | (2, 11) => 51
        | (2, 12) => 50
        | (2, 6) => 50
        | (3, 11) => 50
        | (3, 12) => 50
        | (3, 6) => 50
        | (4, 0) => 50
        | _ => 500
        end,
        (returnGen (MkCtorExprCtorExpr (CtorExpr_Var ) (CtorExpr_Bool )))); 
        (* 6 *) (match (size, stack1) with
        | (1, 11) => 49
        | (1, 12) => 50
        | (1, 6) => 50
        | (2, 11) => 49
        | (2, 12) => 50
        | (2, 6) => 50
        | (3, 11) => 49
        | (3, 12) => 50
        | (3, 6) => 50
        | (4, 0) => 50
        | _ => 500
        end,
        (returnGen (MkCtorExprCtorExpr (CtorExpr_Bool ) (CtorExpr_Bool )))); 
        (* 7 *) (match (size, stack1) with
        | (1, 11) => 59
        | (1, 12) => 50
        | (1, 6) => 51
        | (2, 11) => 60
        | (2, 12) => 50
        | (2, 6) => 50
        | (3, 11) => 58
        | (3, 12) => 50
        | (3, 6) => 50
        | (4, 0) => 54
        | _ => 500
        end,
        (returnGen (MkCtorExprCtorExpr (CtorExpr_Abs ) (CtorExpr_Bool )))); 
        (* 8 *) (match (size, stack1) with
        | (1, 11) => 49
        | (1, 12) => 50
        | (1, 6) => 50
        | (2, 11) => 50
        | (2, 12) => 50
        | (2, 6) => 50
        | (3, 11) => 49
        | (3, 12) => 50
        | (3, 6) => 50
        | (4, 0) => 50
        | _ => 500
        end,
        (returnGen (MkCtorExprCtorExpr (CtorExpr_App ) (CtorExpr_Bool )))); 
        (* 9 *) (match (size, stack1) with
        | (1, 11) => 49
        | (1, 12) => 50
        | (1, 6) => 50
        | (2, 11) => 49
        | (2, 12) => 50
        | (2, 6) => 50
        | (3, 11) => 49
        | (3, 12) => 50
        | (3, 6) => 50
        | (4, 0) => 50
        | _ => 500
        end,
        (returnGen (MkCtorExprCtorExpr (CtorExpr_Var ) (CtorExpr_Abs )))); 
        (* 10 *) (match (size, stack1) with
        | (1, 11) => 49
        | (1, 12) => 50
        | (1, 6) => 50
        | (2, 11) => 49
        | (2, 12) => 50
        | (2, 6) => 50
        | (3, 11) => 49
        | (3, 12) => 50
        | (3, 6) => 50
        | (4, 0) => 50
        | _ => 500
        end,
        (returnGen (MkCtorExprCtorExpr (CtorExpr_Bool ) (CtorExpr_Abs )))); 
        (* 11 *) (match (size, stack1) with
        | (1, 11) => 52
        | (1, 12) => 50
        | (1, 6) => 50
        | (2, 11) => 49
        | (2, 12) => 50
        | (2, 6) => 50
        | (3, 11) => 50
        | (3, 12) => 50
        | (3, 6) => 50
        | (4, 0) => 50
        | _ => 500
        end,
        (returnGen (MkCtorExprCtorExpr (CtorExpr_Abs ) (CtorExpr_Abs )))); 
        (* 12 *) (match (size, stack1) with
        | (1, 11) => 49
        | (1, 12) => 50
        | (1, 6) => 50
        | (2, 11) => 49
        | (2, 12) => 50
        | (2, 6) => 50
        | (3, 11) => 49
        | (3, 12) => 50
        | (3, 6) => 50
        | (4, 0) => 50
        | _ => 500
        end,
        (returnGen (MkCtorExprCtorExpr (CtorExpr_App ) (CtorExpr_Abs )))); 
        (* 13 *) (match (size, stack1) with
        | (1, 11) => 49
        | (1, 12) => 50
        | (1, 6) => 50
        | (2, 11) => 49
        | (2, 12) => 50
        | (2, 6) => 50
        | (3, 11) => 49
        | (3, 12) => 50
        | (3, 6) => 50
        | (4, 0) => 50
        | _ => 500
        end,
        (returnGen (MkCtorExprCtorExpr (CtorExpr_Var ) (CtorExpr_App )))); 
        (* 14 *) (match (size, stack1) with
        | (1, 11) => 49
        | (1, 12) => 50
        | (1, 6) => 50
        | (2, 11) => 49
        | (2, 12) => 50
        | (2, 6) => 50
        | (3, 11) => 49
        | (3, 12) => 50
        | (3, 6) => 50
        | (4, 0) => 50
        | _ => 500
        end,
        (returnGen (MkCtorExprCtorExpr (CtorExpr_Bool ) (CtorExpr_App )))); 
        (* 15 *) (match (size, stack1) with
        | (1, 11) => 49
        | (1, 12) => 50
        | (1, 6) => 50
        | (2, 11) => 49
        | (2, 12) => 50
        | (2, 6) => 50
        | (3, 11) => 49
        | (3, 12) => 50
        | (3, 6) => 50
        | (4, 0) => 50
        | _ => 500
        end,
        (returnGen (MkCtorExprCtorExpr (CtorExpr_Abs ) (CtorExpr_App )))); 
        (* 16 *) (match (size, stack1) with
        | (1, 11) => 49
        | (1, 12) => 50
        | (1, 6) => 50
        | (2, 11) => 49
        | (2, 12) => 50
        | (2, 6) => 50
        | (3, 11) => 49
        | (3, 12) => 50
        | (3, 6) => 50
        | (4, 0) => 50
        | _ => 500
        end,
        (returnGen (MkCtorExprCtorExpr (CtorExpr_App ) (CtorExpr_App ))))]) 
      (fun param_variantis => (let '(MkCtorExprCtorExpr ctor1 ctor2) := param_variantis in

        (bindGen (genExpr size1 ctor1 6) 
        (fun p1 => 
          (bindGen (genExpr size1 ctor2 12) 
          (fun p2 => 
            (returnGen (App p1 p2)))))))))
    end
  end.

Definition gSized :=

  (bindGen 
  (* Frequency1 *) (freq [
    (* 1 *) (match (tt) with
    | tt => 0
    end,
    (returnGen (CtorExpr_Var ))); 
    (* 2 *) (match (tt) with
    | tt => 0
    end,
    (returnGen (CtorExpr_Bool ))); 
    (* 3 *) (match (tt) with
    | tt => 96
    end,
    (returnGen (CtorExpr_Abs ))); 
    (* 4 *) (match (tt) with
    | tt => 0
    end,
    (returnGen (CtorExpr_App )))]) 
  (fun init_ctor => (genExpr 4 init_ctor 0))).

Definition test_prop_SinglePreserve :=
forAll gSized (fun (e: Expr) =>
  prop_SinglePreserve e).

(*! QuickChick test_prop_SinglePreserve. *)

Definition test_prop_MultiPreserve :=
forAll gSized (fun (e: Expr) =>
  prop_MultiPreserve e).

(*! QuickChick test_prop_MultiPreserve. *)
          
