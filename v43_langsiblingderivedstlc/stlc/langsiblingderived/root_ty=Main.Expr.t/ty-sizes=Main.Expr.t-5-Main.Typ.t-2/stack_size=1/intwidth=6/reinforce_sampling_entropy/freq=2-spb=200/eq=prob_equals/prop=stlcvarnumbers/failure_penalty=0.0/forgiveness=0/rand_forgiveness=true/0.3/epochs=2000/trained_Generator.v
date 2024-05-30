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

Inductive TupLeafCtorTypLeafCtorTyp :=
  | MkLeafCtorTypLeafCtorTyp : LeafCtorTyp -> LeafCtorTyp -> TupLeafCtorTypLeafCtorTyp.

Inductive TupCtorTypCtorTyp :=
  | MkCtorTypCtorTyp : CtorTyp -> CtorTyp -> TupCtorTypCtorTyp.

Inductive TupCtorTypCtorExpr :=
  | MkCtorTypCtorExpr : CtorTyp -> CtorExpr -> TupCtorTypCtorExpr.

Inductive TupCtorExprCtorExpr :=
  | MkCtorExprCtorExpr : CtorExpr -> CtorExpr -> TupCtorExprCtorExpr.

Inductive TupCtorTypLeafCtorExpr :=
  | MkCtorTypLeafCtorExpr : CtorTyp -> LeafCtorExpr -> TupCtorTypLeafCtorExpr.

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
        | (1, 3) => 41
        | (1, 5) => 79
        | _ => 500
        end,
        (returnGen (MkCtorTypCtorTyp (CtorTyp_TBool ) (CtorTyp_TBool )))); 
        (* 2 *) (match (size, stack1) with
        | (1, 3) => 72
        | (1, 5) => 78
        | _ => 500
        end,
        (returnGen (MkCtorTypCtorTyp (CtorTyp_TFun ) (CtorTyp_TBool )))); 
        (* 3 *) (match (size, stack1) with
        | (1, 3) => 51
        | (1, 5) => 77
        | _ => 500
        end,
        (returnGen (MkCtorTypCtorTyp (CtorTyp_TBool ) (CtorTyp_TFun )))); 
        (* 4 *) (match (size, stack1) with
        | (1, 3) => 71
        | (1, 5) => 81
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
    | (10) => 15
    | (4) => 29
    | (9) => 61
    | _ => 500
    end
    in
    bindGen (freq [
      (_weight_1, returnGen 1);
      (100-_weight_1, returnGen 0)
    ]) (fun n1 =>
    (let _weight_2 := match (stack1) with
    | (10) => 8
    | (4) => 5
    | (9) => 37
    | _ => 500
    end
    in
    bindGen (freq [
      (_weight_2, returnGen 2);
      (100-_weight_2, returnGen 0)
    ]) (fun n2 =>
    (let _weight_4 := match (stack1) with
    | (10) => 1
    | (4) => 1
    | (9) => 0
    | _ => 500
    end
    in
    bindGen (freq [
      (_weight_4, returnGen 4);
      (100-_weight_4, returnGen 0)
    ]) (fun n4 =>
    (let _weight_8 := match (stack1) with
    | (10) => 1
    | (4) => 1
    | (9) => 0
    | _ => 500
    end
    in
    bindGen (freq [
      (_weight_8, returnGen 8);
      (100-_weight_8, returnGen 0)
    ]) (fun n8 =>
    (let _weight_16 := match (stack1) with
    | (10) => 1
    | (4) => 1
    | (9) => 0
    | _ => 500
    end
    in
    bindGen (freq [
      (_weight_16, returnGen 16);
      (100-_weight_16, returnGen 0)
    ]) (fun n16 =>
    (let _weight_32 := match (stack1) with
    | (10) => 1
    | (4) => 1
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
    | (10) => 66
    | (4) => 48
    | (9) => 52
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
      | (11) => 54
      | (12) => 14
      | (6) => 13
      | _ => 500
      end
      in
      bindGen (freq [
        (_weight_1, returnGen 1);
        (100-_weight_1, returnGen 0)
      ]) (fun n1 =>
      (let _weight_2 := match (stack1) with
      | (11) => 66
      | (12) => 15
      | (6) => 14
      | _ => 500
      end
      in
      bindGen (freq [
        (_weight_2, returnGen 2);
        (100-_weight_2, returnGen 0)
      ]) (fun n2 =>
      (let _weight_4 := match (stack1) with
      | (11) => 0
      | (12) => 2
      | (6) => 3
      | _ => 500
      end
      in
      bindGen (freq [
        (_weight_4, returnGen 4);
        (100-_weight_4, returnGen 0)
      ]) (fun n4 =>
      (let _weight_8 := match (stack1) with
      | (11) => 0
      | (12) => 2
      | (6) => 3
      | _ => 500
      end
      in
      bindGen (freq [
        (_weight_8, returnGen 8);
        (100-_weight_8, returnGen 0)
      ]) (fun n8 =>
      (let _weight_16 := match (stack1) with
      | (11) => 0
      | (12) => 2
      | (6) => 3
      | _ => 500
      end
      in
      bindGen (freq [
        (_weight_16, returnGen 16);
        (100-_weight_16, returnGen 0)
      ]) (fun n16 =>
      (let _weight_32 := match (stack1) with
      | (11) => 0
      | (12) => 2
      | (6) => 3
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
      | (11) => 44
      | (12) => 22
      | (6) => 43
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
        | (11) => 16
        | (12) => 10
        | (6) => 15
        | _ => 500
        end,
        (returnGen (MkCtorTypLeafCtorExpr (CtorTyp_TBool ) (LeafCtorExpr_Var )))); 
        (* 2 *) (match (stack1) with
        | (11) => 88
        | (12) => 82
        | (6) => 83
        | _ => 500
        end,
        (returnGen (MkCtorTypLeafCtorExpr (CtorTyp_TFun ) (LeafCtorExpr_Var )))); 
        (* 3 *) (match (stack1) with
        | (11) => 8
        | (12) => 12
        | (6) => 10
        | _ => 500
        end,
        (returnGen (MkCtorTypLeafCtorExpr (CtorTyp_TBool ) (LeafCtorExpr_Bool )))); 
        (* 4 *) (match (stack1) with
        | (11) => 43
        | (12) => 68
        | (6) => 63
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
        | (11) => 1
        | (12) => 7
        | (6) => 8
        | _ => 500
        end,
        (returnGen (MkLeafCtorExprLeafCtorExpr (LeafCtorExpr_Var ) (LeafCtorExpr_Var )))); 
        (* 2 *) (match (stack1) with
        | (11) => 3
        | (12) => 13
        | (6) => 21
        | _ => 500
        end,
        (returnGen (MkLeafCtorExprLeafCtorExpr (LeafCtorExpr_Bool ) (LeafCtorExpr_Var )))); 
        (* 3 *) (match (stack1) with
        | (11) => 1
        | (12) => 10
        | (6) => 19
        | _ => 500
        end,
        (returnGen (MkLeafCtorExprLeafCtorExpr (LeafCtorExpr_Var ) (LeafCtorExpr_Bool )))); 
        (* 4 *) (match (stack1) with
        | (11) => 94
        | (12) => 89
        | (6) => 87
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
      | (1, 11) => 27
      | (1, 12) => 43
      | (1, 6) => 48
      | (2, 11) => 43
      | (2, 12) => 43
      | (2, 6) => 45
      | (3, 11) => 39
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
      | (1, 11) => 14
      | (1, 12) => 36
      | (1, 6) => 32
      | (2, 11) => 16
      | (2, 12) => 43
      | (2, 6) => 45
      | (3, 11) => 39
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
      | (1, 11) => 5
      | (1, 12) => 36
      | (1, 6) => 32
      | (2, 11) => 16
      | (2, 12) => 43
      | (2, 6) => 45
      | (3, 11) => 39
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
      | (1, 11) => 5
      | (1, 12) => 36
      | (1, 6) => 32
      | (2, 11) => 16
      | (2, 12) => 43
      | (2, 6) => 45
      | (3, 11) => 39
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
      | (1, 11) => 5
      | (1, 12) => 36
      | (1, 6) => 32
      | (2, 11) => 16
      | (2, 12) => 43
      | (2, 6) => 45
      | (3, 11) => 39
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
      | (1, 11) => 5
      | (1, 12) => 36
      | (1, 6) => 32
      | (2, 11) => 16
      | (2, 12) => 43
      | (2, 6) => 45
      | (3, 11) => 39
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
      | (1, 11) => 39
      | (1, 12) => 64
      | (1, 6) => 45
      | (2, 11) => 55
      | (2, 12) => 58
      | (2, 6) => 49
      | (3, 11) => 48
      | (3, 12) => 56
      | (3, 6) => 51
      | (4, 0) => 46
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
        | (1, 11) => 4
        | (1, 12) => 25
        | (1, 6) => 31
        | (2, 11) => 0
        | (2, 12) => 36
        | (2, 6) => 39
        | (3, 11) => 0
        | (3, 12) => 43
        | (3, 6) => 40
        | (4, 0) => 0
        | _ => 500
        end,
        (returnGen (MkCtorTypCtorExpr (CtorTyp_TBool ) (CtorExpr_Var )))); 
        (* 2 *) (match (size, stack1) with
        | (1, 11) => 10
        | (1, 12) => 34
        | (1, 6) => 27
        | (2, 11) => 0
        | (2, 12) => 34
        | (2, 6) => 38
        | (3, 11) => 0
        | (3, 12) => 42
        | (3, 6) => 41
        | (4, 0) => 0
        | _ => 500
        end,
        (returnGen (MkCtorTypCtorExpr (CtorTyp_TFun ) (CtorExpr_Var )))); 
        (* 3 *) (match (size, stack1) with
        | (1, 11) => 2
        | (1, 12) => 57
        | (1, 6) => 49
        | (2, 11) => 0
        | (2, 12) => 59
        | (2, 6) => 63
        | (3, 11) => 0
        | (3, 12) => 53
        | (3, 6) => 52
        | (4, 0) => 0
        | _ => 500
        end,
        (returnGen (MkCtorTypCtorExpr (CtorTyp_TBool ) (CtorExpr_Bool )))); 
        (* 4 *) (match (size, stack1) with
        | (1, 11) => 7
        | (1, 12) => 57
        | (1, 6) => 60
        | (2, 11) => 1
        | (2, 12) => 55
        | (2, 6) => 58
        | (3, 11) => 0
        | (3, 12) => 58
        | (3, 6) => 59
        | (4, 0) => 0
        | _ => 500
        end,
        (returnGen (MkCtorTypCtorExpr (CtorTyp_TFun ) (CtorExpr_Bool )))); 
        (* 5 *) (match (size, stack1) with
        | (1, 11) => 26
        | (1, 12) => 54
        | (1, 6) => 47
        | (2, 11) => 7
        | (2, 12) => 60
        | (2, 6) => 51
        | (3, 11) => 31
        | (3, 12) => 52
        | (3, 6) => 56
        | (4, 0) => 22
        | _ => 500
        end,
        (returnGen (MkCtorTypCtorExpr (CtorTyp_TBool ) (CtorExpr_Abs )))); 
        (* 6 *) (match (size, stack1) with
        | (1, 11) => 96
        | (1, 12) => 60
        | (1, 6) => 71
        | (2, 11) => 14
        | (2, 12) => 62
        | (2, 6) => 58
        | (3, 11) => 98
        | (3, 12) => 56
        | (3, 6) => 57
        | (4, 0) => 98
        | _ => 500
        end,
        (returnGen (MkCtorTypCtorExpr (CtorTyp_TFun ) (CtorExpr_Abs )))); 
        (* 7 *) (match (size, stack1) with
        | (1, 11) => 4
        | (1, 12) => 57
        | (1, 6) => 49
        | (2, 11) => 26
        | (2, 12) => 37
        | (2, 6) => 38
        | (3, 11) => 0
        | (3, 12) => 48
        | (3, 6) => 45
        | (4, 0) => 0
        | _ => 500
        end,
        (returnGen (MkCtorTypCtorExpr (CtorTyp_TBool ) (CtorExpr_App )))); 
        (* 8 *) (match (size, stack1) with
        | (1, 11) => 10
        | (1, 12) => 49
        | (1, 6) => 52
        | (2, 11) => 97
        | (2, 12) => 49
        | (2, 6) => 49
        | (3, 11) => 1
        | (3, 12) => 45
        | (3, 6) => 48
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
        | (1, 11) => 1
        | (1, 12) => 38
        | (1, 6) => 40
        | (2, 11) => 13
        | (2, 12) => 45
        | (2, 6) => 45
        | (3, 11) => 25
        | (3, 12) => 48
        | (3, 6) => 48
        | (4, 0) => 37
        | _ => 500
        end,
        (returnGen (MkCtorExprCtorExpr (CtorExpr_Var ) (CtorExpr_Var )))); 
        (* 2 *) (match (size, stack1) with
        | (1, 11) => 1
        | (1, 12) => 39
        | (1, 6) => 42
        | (2, 11) => 15
        | (2, 12) => 45
        | (2, 6) => 46
        | (3, 11) => 29
        | (3, 12) => 48
        | (3, 6) => 48
        | (4, 0) => 37
        | _ => 500
        end,
        (returnGen (MkCtorExprCtorExpr (CtorExpr_Bool ) (CtorExpr_Var )))); 
        (* 3 *) (match (size, stack1) with
        | (1, 11) => 4
        | (1, 12) => 41
        | (1, 6) => 41
        | (2, 11) => 15
        | (2, 12) => 45
        | (2, 6) => 45
        | (3, 11) => 26
        | (3, 12) => 48
        | (3, 6) => 48
        | (4, 0) => 37
        | _ => 500
        end,
        (returnGen (MkCtorExprCtorExpr (CtorExpr_Abs ) (CtorExpr_Var )))); 
        (* 4 *) (match (size, stack1) with
        | (1, 11) => 4
        | (1, 12) => 38
        | (1, 6) => 42
        | (2, 11) => 13
        | (2, 12) => 46
        | (2, 6) => 45
        | (3, 11) => 26
        | (3, 12) => 48
        | (3, 6) => 48
        | (4, 0) => 37
        | _ => 500
        end,
        (returnGen (MkCtorExprCtorExpr (CtorExpr_App ) (CtorExpr_Var )))); 
        (* 5 *) (match (size, stack1) with
        | (1, 11) => 1
        | (1, 12) => 40
        | (1, 6) => 40
        | (2, 11) => 16
        | (2, 12) => 47
        | (2, 6) => 45
        | (3, 11) => 29
        | (3, 12) => 48
        | (3, 6) => 48
        | (4, 0) => 37
        | _ => 500
        end,
        (returnGen (MkCtorExprCtorExpr (CtorExpr_Var ) (CtorExpr_Bool )))); 
        (* 6 *) (match (size, stack1) with
        | (1, 11) => 4
        | (1, 12) => 63
        | (1, 6) => 57
        | (2, 11) => 80
        | (2, 12) => 57
        | (2, 6) => 62
        | (3, 11) => 79
        | (3, 12) => 59
        | (3, 6) => 58
        | (4, 0) => 75
        | _ => 500
        end,
        (returnGen (MkCtorExprCtorExpr (CtorExpr_Bool ) (CtorExpr_Bool )))); 
        (* 7 *) (match (size, stack1) with
        | (1, 11) => 21
        | (1, 12) => 61
        | (1, 6) => 66
        | (2, 11) => 79
        | (2, 12) => 62
        | (2, 6) => 57
        | (3, 11) => 74
        | (3, 12) => 52
        | (3, 6) => 53
        | (4, 0) => 71
        | _ => 500
        end,
        (returnGen (MkCtorExprCtorExpr (CtorExpr_Abs ) (CtorExpr_Bool )))); 
        (* 8 *) (match (size, stack1) with
        | (1, 11) => 7
        | (1, 12) => 57
        | (1, 6) => 54
        | (2, 11) => 58
        | (2, 12) => 52
        | (2, 6) => 47
        | (3, 11) => 55
        | (3, 12) => 48
        | (3, 6) => 51
        | (4, 0) => 49
        | _ => 500
        end,
        (returnGen (MkCtorExprCtorExpr (CtorExpr_App ) (CtorExpr_Bool )))); 
        (* 9 *) (match (size, stack1) with
        | (1, 11) => 2
        | (1, 12) => 40
        | (1, 6) => 44
        | (2, 11) => 16
        | (2, 12) => 45
        | (2, 6) => 46
        | (3, 11) => 26
        | (3, 12) => 48
        | (3, 6) => 48
        | (4, 0) => 37
        | _ => 500
        end,
        (returnGen (MkCtorExprCtorExpr (CtorExpr_Var ) (CtorExpr_Abs )))); 
        (* 10 *) (match (size, stack1) with
        | (1, 11) => 23
        | (1, 12) => 60
        | (1, 6) => 59
        | (2, 11) => 78
        | (2, 12) => 58
        | (2, 6) => 59
        | (3, 11) => 75
        | (3, 12) => 56
        | (3, 6) => 50
        | (4, 0) => 66
        | _ => 500
        end,
        (returnGen (MkCtorExprCtorExpr (CtorExpr_Bool ) (CtorExpr_Abs )))); 
        (* 11 *) (match (size, stack1) with
        | (1, 11) => 98
        | (1, 12) => 60
        | (1, 6) => 56
        | (2, 11) => 79
        | (2, 12) => 52
        | (2, 6) => 52
        | (3, 11) => 68
        | (3, 12) => 52
        | (3, 6) => 50
        | (4, 0) => 58
        | _ => 500
        end,
        (returnGen (MkCtorExprCtorExpr (CtorExpr_Abs ) (CtorExpr_Abs )))); 
        (* 12 *) (match (size, stack1) with
        | (1, 11) => 87
        | (1, 12) => 61
        | (1, 6) => 50
        | (2, 11) => 53
        | (2, 12) => 47
        | (2, 6) => 48
        | (3, 11) => 50
        | (3, 12) => 48
        | (3, 6) => 50
        | (4, 0) => 48
        | _ => 500
        end,
        (returnGen (MkCtorExprCtorExpr (CtorExpr_App ) (CtorExpr_Abs )))); 
        (* 13 *) (match (size, stack1) with
        | (1, 11) => 2
        | (1, 12) => 39
        | (1, 6) => 46
        | (2, 11) => 14
        | (2, 12) => 46
        | (2, 6) => 46
        | (3, 11) => 25
        | (3, 12) => 48
        | (3, 6) => 48
        | (4, 0) => 37
        | _ => 500
        end,
        (returnGen (MkCtorExprCtorExpr (CtorExpr_Var ) (CtorExpr_App )))); 
        (* 14 *) (match (size, stack1) with
        | (1, 11) => 8
        | (1, 12) => 43
        | (1, 6) => 55
        | (2, 11) => 48
        | (2, 12) => 54
        | (2, 6) => 51
        | (3, 11) => 56
        | (3, 12) => 51
        | (3, 6) => 50
        | (4, 0) => 53
        | _ => 500
        end,
        (returnGen (MkCtorExprCtorExpr (CtorExpr_Bool ) (CtorExpr_App )))); 
        (* 15 *) (match (size, stack1) with
        | (1, 11) => 65
        | (1, 12) => 51
        | (1, 6) => 50
        | (2, 11) => 67
        | (2, 12) => 51
        | (2, 6) => 53
        | (3, 11) => 49
        | (3, 12) => 48
        | (3, 6) => 50
        | (4, 0) => 48
        | _ => 500
        end,
        (returnGen (MkCtorExprCtorExpr (CtorExpr_Abs ) (CtorExpr_App )))); 
        (* 16 *) (match (size, stack1) with
        | (1, 11) => 13
        | (1, 12) => 53
        | (1, 6) => 47
        | (2, 11) => 45
        | (2, 12) => 45
        | (2, 6) => 50
        | (3, 11) => 35
        | (3, 12) => 48
        | (3, 6) => 48
        | (4, 0) => 39
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
          
