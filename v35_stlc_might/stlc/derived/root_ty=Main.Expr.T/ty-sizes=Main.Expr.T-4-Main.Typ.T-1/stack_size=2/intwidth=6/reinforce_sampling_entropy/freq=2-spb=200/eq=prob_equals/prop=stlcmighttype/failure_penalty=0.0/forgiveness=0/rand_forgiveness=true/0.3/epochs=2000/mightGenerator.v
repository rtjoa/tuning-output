From QuickChick Require Import QuickChick. Import QcNotation.
From Coq Require Import Bool ZArith List. Import ListNotations.
From ExtLib Require Import Monad.
From ExtLib.Data.Monads Require Import OptionMonad.
Import MonadNotation.

From STLC Require Import Impl Spec.

Inductive Typ_leaf_ctor :=
  | Ctor_leaf_TBool.

Inductive Expr_leaf_ctor :=
  | Ctor_leaf_Var
  | Ctor_leaf_Bool.

Inductive Typ_ctor :=
  | Ctor_TBool
  | Ctor_TFun.

Inductive Expr_ctor :=
  | Ctor_Var
  | Ctor_Bool
  | Ctor_Abs
  | Ctor_App.

Inductive Typ_ctor_Typ_ctor :=
  | MkTyp_ctor_Typ_ctor : Typ_ctor -> Typ_ctor -> Typ_ctor_Typ_ctor.
Inductive Expr_ctor_Expr_ctor :=
  | MkExpr_ctor_Expr_ctor : Expr_ctor -> Expr_ctor -> Expr_ctor_Expr_ctor.
Inductive Expr_leaf_ctor_Expr_leaf_ctor :=
  | MkExpr_leaf_ctor_Expr_leaf_ctor : Expr_leaf_ctor -> Expr_leaf_ctor -> Expr_leaf_ctor_Expr_leaf_ctor.
Inductive Typ_ctor_Expr_ctor :=
  | MkTyp_ctor_Expr_ctor : Typ_ctor -> Expr_ctor -> Typ_ctor_Expr_ctor.
Inductive Typ_ctor_Expr_leaf_ctor :=
  | MkTyp_ctor_Expr_leaf_ctor : Typ_ctor -> Expr_leaf_ctor -> Typ_ctor_Expr_leaf_ctor.
Inductive Typ_leaf_ctor_Typ_leaf_ctor :=
  | MkTyp_leaf_ctor_Typ_leaf_ctor : Typ_leaf_ctor -> Typ_leaf_ctor -> Typ_leaf_ctor_Typ_leaf_ctor.
Definition gen_leaf_Typ (chosen_ctor : Typ_leaf_ctor) (stack1 : nat) (stack2 : nat) : G Typ :=
  match chosen_ctor with
  | Ctor_leaf_TBool =>
    returnGen (TBool )
  end.

Definition gen_leaf_Expr (chosen_ctor : Expr_leaf_ctor) (stack1 : nat) (stack2 : nat) : G Expr :=
  match chosen_ctor with
  | Ctor_leaf_Var =>
    let weight_1 :=
    match ((stack1 : nat), (stack2 : nat)) with 
    | (4, 4) => 16
    | (4, 5) => 100
    | (4, 6) => 11
    | (5, 4) => 87
    | (5, 5) => 86
    | (5, 6) => 93
    | (6, 4) => 88
    | (6, 5) => 13
    | (6, 6) => 9
    | _ => 500
    end
    in
    bindGen (freq [
      (weight_1, returnGen 1);
      (100-weight_1, returnGen 0)
    ]) (fun n1 =>
    let weight_2 :=
    match ((stack1 : nat), (stack2 : nat)) with 
    | (4, 4) => 28
    | (4, 5) => 1
    | (4, 6) => 6
    | (5, 4) => 10
    | (5, 5) => 88
    | (5, 6) => 90
    | (6, 4) => 11
    | (6, 5) => 89
    | (6, 6) => 6
    | _ => 500
    end
    in
    bindGen (freq [
      (weight_2, returnGen 2);
      (100-weight_2, returnGen 0)
    ]) (fun n2 =>
    let weight_4 :=
    match ((stack1 : nat), (stack2 : nat)) with 
    | (4, 4) => 95
    | (4, 5) => 72
    | (4, 6) => 70
    | (5, 4) => 13
    | (5, 5) => 88
    | (5, 6) => 100
    | (6, 4) => 88
    | (6, 5) => 84
    | (6, 6) => 91
    | _ => 500
    end
    in
    bindGen (freq [
      (weight_4, returnGen 4);
      (100-weight_4, returnGen 0)
    ]) (fun n4 =>
    let weight_8 :=
    match ((stack1 : nat), (stack2 : nat)) with 
    | (4, 4) => 72
    | (4, 5) => 57
    | (4, 6) => 37
    | (5, 4) => 13
    | (5, 5) => 100
    | (5, 6) => 10
    | (6, 4) => 91
    | (6, 5) => 8
    | (6, 6) => 89
    | _ => 500
    end
    in
    bindGen (freq [
      (weight_8, returnGen 8);
      (100-weight_8, returnGen 0)
    ]) (fun n8 =>
    let weight_16 :=
    match ((stack1 : nat), (stack2 : nat)) with 
    | (4, 4) => 81
    | (4, 5) => 52
    | (4, 6) => 80
    | (5, 4) => 11
    | (5, 5) => 95
    | (5, 6) => 11
    | (6, 4) => 9
    | (6, 5) => 8
    | (6, 6) => 9
    | _ => 500
    end
    in
    bindGen (freq [
      (weight_16, returnGen 16);
      (100-weight_16, returnGen 0)
    ]) (fun n16 =>
    let weight_32 :=
    match ((stack1 : nat), (stack2 : nat)) with 
    | (4, 4) => 99
    | (4, 5) => 99
    | (4, 6) => 11
    | (5, 4) => 98
    | (5, 5) => 89
    | (5, 6) => 91
    | (6, 4) => 86
    | (6, 5) => 11
    | (6, 6) => 7
    | _ => 500
    end
    in
    bindGen (freq [
      (weight_32, returnGen 32);
      (100-weight_32, returnGen 0)
    ]) (fun n32 =>
    let p1 := n1 + n2 + n4 + n8 + n16 + n32 in 
    returnGen (Var p1)))))))
  | Ctor_leaf_Bool =>
    let weight_true :=
    match ((stack1 : nat), (stack2 : nat)) with 
    | (4, 4) => 18
    | (4, 5) => 92
    | (4, 6) => 3
    | (5, 4) => 2
    | (5, 5) => 51
    | (5, 6) => 97
    | (6, 4) => 40
    | (6, 5) => 57
    | (6, 6) => 97
    | _ => 500
    end
    in
    bindGen (freq [
      (weight_true, returnGen true);
      (100-weight_true, returnGen false)
    ]) (fun p1 : bool =>
    returnGen (Bool p1))
  end.

Fixpoint gen_Typ (size : nat) (chosen_ctor : Typ_ctor) (stack1 : nat) (stack2 : nat) : G Typ :=
  match size with
  | 0 =>
    match chosen_ctor with
    | Ctor_TBool =>
      returnGen (TBool )
    | Ctor_TFun =>
      bindGen (freq [
        (* no alternatives, so lets just put this again *)
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (0, (3, 1)) => 50
          | (0, (3, 2)) => 50
          | _ => 500
          end,
          returnGen (MkTyp_leaf_ctor_Typ_leaf_ctor Ctor_leaf_TBool Ctor_leaf_TBool)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (0, (3, 1)) => 50
          | (0, (3, 2)) => 50
          | _ => 500
          end,
          returnGen (MkTyp_leaf_ctor_Typ_leaf_ctor Ctor_leaf_TBool Ctor_leaf_TBool)
        )
      ]) (fun param_variantis =>
      let '(MkTyp_leaf_ctor_Typ_leaf_ctor param1_ctor param2_ctor) := param_variantis in
      bindGen (gen_leaf_Typ param1_ctor (stack2 : nat) 1)
      (fun p1 : Typ =>
      bindGen (gen_leaf_Typ param2_ctor (stack2 : nat) 2)
      (fun p2 : Typ =>
      returnGen (TFun p1 p2))))
  end
  | S size' =>
    match chosen_ctor with
    | Ctor_TBool =>
      returnGen (TBool )
    | Ctor_TFun =>
      bindGen (freq [
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (0, 3)) => 92
          | (1, (4, 3)) => 17
          | (1, (5, 3)) => 72
          | (1, (6, 3)) => 91
          | _ => 500
          end,
          returnGen (MkTyp_ctor_Typ_ctor Ctor_TBool Ctor_TBool)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (0, 3)) => 92
          | (1, (4, 3)) => 36
          | (1, (5, 3)) => 96
          | (1, (6, 3)) => 91
          | _ => 500
          end,
          returnGen (MkTyp_ctor_Typ_ctor Ctor_TFun Ctor_TBool)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (0, 3)) => 88
          | (1, (4, 3)) => 85
          | (1, (5, 3)) => 55
          | (1, (6, 3)) => 92
          | _ => 500
          end,
          returnGen (MkTyp_ctor_Typ_ctor Ctor_TBool Ctor_TFun)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (0, 3)) => 89
          | (1, (4, 3)) => 78
          | (1, (5, 3)) => 95
          | (1, (6, 3)) => 91
          | _ => 500
          end,
          returnGen (MkTyp_ctor_Typ_ctor Ctor_TFun Ctor_TFun)
        )
      ]) (fun param_variantis =>
      let '(MkTyp_ctor_Typ_ctor param1_ctor param2_ctor) := param_variantis in
      bindGen (gen_Typ size' param1_ctor (stack2 : nat) 1)
      (fun p1 : Typ =>
      bindGen (gen_Typ size' param2_ctor (stack2 : nat) 2)
      (fun p2 : Typ =>
      returnGen (TFun p1 p2))))
  end
  end.

Fixpoint gen_Expr (size : nat) (chosen_ctor : Expr_ctor) (stack1 : nat) (stack2 : nat) : G Expr :=
  match size with
  | 0 =>
    match chosen_ctor with
    | Ctor_Var =>
      let weight_1 :=
      match (size, ((stack1 : nat), (stack2 : nat))) with 
      | (0, (4, 4)) => 26
      | (0, (4, 5)) => 33
      | (0, (4, 6)) => 25
      | (0, (5, 4)) => 3
      | (0, (5, 5)) => 29
      | (0, (5, 6)) => 23
      | (0, (6, 4)) => 11
      | (0, (6, 5)) => 65
      | (0, (6, 6)) => 24
      | _ => 500
      end
      in
      bindGen (freq [
        (weight_1, returnGen 1);
        (100-weight_1, returnGen 0)
      ]) (fun n1 =>
      let weight_2 :=
      match (size, ((stack1 : nat), (stack2 : nat))) with 
      | (0, (4, 4)) => 62
      | (0, (4, 5)) => 81
      | (0, (4, 6)) => 69
      | (0, (5, 4)) => 79
      | (0, (5, 5)) => 48
      | (0, (5, 6)) => 54
      | (0, (6, 4)) => 7
      | (0, (6, 5)) => 2
      | (0, (6, 6)) => 15
      | _ => 500
      end
      in
      bindGen (freq [
        (weight_2, returnGen 2);
        (100-weight_2, returnGen 0)
      ]) (fun n2 =>
      let weight_4 :=
      match (size, ((stack1 : nat), (stack2 : nat))) with 
      | (0, (4, 4)) => 51
      | (0, (4, 5)) => 71
      | (0, (4, 6)) => 83
      | (0, (5, 4)) => 17
      | (0, (5, 5)) => 82
      | (0, (5, 6)) => 30
      | (0, (6, 4)) => 8
      | (0, (6, 5)) => 55
      | (0, (6, 6)) => 32
      | _ => 500
      end
      in
      bindGen (freq [
        (weight_4, returnGen 4);
        (100-weight_4, returnGen 0)
      ]) (fun n4 =>
      let weight_8 :=
      match (size, ((stack1 : nat), (stack2 : nat))) with 
      | (0, (4, 4)) => 22
      | (0, (4, 5)) => 44
      | (0, (4, 6)) => 43
      | (0, (5, 4)) => 6
      | (0, (5, 5)) => 20
      | (0, (5, 6)) => 10
      | (0, (6, 4)) => 47
      | (0, (6, 5)) => 63
      | (0, (6, 6)) => 87
      | _ => 500
      end
      in
      bindGen (freq [
        (weight_8, returnGen 8);
        (100-weight_8, returnGen 0)
      ]) (fun n8 =>
      let weight_16 :=
      match (size, ((stack1 : nat), (stack2 : nat))) with 
      | (0, (4, 4)) => 34
      | (0, (4, 5)) => 19
      | (0, (4, 6)) => 68
      | (0, (5, 4)) => 25
      | (0, (5, 5)) => 66
      | (0, (5, 6)) => 52
      | (0, (6, 4)) => 95
      | (0, (6, 5)) => 5
      | (0, (6, 6)) => 23
      | _ => 500
      end
      in
      bindGen (freq [
        (weight_16, returnGen 16);
        (100-weight_16, returnGen 0)
      ]) (fun n16 =>
      let weight_32 :=
      match (size, ((stack1 : nat), (stack2 : nat))) with 
      | (0, (4, 4)) => 63
      | (0, (4, 5)) => 74
      | (0, (4, 6)) => 81
      | (0, (5, 4)) => 4
      | (0, (5, 5)) => 19
      | (0, (5, 6)) => 32
      | (0, (6, 4)) => 90
      | (0, (6, 5)) => 38
      | (0, (6, 6)) => 37
      | _ => 500
      end
      in
      bindGen (freq [
        (weight_32, returnGen 32);
        (100-weight_32, returnGen 0)
      ]) (fun n32 =>
      let p1 := n1 + n2 + n4 + n8 + n16 + n32 in 
      returnGen (Var p1)))))))
    | Ctor_Bool =>
      let weight_true :=
      match (size, ((stack1 : nat), (stack2 : nat))) with 
      | (0, (4, 4)) => 49
      | (0, (4, 5)) => 8
      | (0, (4, 6)) => 23
      | (0, (5, 4)) => 14
      | (0, (5, 5)) => 88
      | (0, (5, 6)) => 18
      | (0, (6, 4)) => 13
      | (0, (6, 5)) => 36
      | (0, (6, 6)) => 83
      | _ => 500
      end
      in
      bindGen (freq [
        (weight_true, returnGen true);
        (100-weight_true, returnGen false)
      ]) (fun p1 : bool =>
      returnGen (Bool p1))
    | Ctor_Abs =>
      bindGen (freq [
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (0, (4, 4)) => 64
          | (0, (4, 5)) => 28
          | (0, (4, 6)) => 53
          | (0, (5, 4)) => 25
          | (0, (5, 5)) => 1
          | (0, (5, 6)) => 73
          | (0, (6, 4)) => 37
          | (0, (6, 5)) => 6
          | (0, (6, 6)) => 3
          | _ => 500
          end,
          returnGen (MkTyp_ctor_Expr_leaf_ctor Ctor_TBool Ctor_leaf_Var)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (0, (4, 4)) => 56
          | (0, (4, 5)) => 73
          | (0, (4, 6)) => 75
          | (0, (5, 4)) => 93
          | (0, (5, 5)) => 96
          | (0, (5, 6)) => 95
          | (0, (6, 4)) => 90
          | (0, (6, 5)) => 95
          | (0, (6, 6)) => 96
          | _ => 500
          end,
          returnGen (MkTyp_ctor_Expr_leaf_ctor Ctor_TFun Ctor_leaf_Var)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (0, (4, 4)) => 38
          | (0, (4, 5)) => 66
          | (0, (4, 6)) => 31
          | (0, (5, 4)) => 2
          | (0, (5, 5)) => 1
          | (0, (5, 6)) => 3
          | (0, (6, 4)) => 2
          | (0, (6, 5)) => 1
          | (0, (6, 6)) => 2
          | _ => 500
          end,
          returnGen (MkTyp_ctor_Expr_leaf_ctor Ctor_TBool Ctor_leaf_Bool)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (0, (4, 4)) => 40
          | (0, (4, 5)) => 21
          | (0, (4, 6)) => 31
          | (0, (5, 4)) => 1
          | (0, (5, 5)) => 7
          | (0, (5, 6)) => 2
          | (0, (6, 4)) => 34
          | (0, (6, 5)) => 1
          | (0, (6, 6)) => 1
          | _ => 500
          end,
          returnGen (MkTyp_ctor_Expr_leaf_ctor Ctor_TFun Ctor_leaf_Bool)
        )
      ]) (fun param_variantis =>
      let '(MkTyp_ctor_Expr_leaf_ctor param1_ctor param2_ctor) := param_variantis in
      bindGen (gen_Typ 1 param1_ctor (stack2 : nat) 3)
      (fun p1 : Typ =>
      bindGen (gen_leaf_Expr param2_ctor (stack2 : nat) 4)
      (fun p2 : Expr =>
      returnGen (Abs p1 p2))))
    | Ctor_App =>
      bindGen (freq [
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (0, (4, 4)) => 71
          | (0, (4, 5)) => 81
          | (0, (4, 6)) => 66
          | (0, (5, 4)) => 93
          | (0, (5, 5)) => 97
          | (0, (5, 6)) => 96
          | (0, (6, 4)) => 94
          | (0, (6, 5)) => 93
          | (0, (6, 6)) => 96
          | _ => 500
          end,
          returnGen (MkExpr_leaf_ctor_Expr_leaf_ctor Ctor_leaf_Var Ctor_leaf_Var)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (0, (4, 4)) => 65
          | (0, (4, 5)) => 33
          | (0, (4, 6)) => 44
          | (0, (5, 4)) => 1
          | (0, (5, 5)) => 9
          | (0, (5, 6)) => 59
          | (0, (6, 4)) => 7
          | (0, (6, 5)) => 67
          | (0, (6, 6)) => 4
          | _ => 500
          end,
          returnGen (MkExpr_leaf_ctor_Expr_leaf_ctor Ctor_leaf_Bool Ctor_leaf_Var)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (0, (4, 4)) => 41
          | (0, (4, 5)) => 28
          | (0, (4, 6)) => 61
          | (0, (5, 4)) => 20
          | (0, (5, 5)) => 1
          | (0, (5, 6)) => 3
          | (0, (6, 4)) => 5
          | (0, (6, 5)) => 6
          | (0, (6, 6)) => 3
          | _ => 500
          end,
          returnGen (MkExpr_leaf_ctor_Expr_leaf_ctor Ctor_leaf_Var Ctor_leaf_Bool)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (0, (4, 4)) => 12
          | (0, (4, 5)) => 35
          | (0, (4, 6)) => 31
          | (0, (5, 4)) => 1
          | (0, (5, 5)) => 1
          | (0, (5, 6)) => 6
          | (0, (6, 4)) => 1
          | (0, (6, 5)) => 22
          | (0, (6, 6)) => 0
          | _ => 500
          end,
          returnGen (MkExpr_leaf_ctor_Expr_leaf_ctor Ctor_leaf_Bool Ctor_leaf_Bool)
        )
      ]) (fun param_variantis =>
      let '(MkExpr_leaf_ctor_Expr_leaf_ctor param1_ctor param2_ctor) := param_variantis in
      bindGen (gen_leaf_Expr param1_ctor (stack2 : nat) 5)
      (fun p1 : Expr =>
      bindGen (gen_leaf_Expr param2_ctor (stack2 : nat) 6)
      (fun p2 : Expr =>
      returnGen (App p1 p2))))
  end
  | S size' =>
    match chosen_ctor with
    | Ctor_Var =>
      let weight_1 :=
      match (size, ((stack1 : nat), (stack2 : nat))) with 
      | (1, (4, 4)) => 50
      | (1, (4, 5)) => 44
      | (1, (4, 6)) => 47
      | (1, (5, 4)) => 41
      | (1, (5, 5)) => 3
      | (1, (5, 6)) => 88
      | (1, (6, 4)) => 28
      | (1, (6, 5)) => 57
      | (1, (6, 6)) => 62
      | (2, (4, 4)) => 50
      | (2, (4, 5)) => 23
      | (2, (4, 6)) => 54
      | (2, (5, 4)) => 50
      | (2, (5, 5)) => 50
      | (2, (5, 6)) => 50
      | (2, (6, 4)) => 50
      | (2, (6, 5)) => 50
      | (2, (6, 6)) => 50
      | (3, (0, 4)) => 46
      | (3, (0, 5)) => 50
      | (3, (0, 6)) => 50
      | (4, (0, 0)) => 41
      | _ => 500
      end
      in
      bindGen (freq [
        (weight_1, returnGen 1);
        (100-weight_1, returnGen 0)
      ]) (fun n1 =>
      let weight_2 :=
      match (size, ((stack1 : nat), (stack2 : nat))) with 
      | (1, (4, 4)) => 37
      | (1, (4, 5)) => 48
      | (1, (4, 6)) => 58
      | (1, (5, 4)) => 39
      | (1, (5, 5)) => 26
      | (1, (5, 6)) => 55
      | (1, (6, 4)) => 77
      | (1, (6, 5)) => 47
      | (1, (6, 6)) => 51
      | (2, (4, 4)) => 38
      | (2, (4, 5)) => 16
      | (2, (4, 6)) => 58
      | (2, (5, 4)) => 50
      | (2, (5, 5)) => 50
      | (2, (5, 6)) => 50
      | (2, (6, 4)) => 50
      | (2, (6, 5)) => 50
      | (2, (6, 6)) => 50
      | (3, (0, 4)) => 33
      | (3, (0, 5)) => 50
      | (3, (0, 6)) => 50
      | (4, (0, 0)) => 40
      | _ => 500
      end
      in
      bindGen (freq [
        (weight_2, returnGen 2);
        (100-weight_2, returnGen 0)
      ]) (fun n2 =>
      let weight_4 :=
      match (size, ((stack1 : nat), (stack2 : nat))) with 
      | (1, (4, 4)) => 41
      | (1, (4, 5)) => 47
      | (1, (4, 6)) => 46
      | (1, (5, 4)) => 72
      | (1, (5, 5)) => 26
      | (1, (5, 6)) => 42
      | (1, (6, 4)) => 73
      | (1, (6, 5)) => 90
      | (1, (6, 6)) => 40
      | (2, (4, 4)) => 49
      | (2, (4, 5)) => 70
      | (2, (4, 6)) => 63
      | (2, (5, 4)) => 50
      | (2, (5, 5)) => 50
      | (2, (5, 6)) => 50
      | (2, (6, 4)) => 50
      | (2, (6, 5)) => 50
      | (2, (6, 6)) => 50
      | (3, (0, 4)) => 48
      | (3, (0, 5)) => 50
      | (3, (0, 6)) => 50
      | (4, (0, 0)) => 61
      | _ => 500
      end
      in
      bindGen (freq [
        (weight_4, returnGen 4);
        (100-weight_4, returnGen 0)
      ]) (fun n4 =>
      let weight_8 :=
      match (size, ((stack1 : nat), (stack2 : nat))) with 
      | (1, (4, 4)) => 53
      | (1, (4, 5)) => 48
      | (1, (4, 6)) => 47
      | (1, (5, 4)) => 62
      | (1, (5, 5)) => 13
      | (1, (5, 6)) => 81
      | (1, (6, 4)) => 56
      | (1, (6, 5)) => 82
      | (1, (6, 6)) => 84
      | (2, (4, 4)) => 47
      | (2, (4, 5)) => 68
      | (2, (4, 6)) => 55
      | (2, (5, 4)) => 50
      | (2, (5, 5)) => 50
      | (2, (5, 6)) => 50
      | (2, (6, 4)) => 50
      | (2, (6, 5)) => 50
      | (2, (6, 6)) => 50
      | (3, (0, 4)) => 48
      | (3, (0, 5)) => 50
      | (3, (0, 6)) => 50
      | (4, (0, 0)) => 48
      | _ => 500
      end
      in
      bindGen (freq [
        (weight_8, returnGen 8);
        (100-weight_8, returnGen 0)
      ]) (fun n8 =>
      let weight_16 :=
      match (size, ((stack1 : nat), (stack2 : nat))) with 
      | (1, (4, 4)) => 53
      | (1, (4, 5)) => 52
      | (1, (4, 6)) => 41
      | (1, (5, 4)) => 62
      | (1, (5, 5)) => 11
      | (1, (5, 6)) => 93
      | (1, (6, 4)) => 77
      | (1, (6, 5)) => 45
      | (1, (6, 6)) => 35
      | (2, (4, 4)) => 51
      | (2, (4, 5)) => 53
      | (2, (4, 6)) => 48
      | (2, (5, 4)) => 50
      | (2, (5, 5)) => 50
      | (2, (5, 6)) => 50
      | (2, (6, 4)) => 50
      | (2, (6, 5)) => 50
      | (2, (6, 6)) => 50
      | (3, (0, 4)) => 54
      | (3, (0, 5)) => 50
      | (3, (0, 6)) => 50
      | (4, (0, 0)) => 52
      | _ => 500
      end
      in
      bindGen (freq [
        (weight_16, returnGen 16);
        (100-weight_16, returnGen 0)
      ]) (fun n16 =>
      let weight_32 :=
      match (size, ((stack1 : nat), (stack2 : nat))) with 
      | (1, (4, 4)) => 49
      | (1, (4, 5)) => 43
      | (1, (4, 6)) => 51
      | (1, (5, 4)) => 72
      | (1, (5, 5)) => 80
      | (1, (5, 6)) => 22
      | (1, (6, 4)) => 77
      | (1, (6, 5)) => 48
      | (1, (6, 6)) => 4
      | (2, (4, 4)) => 37
      | (2, (4, 5)) => 25
      | (2, (4, 6)) => 85
      | (2, (5, 4)) => 50
      | (2, (5, 5)) => 50
      | (2, (5, 6)) => 50
      | (2, (6, 4)) => 50
      | (2, (6, 5)) => 50
      | (2, (6, 6)) => 50
      | (3, (0, 4)) => 61
      | (3, (0, 5)) => 50
      | (3, (0, 6)) => 50
      | (4, (0, 0)) => 52
      | _ => 500
      end
      in
      bindGen (freq [
        (weight_32, returnGen 32);
        (100-weight_32, returnGen 0)
      ]) (fun n32 =>
      let p1 := n1 + n2 + n4 + n8 + n16 + n32 in 
      returnGen (Var p1)))))))
    | Ctor_Bool =>
      let weight_true :=
      match (size, ((stack1 : nat), (stack2 : nat))) with 
      | (1, (4, 4)) => 45
      | (1, (4, 5)) => 44
      | (1, (4, 6)) => 41
      | (1, (5, 4)) => 52
      | (1, (5, 5)) => 86
      | (1, (5, 6)) => 11
      | (1, (6, 4)) => 55
      | (1, (6, 5)) => 78
      | (1, (6, 6)) => 80
      | (2, (4, 4)) => 44
      | (2, (4, 5)) => 67
      | (2, (4, 6)) => 47
      | (2, (5, 4)) => 50
      | (2, (5, 5)) => 50
      | (2, (5, 6)) => 50
      | (2, (6, 4)) => 50
      | (2, (6, 5)) => 50
      | (2, (6, 6)) => 50
      | (3, (0, 4)) => 40
      | (3, (0, 5)) => 50
      | (3, (0, 6)) => 50
      | (4, (0, 0)) => 45
      | _ => 500
      end
      in
      bindGen (freq [
        (weight_true, returnGen true);
        (100-weight_true, returnGen false)
      ]) (fun p1 : bool =>
      returnGen (Bool p1))
    | Ctor_Abs =>
      bindGen (freq [
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (4, 4)) => 47
          | (1, (4, 5)) => 46
          | (1, (4, 6)) => 47
          | (1, (5, 4)) => 33
          | (1, (5, 5)) => 42
          | (1, (5, 6)) => 11
          | (1, (6, 4)) => 43
          | (1, (6, 5)) => 1
          | (1, (6, 6)) => 1
          | (2, (4, 4)) => 41
          | (2, (4, 5)) => 3
          | (2, (4, 6)) => 6
          | (2, (5, 4)) => 50
          | (2, (5, 5)) => 50
          | (2, (5, 6)) => 50
          | (2, (6, 4)) => 50
          | (2, (6, 5)) => 50
          | (2, (6, 6)) => 50
          | (3, (0, 4)) => 24
          | (3, (0, 5)) => 50
          | (3, (0, 6)) => 50
          | (4, (0, 0)) => 0
          | _ => 500
          end,
          returnGen (MkTyp_ctor_Expr_ctor Ctor_TBool Ctor_Var)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (4, 4)) => 49
          | (1, (4, 5)) => 51
          | (1, (4, 6)) => 50
          | (1, (5, 4)) => 41
          | (1, (5, 5)) => 71
          | (1, (5, 6)) => 49
          | (1, (6, 4)) => 54
          | (1, (6, 5)) => 83
          | (1, (6, 6)) => 41
          | (2, (4, 4)) => 53
          | (2, (4, 5)) => 4
          | (2, (4, 6)) => 10
          | (2, (5, 4)) => 50
          | (2, (5, 5)) => 50
          | (2, (5, 6)) => 50
          | (2, (6, 4)) => 50
          | (2, (6, 5)) => 50
          | (2, (6, 6)) => 50
          | (3, (0, 4)) => 34
          | (3, (0, 5)) => 50
          | (3, (0, 6)) => 50
          | (4, (0, 0)) => 0
          | _ => 500
          end,
          returnGen (MkTyp_ctor_Expr_ctor Ctor_TFun Ctor_Var)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (4, 4)) => 46
          | (1, (4, 5)) => 49
          | (1, (4, 6)) => 49
          | (1, (5, 4)) => 23
          | (1, (5, 5)) => 2
          | (1, (5, 6)) => 3
          | (1, (6, 4)) => 36
          | (1, (6, 5)) => 2
          | (1, (6, 6)) => 2
          | (2, (4, 4)) => 42
          | (2, (4, 5)) => 6
          | (2, (4, 6)) => 6
          | (2, (5, 4)) => 50
          | (2, (5, 5)) => 50
          | (2, (5, 6)) => 50
          | (2, (6, 4)) => 50
          | (2, (6, 5)) => 50
          | (2, (6, 6)) => 50
          | (3, (0, 4)) => 13
          | (3, (0, 5)) => 50
          | (3, (0, 6)) => 50
          | (4, (0, 0)) => 0
          | _ => 500
          end,
          returnGen (MkTyp_ctor_Expr_ctor Ctor_TBool Ctor_Bool)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (4, 4)) => 49
          | (1, (4, 5)) => 53
          | (1, (4, 6)) => 48
          | (1, (5, 4)) => 26
          | (1, (5, 5)) => 3
          | (1, (5, 6)) => 10
          | (1, (6, 4)) => 21
          | (1, (6, 5)) => 2
          | (1, (6, 6)) => 1
          | (2, (4, 4)) => 40
          | (2, (4, 5)) => 2
          | (2, (4, 6)) => 2
          | (2, (5, 4)) => 50
          | (2, (5, 5)) => 50
          | (2, (5, 6)) => 50
          | (2, (6, 4)) => 50
          | (2, (6, 5)) => 50
          | (2, (6, 6)) => 50
          | (3, (0, 4)) => 20
          | (3, (0, 5)) => 50
          | (3, (0, 6)) => 50
          | (4, (0, 0)) => 0
          | _ => 500
          end,
          returnGen (MkTyp_ctor_Expr_ctor Ctor_TFun Ctor_Bool)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (4, 4)) => 53
          | (1, (4, 5)) => 47
          | (1, (4, 6)) => 49
          | (1, (5, 4)) => 70
          | (1, (5, 5)) => 5
          | (1, (5, 6)) => 9
          | (1, (6, 4)) => 34
          | (1, (6, 5)) => 3
          | (1, (6, 6)) => 16
          | (2, (4, 4)) => 49
          | (2, (4, 5)) => 40
          | (2, (4, 6)) => 39
          | (2, (5, 4)) => 50
          | (2, (5, 5)) => 50
          | (2, (5, 6)) => 50
          | (2, (6, 4)) => 50
          | (2, (6, 5)) => 50
          | (2, (6, 6)) => 50
          | (3, (0, 4)) => 46
          | (3, (0, 5)) => 50
          | (3, (0, 6)) => 50
          | (4, (0, 0)) => 0
          | _ => 500
          end,
          returnGen (MkTyp_ctor_Expr_ctor Ctor_TBool Ctor_Abs)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (4, 4)) => 50
          | (1, (4, 5)) => 48
          | (1, (4, 6)) => 50
          | (1, (5, 4)) => 78
          | (1, (5, 5)) => 42
          | (1, (5, 6)) => 20
          | (1, (6, 4)) => 51
          | (1, (6, 5)) => 84
          | (1, (6, 6)) => 69
          | (2, (4, 4)) => 57
          | (2, (4, 5)) => 52
          | (2, (4, 6)) => 19
          | (2, (5, 4)) => 50
          | (2, (5, 5)) => 50
          | (2, (5, 6)) => 50
          | (2, (6, 4)) => 50
          | (2, (6, 5)) => 50
          | (2, (6, 6)) => 50
          | (3, (0, 4)) => 66
          | (3, (0, 5)) => 50
          | (3, (0, 6)) => 50
          | (4, (0, 0)) => 0
          | _ => 500
          end,
          returnGen (MkTyp_ctor_Expr_ctor Ctor_TFun Ctor_Abs)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (4, 4)) => 51
          | (1, (4, 5)) => 52
          | (1, (4, 6)) => 51
          | (1, (5, 4)) => 44
          | (1, (5, 5)) => 69
          | (1, (5, 6)) => 61
          | (1, (6, 4)) => 71
          | (1, (6, 5)) => 31
          | (1, (6, 6)) => 8
          | (2, (4, 4)) => 56
          | (2, (4, 5)) => 90
          | (2, (4, 6)) => 86
          | (2, (5, 4)) => 50
          | (2, (5, 5)) => 50
          | (2, (5, 6)) => 50
          | (2, (6, 4)) => 50
          | (2, (6, 5)) => 50
          | (2, (6, 6)) => 50
          | (3, (0, 4)) => 77
          | (3, (0, 5)) => 50
          | (3, (0, 6)) => 50
          | (4, (0, 0)) => 18
          | _ => 500
          end,
          returnGen (MkTyp_ctor_Expr_ctor Ctor_TBool Ctor_App)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (4, 4)) => 54
          | (1, (4, 5)) => 55
          | (1, (4, 6)) => 56
          | (1, (5, 4)) => 56
          | (1, (5, 5)) => 95
          | (1, (5, 6)) => 95
          | (1, (6, 4)) => 71
          | (1, (6, 5)) => 94
          | (1, (6, 6)) => 97
          | (2, (4, 4)) => 57
          | (2, (4, 5)) => 89
          | (2, (4, 6)) => 92
          | (2, (5, 4)) => 50
          | (2, (5, 5)) => 50
          | (2, (5, 6)) => 50
          | (2, (6, 4)) => 50
          | (2, (6, 5)) => 50
          | (2, (6, 6)) => 50
          | (3, (0, 4)) => 75
          | (3, (0, 5)) => 50
          | (3, (0, 6)) => 50
          | (4, (0, 0)) => 99
          | _ => 500
          end,
          returnGen (MkTyp_ctor_Expr_ctor Ctor_TFun Ctor_App)
        )
      ]) (fun param_variantis =>
      let '(MkTyp_ctor_Expr_ctor param1_ctor param2_ctor) := param_variantis in
      bindGen (gen_Typ 1 param1_ctor (stack2 : nat) 3)
      (fun p1 : Typ =>
      bindGen (gen_Expr size' param2_ctor (stack2 : nat) 4)
      (fun p2 : Expr =>
      returnGen (Abs p1 p2))))
    | Ctor_App =>
      bindGen (freq [
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (4, 4)) => 51
          | (1, (4, 5)) => 52
          | (1, (4, 6)) => 49
          | (1, (5, 4)) => 51
          | (1, (5, 5)) => 43
          | (1, (5, 6)) => 52
          | (1, (6, 4)) => 34
          | (1, (6, 5)) => 1
          | (1, (6, 6)) => 44
          | (2, (4, 4)) => 48
          | (2, (4, 5)) => 0
          | (2, (4, 6)) => 0
          | (2, (5, 4)) => 50
          | (2, (5, 5)) => 50
          | (2, (5, 6)) => 50
          | (2, (6, 4)) => 50
          | (2, (6, 5)) => 50
          | (2, (6, 6)) => 50
          | (3, (0, 4)) => 0
          | (3, (0, 5)) => 50
          | (3, (0, 6)) => 50
          | (4, (0, 0)) => 50
          | _ => 500
          end,
          returnGen (MkExpr_ctor_Expr_ctor Ctor_Var Ctor_Var)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (4, 4)) => 47
          | (1, (4, 5)) => 47
          | (1, (4, 6)) => 51
          | (1, (5, 4)) => 26
          | (1, (5, 5)) => 0
          | (1, (5, 6)) => 2
          | (1, (6, 4)) => 41
          | (1, (6, 5)) => 4
          | (1, (6, 6)) => 3
          | (2, (4, 4)) => 48
          | (2, (4, 5)) => 0
          | (2, (4, 6)) => 0
          | (2, (5, 4)) => 50
          | (2, (5, 5)) => 50
          | (2, (5, 6)) => 50
          | (2, (6, 4)) => 50
          | (2, (6, 5)) => 50
          | (2, (6, 6)) => 50
          | (3, (0, 4)) => 0
          | (3, (0, 5)) => 50
          | (3, (0, 6)) => 50
          | (4, (0, 0)) => 50
          | _ => 500
          end,
          returnGen (MkExpr_ctor_Expr_ctor Ctor_Bool Ctor_Var)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (4, 4)) => 48
          | (1, (4, 5)) => 51
          | (1, (4, 6)) => 48
          | (1, (5, 4)) => 46
          | (1, (5, 5)) => 54
          | (1, (5, 6)) => 44
          | (1, (6, 4)) => 30
          | (1, (6, 5)) => 72
          | (1, (6, 6)) => 95
          | (2, (4, 4)) => 51
          | (2, (4, 5)) => 0
          | (2, (4, 6)) => 0
          | (2, (5, 4)) => 50
          | (2, (5, 5)) => 50
          | (2, (5, 6)) => 50
          | (2, (6, 4)) => 50
          | (2, (6, 5)) => 50
          | (2, (6, 6)) => 50
          | (3, (0, 4)) => 0
          | (3, (0, 5)) => 50
          | (3, (0, 6)) => 50
          | (4, (0, 0)) => 50
          | _ => 500
          end,
          returnGen (MkExpr_ctor_Expr_ctor Ctor_Abs Ctor_Var)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (4, 4)) => 49
          | (1, (4, 5)) => 49
          | (1, (4, 6)) => 51
          | (1, (5, 4)) => 77
          | (1, (5, 5)) => 89
          | (1, (5, 6)) => 96
          | (1, (6, 4)) => 59
          | (1, (6, 5)) => 78
          | (1, (6, 6)) => 89
          | (2, (4, 4)) => 46
          | (2, (4, 5)) => 0
          | (2, (4, 6)) => 0
          | (2, (5, 4)) => 50
          | (2, (5, 5)) => 50
          | (2, (5, 6)) => 50
          | (2, (6, 4)) => 50
          | (2, (6, 5)) => 50
          | (2, (6, 6)) => 50
          | (3, (0, 4)) => 0
          | (3, (0, 5)) => 50
          | (3, (0, 6)) => 50
          | (4, (0, 0)) => 50
          | _ => 500
          end,
          returnGen (MkExpr_ctor_Expr_ctor Ctor_App Ctor_Var)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (4, 4)) => 48
          | (1, (4, 5)) => 51
          | (1, (4, 6)) => 50
          | (1, (5, 4)) => 16
          | (1, (5, 5)) => 1
          | (1, (5, 6)) => 3
          | (1, (6, 4)) => 35
          | (1, (6, 5)) => 0
          | (1, (6, 6)) => 1
          | (2, (4, 4)) => 41
          | (2, (4, 5)) => 0
          | (2, (4, 6)) => 0
          | (2, (5, 4)) => 50
          | (2, (5, 5)) => 50
          | (2, (5, 6)) => 50
          | (2, (6, 4)) => 50
          | (2, (6, 5)) => 50
          | (2, (6, 6)) => 50
          | (3, (0, 4)) => 0
          | (3, (0, 5)) => 50
          | (3, (0, 6)) => 50
          | (4, (0, 0)) => 50
          | _ => 500
          end,
          returnGen (MkExpr_ctor_Expr_ctor Ctor_Var Ctor_Bool)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (4, 4)) => 48
          | (1, (4, 5)) => 48
          | (1, (4, 6)) => 47
          | (1, (5, 4)) => 17
          | (1, (5, 5)) => 1
          | (1, (5, 6)) => 0
          | (1, (6, 4)) => 25
          | (1, (6, 5)) => 0
          | (1, (6, 6)) => 1
          | (2, (4, 4)) => 39
          | (2, (4, 5)) => 0
          | (2, (4, 6)) => 0
          | (2, (5, 4)) => 50
          | (2, (5, 5)) => 50
          | (2, (5, 6)) => 50
          | (2, (6, 4)) => 50
          | (2, (6, 5)) => 50
          | (2, (6, 6)) => 50
          | (3, (0, 4)) => 0
          | (3, (0, 5)) => 50
          | (3, (0, 6)) => 50
          | (4, (0, 0)) => 50
          | _ => 500
          end,
          returnGen (MkExpr_ctor_Expr_ctor Ctor_Bool Ctor_Bool)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (4, 4)) => 51
          | (1, (4, 5)) => 48
          | (1, (4, 6)) => 49
          | (1, (5, 4)) => 29
          | (1, (5, 5)) => 4
          | (1, (5, 6)) => 1
          | (1, (6, 4)) => 26
          | (1, (6, 5)) => 13
          | (1, (6, 6)) => 1
          | (2, (4, 4)) => 43
          | (2, (4, 5)) => 0
          | (2, (4, 6)) => 0
          | (2, (5, 4)) => 50
          | (2, (5, 5)) => 50
          | (2, (5, 6)) => 50
          | (2, (6, 4)) => 50
          | (2, (6, 5)) => 50
          | (2, (6, 6)) => 50
          | (3, (0, 4)) => 0
          | (3, (0, 5)) => 50
          | (3, (0, 6)) => 50
          | (4, (0, 0)) => 50
          | _ => 500
          end,
          returnGen (MkExpr_ctor_Expr_ctor Ctor_Abs Ctor_Bool)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (4, 4)) => 54
          | (1, (4, 5)) => 51
          | (1, (4, 6)) => 46
          | (1, (5, 4)) => 34
          | (1, (5, 5)) => 2
          | (1, (5, 6)) => 1
          | (1, (6, 4)) => 60
          | (1, (6, 5)) => 0
          | (1, (6, 6)) => 1
          | (2, (4, 4)) => 57
          | (2, (4, 5)) => 0
          | (2, (4, 6)) => 0
          | (2, (5, 4)) => 50
          | (2, (5, 5)) => 50
          | (2, (5, 6)) => 50
          | (2, (6, 4)) => 50
          | (2, (6, 5)) => 50
          | (2, (6, 6)) => 50
          | (3, (0, 4)) => 0
          | (3, (0, 5)) => 50
          | (3, (0, 6)) => 50
          | (4, (0, 0)) => 50
          | _ => 500
          end,
          returnGen (MkExpr_ctor_Expr_ctor Ctor_App Ctor_Bool)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (4, 4)) => 48
          | (1, (4, 5)) => 52
          | (1, (4, 6)) => 52
          | (1, (5, 4)) => 50
          | (1, (5, 5)) => 88
          | (1, (5, 6)) => 10
          | (1, (6, 4)) => 65
          | (1, (6, 5)) => 83
          | (1, (6, 6)) => 64
          | (2, (4, 4)) => 44
          | (2, (4, 5)) => 0
          | (2, (4, 6)) => 0
          | (2, (5, 4)) => 50
          | (2, (5, 5)) => 50
          | (2, (5, 6)) => 50
          | (2, (6, 4)) => 50
          | (2, (6, 5)) => 50
          | (2, (6, 6)) => 50
          | (3, (0, 4)) => 0
          | (3, (0, 5)) => 50
          | (3, (0, 6)) => 50
          | (4, (0, 0)) => 50
          | _ => 500
          end,
          returnGen (MkExpr_ctor_Expr_ctor Ctor_Var Ctor_Abs)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (4, 4)) => 49
          | (1, (4, 5)) => 49
          | (1, (4, 6)) => 47
          | (1, (5, 4)) => 58
          | (1, (5, 5)) => 0
          | (1, (5, 6)) => 2
          | (1, (6, 4)) => 18
          | (1, (6, 5)) => 1
          | (1, (6, 6)) => 0
          | (2, (4, 4)) => 45
          | (2, (4, 5)) => 0
          | (2, (4, 6)) => 0
          | (2, (5, 4)) => 50
          | (2, (5, 5)) => 50
          | (2, (5, 6)) => 50
          | (2, (6, 4)) => 50
          | (2, (6, 5)) => 50
          | (2, (6, 6)) => 50
          | (3, (0, 4)) => 0
          | (3, (0, 5)) => 50
          | (3, (0, 6)) => 50
          | (4, (0, 0)) => 50
          | _ => 500
          end,
          returnGen (MkExpr_ctor_Expr_ctor Ctor_Bool Ctor_Abs)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (4, 4)) => 52
          | (1, (4, 5)) => 52
          | (1, (4, 6)) => 50
          | (1, (5, 4)) => 47
          | (1, (5, 5)) => 86
          | (1, (5, 6)) => 88
          | (1, (6, 4)) => 70
          | (1, (6, 5)) => 52
          | (1, (6, 6)) => 10
          | (2, (4, 4)) => 57
          | (2, (4, 5)) => 0
          | (2, (4, 6)) => 0
          | (2, (5, 4)) => 50
          | (2, (5, 5)) => 50
          | (2, (5, 6)) => 50
          | (2, (6, 4)) => 50
          | (2, (6, 5)) => 50
          | (2, (6, 6)) => 50
          | (3, (0, 4)) => 0
          | (3, (0, 5)) => 50
          | (3, (0, 6)) => 50
          | (4, (0, 0)) => 50
          | _ => 500
          end,
          returnGen (MkExpr_ctor_Expr_ctor Ctor_Abs Ctor_Abs)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (4, 4)) => 53
          | (1, (4, 5)) => 50
          | (1, (4, 6)) => 51
          | (1, (5, 4)) => 79
          | (1, (5, 5)) => 87
          | (1, (5, 6)) => 94
          | (1, (6, 4)) => 76
          | (1, (6, 5)) => 95
          | (1, (6, 6)) => 94
          | (2, (4, 4)) => 50
          | (2, (4, 5)) => 0
          | (2, (4, 6)) => 5
          | (2, (5, 4)) => 50
          | (2, (5, 5)) => 50
          | (2, (5, 6)) => 50
          | (2, (6, 4)) => 50
          | (2, (6, 5)) => 50
          | (2, (6, 6)) => 50
          | (3, (0, 4)) => 0
          | (3, (0, 5)) => 50
          | (3, (0, 6)) => 50
          | (4, (0, 0)) => 50
          | _ => 500
          end,
          returnGen (MkExpr_ctor_Expr_ctor Ctor_App Ctor_Abs)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (4, 4)) => 53
          | (1, (4, 5)) => 50
          | (1, (4, 6)) => 49
          | (1, (5, 4)) => 74
          | (1, (5, 5)) => 93
          | (1, (5, 6)) => 91
          | (1, (6, 4)) => 71
          | (1, (6, 5)) => 12
          | (1, (6, 6)) => 13
          | (2, (4, 4)) => 50
          | (2, (4, 5)) => 0
          | (2, (4, 6)) => 0
          | (2, (5, 4)) => 50
          | (2, (5, 5)) => 50
          | (2, (5, 6)) => 50
          | (2, (6, 4)) => 50
          | (2, (6, 5)) => 50
          | (2, (6, 6)) => 50
          | (3, (0, 4)) => 0
          | (3, (0, 5)) => 50
          | (3, (0, 6)) => 50
          | (4, (0, 0)) => 50
          | _ => 500
          end,
          returnGen (MkExpr_ctor_Expr_ctor Ctor_Var Ctor_App)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (4, 4)) => 49
          | (1, (4, 5)) => 50
          | (1, (4, 6)) => 48
          | (1, (5, 4)) => 15
          | (1, (5, 5)) => 2
          | (1, (5, 6)) => 1
          | (1, (6, 4)) => 22
          | (1, (6, 5)) => 0
          | (1, (6, 6)) => 0
          | (2, (4, 4)) => 58
          | (2, (4, 5)) => 0
          | (2, (4, 6)) => 0
          | (2, (5, 4)) => 50
          | (2, (5, 5)) => 50
          | (2, (5, 6)) => 50
          | (2, (6, 4)) => 50
          | (2, (6, 5)) => 50
          | (2, (6, 6)) => 50
          | (3, (0, 4)) => 0
          | (3, (0, 5)) => 50
          | (3, (0, 6)) => 50
          | (4, (0, 0)) => 50
          | _ => 500
          end,
          returnGen (MkExpr_ctor_Expr_ctor Ctor_Bool Ctor_App)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (4, 4)) => 51
          | (1, (4, 5)) => 54
          | (1, (4, 6)) => 58
          | (1, (5, 4)) => 65
          | (1, (5, 5)) => 92
          | (1, (5, 6)) => 96
          | (1, (6, 4)) => 68
          | (1, (6, 5)) => 98
          | (1, (6, 6)) => 97
          | (2, (4, 4)) => 59
          | (2, (4, 5)) => 0
          | (2, (4, 6)) => 1
          | (2, (5, 4)) => 50
          | (2, (5, 5)) => 50
          | (2, (5, 6)) => 50
          | (2, (6, 4)) => 50
          | (2, (6, 5)) => 50
          | (2, (6, 6)) => 50
          | (3, (0, 4)) => 0
          | (3, (0, 5)) => 50
          | (3, (0, 6)) => 50
          | (4, (0, 0)) => 50
          | _ => 500
          end,
          returnGen (MkExpr_ctor_Expr_ctor Ctor_Abs Ctor_App)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (4, 4)) => 48
          | (1, (4, 5)) => 48
          | (1, (4, 6)) => 53
          | (1, (5, 4)) => 62
          | (1, (5, 5)) => 97
          | (1, (5, 6)) => 85
          | (1, (6, 4)) => 55
          | (1, (6, 5)) => 96
          | (1, (6, 6)) => 95
          | (2, (4, 4)) => 60
          | (2, (4, 5)) => 99
          | (2, (4, 6)) => 99
          | (2, (5, 4)) => 50
          | (2, (5, 5)) => 50
          | (2, (5, 6)) => 50
          | (2, (6, 4)) => 50
          | (2, (6, 5)) => 50
          | (2, (6, 6)) => 50
          | (3, (0, 4)) => 99
          | (3, (0, 5)) => 50
          | (3, (0, 6)) => 50
          | (4, (0, 0)) => 50
          | _ => 500
          end,
          returnGen (MkExpr_ctor_Expr_ctor Ctor_App Ctor_App)
        )
      ]) (fun param_variantis =>
      let '(MkExpr_ctor_Expr_ctor param1_ctor param2_ctor) := param_variantis in
      bindGen (gen_Expr size' param1_ctor (stack2 : nat) 5)
      (fun p1 : Expr =>
      bindGen (gen_Expr size' param2_ctor (stack2 : nat) 6)
      (fun p2 : Expr =>
      returnGen (App p1 p2))))
  end
  end.

Definition gSized :=
  bindGen (freq [
    (
      0,
      returnGen Ctor_Var
    );
    (
      0,
      returnGen Ctor_Bool
    );
    (
      97,
      returnGen Ctor_Abs
    );
    (
      0,
      returnGen Ctor_App
    )
  ]) (fun init_ctor =>
  gen_Expr 4 init_ctor 0 0).

Definition test_prop_SinglePreserve :=
forAll gSized (fun (e: Expr) =>
  prop_SinglePreserve e).

(*! QuickChick test_prop_SinglePreserve. *)

Definition test_prop_MultiPreserve :=
forAll gSized (fun (e: Expr) =>
  prop_MultiPreserve e).

(*! QuickChick test_prop_MultiPreserve. *)
          
