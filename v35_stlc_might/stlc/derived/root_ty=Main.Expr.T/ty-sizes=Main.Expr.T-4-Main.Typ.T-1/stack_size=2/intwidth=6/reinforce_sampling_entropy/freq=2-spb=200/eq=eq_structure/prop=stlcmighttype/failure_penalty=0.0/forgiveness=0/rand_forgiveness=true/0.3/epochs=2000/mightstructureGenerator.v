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
    | (4, 4) => 50
    | (4, 5) => 50
    | (4, 6) => 50
    | (5, 4) => 50
    | (5, 5) => 50
    | (5, 6) => 50
    | (6, 4) => 50
    | (6, 5) => 50
    | (6, 6) => 50
    | _ => 500
    end
    in
    bindGen (freq [
      (weight_1, returnGen 1);
      (100-weight_1, returnGen 0)
    ]) (fun n1 =>
    let weight_2 :=
    match ((stack1 : nat), (stack2 : nat)) with 
    | (4, 4) => 50
    | (4, 5) => 50
    | (4, 6) => 50
    | (5, 4) => 50
    | (5, 5) => 50
    | (5, 6) => 50
    | (6, 4) => 50
    | (6, 5) => 50
    | (6, 6) => 50
    | _ => 500
    end
    in
    bindGen (freq [
      (weight_2, returnGen 2);
      (100-weight_2, returnGen 0)
    ]) (fun n2 =>
    let weight_4 :=
    match ((stack1 : nat), (stack2 : nat)) with 
    | (4, 4) => 50
    | (4, 5) => 50
    | (4, 6) => 50
    | (5, 4) => 50
    | (5, 5) => 50
    | (5, 6) => 50
    | (6, 4) => 50
    | (6, 5) => 50
    | (6, 6) => 50
    | _ => 500
    end
    in
    bindGen (freq [
      (weight_4, returnGen 4);
      (100-weight_4, returnGen 0)
    ]) (fun n4 =>
    let weight_8 :=
    match ((stack1 : nat), (stack2 : nat)) with 
    | (4, 4) => 50
    | (4, 5) => 50
    | (4, 6) => 50
    | (5, 4) => 50
    | (5, 5) => 50
    | (5, 6) => 50
    | (6, 4) => 50
    | (6, 5) => 50
    | (6, 6) => 50
    | _ => 500
    end
    in
    bindGen (freq [
      (weight_8, returnGen 8);
      (100-weight_8, returnGen 0)
    ]) (fun n8 =>
    let weight_16 :=
    match ((stack1 : nat), (stack2 : nat)) with 
    | (4, 4) => 50
    | (4, 5) => 50
    | (4, 6) => 50
    | (5, 4) => 50
    | (5, 5) => 50
    | (5, 6) => 50
    | (6, 4) => 50
    | (6, 5) => 50
    | (6, 6) => 50
    | _ => 500
    end
    in
    bindGen (freq [
      (weight_16, returnGen 16);
      (100-weight_16, returnGen 0)
    ]) (fun n16 =>
    let weight_32 :=
    match ((stack1 : nat), (stack2 : nat)) with 
    | (4, 4) => 50
    | (4, 5) => 50
    | (4, 6) => 50
    | (5, 4) => 50
    | (5, 5) => 50
    | (5, 6) => 50
    | (6, 4) => 50
    | (6, 5) => 50
    | (6, 6) => 50
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
    | (4, 4) => 50
    | (4, 5) => 50
    | (4, 6) => 50
    | (5, 4) => 50
    | (5, 5) => 50
    | (5, 6) => 50
    | (6, 4) => 50
    | (6, 5) => 50
    | (6, 6) => 50
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
          | (1, (0, 3)) => 50
          | (1, (4, 3)) => 50
          | (1, (5, 3)) => 50
          | (1, (6, 3)) => 50
          | _ => 500
          end,
          returnGen (MkTyp_ctor_Typ_ctor Ctor_TBool Ctor_TBool)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (0, 3)) => 50
          | (1, (4, 3)) => 50
          | (1, (5, 3)) => 50
          | (1, (6, 3)) => 50
          | _ => 500
          end,
          returnGen (MkTyp_ctor_Typ_ctor Ctor_TFun Ctor_TBool)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (0, 3)) => 50
          | (1, (4, 3)) => 50
          | (1, (5, 3)) => 50
          | (1, (6, 3)) => 50
          | _ => 500
          end,
          returnGen (MkTyp_ctor_Typ_ctor Ctor_TBool Ctor_TFun)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (0, 3)) => 50
          | (1, (4, 3)) => 50
          | (1, (5, 3)) => 50
          | (1, (6, 3)) => 50
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
      | (0, (4, 4)) => 50
      | (0, (4, 5)) => 50
      | (0, (4, 6)) => 50
      | (0, (5, 4)) => 50
      | (0, (5, 5)) => 50
      | (0, (5, 6)) => 50
      | (0, (6, 4)) => 50
      | (0, (6, 5)) => 50
      | (0, (6, 6)) => 50
      | _ => 500
      end
      in
      bindGen (freq [
        (weight_1, returnGen 1);
        (100-weight_1, returnGen 0)
      ]) (fun n1 =>
      let weight_2 :=
      match (size, ((stack1 : nat), (stack2 : nat))) with 
      | (0, (4, 4)) => 50
      | (0, (4, 5)) => 50
      | (0, (4, 6)) => 50
      | (0, (5, 4)) => 50
      | (0, (5, 5)) => 50
      | (0, (5, 6)) => 50
      | (0, (6, 4)) => 50
      | (0, (6, 5)) => 50
      | (0, (6, 6)) => 50
      | _ => 500
      end
      in
      bindGen (freq [
        (weight_2, returnGen 2);
        (100-weight_2, returnGen 0)
      ]) (fun n2 =>
      let weight_4 :=
      match (size, ((stack1 : nat), (stack2 : nat))) with 
      | (0, (4, 4)) => 50
      | (0, (4, 5)) => 50
      | (0, (4, 6)) => 50
      | (0, (5, 4)) => 50
      | (0, (5, 5)) => 50
      | (0, (5, 6)) => 50
      | (0, (6, 4)) => 50
      | (0, (6, 5)) => 50
      | (0, (6, 6)) => 50
      | _ => 500
      end
      in
      bindGen (freq [
        (weight_4, returnGen 4);
        (100-weight_4, returnGen 0)
      ]) (fun n4 =>
      let weight_8 :=
      match (size, ((stack1 : nat), (stack2 : nat))) with 
      | (0, (4, 4)) => 50
      | (0, (4, 5)) => 50
      | (0, (4, 6)) => 50
      | (0, (5, 4)) => 50
      | (0, (5, 5)) => 50
      | (0, (5, 6)) => 50
      | (0, (6, 4)) => 50
      | (0, (6, 5)) => 50
      | (0, (6, 6)) => 50
      | _ => 500
      end
      in
      bindGen (freq [
        (weight_8, returnGen 8);
        (100-weight_8, returnGen 0)
      ]) (fun n8 =>
      let weight_16 :=
      match (size, ((stack1 : nat), (stack2 : nat))) with 
      | (0, (4, 4)) => 50
      | (0, (4, 5)) => 50
      | (0, (4, 6)) => 50
      | (0, (5, 4)) => 50
      | (0, (5, 5)) => 50
      | (0, (5, 6)) => 50
      | (0, (6, 4)) => 50
      | (0, (6, 5)) => 50
      | (0, (6, 6)) => 50
      | _ => 500
      end
      in
      bindGen (freq [
        (weight_16, returnGen 16);
        (100-weight_16, returnGen 0)
      ]) (fun n16 =>
      let weight_32 :=
      match (size, ((stack1 : nat), (stack2 : nat))) with 
      | (0, (4, 4)) => 50
      | (0, (4, 5)) => 50
      | (0, (4, 6)) => 50
      | (0, (5, 4)) => 50
      | (0, (5, 5)) => 50
      | (0, (5, 6)) => 50
      | (0, (6, 4)) => 50
      | (0, (6, 5)) => 50
      | (0, (6, 6)) => 50
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
      | (0, (4, 4)) => 50
      | (0, (4, 5)) => 50
      | (0, (4, 6)) => 50
      | (0, (5, 4)) => 50
      | (0, (5, 5)) => 50
      | (0, (5, 6)) => 50
      | (0, (6, 4)) => 50
      | (0, (6, 5)) => 50
      | (0, (6, 6)) => 50
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
          | (0, (4, 4)) => 44
          | (0, (4, 5)) => 49
          | (0, (4, 6)) => 54
          | (0, (5, 4)) => 55
          | (0, (5, 5)) => 63
          | (0, (5, 6)) => 52
          | (0, (6, 4)) => 52
          | (0, (6, 5)) => 62
          | (0, (6, 6)) => 49
          | _ => 500
          end,
          returnGen (MkTyp_ctor_Expr_leaf_ctor Ctor_TBool Ctor_leaf_Var)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (0, (4, 4)) => 44
          | (0, (4, 5)) => 49
          | (0, (4, 6)) => 54
          | (0, (5, 4)) => 55
          | (0, (5, 5)) => 63
          | (0, (5, 6)) => 52
          | (0, (6, 4)) => 52
          | (0, (6, 5)) => 62
          | (0, (6, 6)) => 49
          | _ => 500
          end,
          returnGen (MkTyp_ctor_Expr_leaf_ctor Ctor_TFun Ctor_leaf_Var)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (0, (4, 4)) => 56
          | (0, (4, 5)) => 51
          | (0, (4, 6)) => 47
          | (0, (5, 4)) => 48
          | (0, (5, 5)) => 49
          | (0, (5, 6)) => 61
          | (0, (6, 4)) => 51
          | (0, (6, 5)) => 49
          | (0, (6, 6)) => 63
          | _ => 500
          end,
          returnGen (MkTyp_ctor_Expr_leaf_ctor Ctor_TBool Ctor_leaf_Bool)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (0, (4, 4)) => 56
          | (0, (4, 5)) => 51
          | (0, (4, 6)) => 47
          | (0, (5, 4)) => 48
          | (0, (5, 5)) => 49
          | (0, (5, 6)) => 61
          | (0, (6, 4)) => 51
          | (0, (6, 5)) => 49
          | (0, (6, 6)) => 63
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
          | (0, (4, 4)) => 42
          | (0, (4, 5)) => 47
          | (0, (4, 6)) => 49
          | (0, (5, 4)) => 37
          | (0, (5, 5)) => 76
          | (0, (5, 6)) => 69
          | (0, (6, 4)) => 77
          | (0, (6, 5)) => 67
          | (0, (6, 6)) => 70
          | _ => 500
          end,
          returnGen (MkExpr_leaf_ctor_Expr_leaf_ctor Ctor_leaf_Var Ctor_leaf_Var)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (0, (4, 4)) => 47
          | (0, (4, 5)) => 49
          | (0, (4, 6)) => 71
          | (0, (5, 4)) => 76
          | (0, (5, 5)) => 83
          | (0, (5, 6)) => 55
          | (0, (6, 4)) => 38
          | (0, (6, 5)) => 47
          | (0, (6, 6)) => 76
          | _ => 500
          end,
          returnGen (MkExpr_leaf_ctor_Expr_leaf_ctor Ctor_leaf_Bool Ctor_leaf_Var)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (0, (4, 4)) => 49
          | (0, (4, 5)) => 52
          | (0, (4, 6)) => 47
          | (0, (5, 4)) => 66
          | (0, (5, 5)) => 67
          | (0, (5, 6)) => 55
          | (0, (6, 4)) => 55
          | (0, (6, 5)) => 74
          | (0, (6, 6)) => 72
          | _ => 500
          end,
          returnGen (MkExpr_leaf_ctor_Expr_leaf_ctor Ctor_leaf_Var Ctor_leaf_Bool)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (0, (4, 4)) => 61
          | (0, (4, 5)) => 56
          | (0, (4, 6)) => 25
          | (0, (5, 4)) => 26
          | (0, (5, 5)) => 33
          | (0, (5, 6)) => 84
          | (0, (6, 4)) => 37
          | (0, (6, 5)) => 82
          | (0, (6, 6)) => 64
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
      | (1, (4, 5)) => 50
      | (1, (4, 6)) => 50
      | (1, (5, 4)) => 50
      | (1, (5, 5)) => 50
      | (1, (5, 6)) => 50
      | (1, (6, 4)) => 50
      | (1, (6, 5)) => 50
      | (1, (6, 6)) => 50
      | (2, (4, 4)) => 50
      | (2, (4, 5)) => 50
      | (2, (4, 6)) => 50
      | (2, (5, 4)) => 50
      | (2, (5, 5)) => 50
      | (2, (5, 6)) => 50
      | (2, (6, 4)) => 50
      | (2, (6, 5)) => 50
      | (2, (6, 6)) => 50
      | (3, (0, 4)) => 50
      | (3, (0, 5)) => 50
      | (3, (0, 6)) => 50
      | (4, (0, 0)) => 50
      | _ => 500
      end
      in
      bindGen (freq [
        (weight_1, returnGen 1);
        (100-weight_1, returnGen 0)
      ]) (fun n1 =>
      let weight_2 :=
      match (size, ((stack1 : nat), (stack2 : nat))) with 
      | (1, (4, 4)) => 50
      | (1, (4, 5)) => 50
      | (1, (4, 6)) => 50
      | (1, (5, 4)) => 50
      | (1, (5, 5)) => 50
      | (1, (5, 6)) => 50
      | (1, (6, 4)) => 50
      | (1, (6, 5)) => 50
      | (1, (6, 6)) => 50
      | (2, (4, 4)) => 50
      | (2, (4, 5)) => 50
      | (2, (4, 6)) => 50
      | (2, (5, 4)) => 50
      | (2, (5, 5)) => 50
      | (2, (5, 6)) => 50
      | (2, (6, 4)) => 50
      | (2, (6, 5)) => 50
      | (2, (6, 6)) => 50
      | (3, (0, 4)) => 50
      | (3, (0, 5)) => 50
      | (3, (0, 6)) => 50
      | (4, (0, 0)) => 50
      | _ => 500
      end
      in
      bindGen (freq [
        (weight_2, returnGen 2);
        (100-weight_2, returnGen 0)
      ]) (fun n2 =>
      let weight_4 :=
      match (size, ((stack1 : nat), (stack2 : nat))) with 
      | (1, (4, 4)) => 50
      | (1, (4, 5)) => 50
      | (1, (4, 6)) => 50
      | (1, (5, 4)) => 50
      | (1, (5, 5)) => 50
      | (1, (5, 6)) => 50
      | (1, (6, 4)) => 50
      | (1, (6, 5)) => 50
      | (1, (6, 6)) => 50
      | (2, (4, 4)) => 50
      | (2, (4, 5)) => 50
      | (2, (4, 6)) => 50
      | (2, (5, 4)) => 50
      | (2, (5, 5)) => 50
      | (2, (5, 6)) => 50
      | (2, (6, 4)) => 50
      | (2, (6, 5)) => 50
      | (2, (6, 6)) => 50
      | (3, (0, 4)) => 50
      | (3, (0, 5)) => 50
      | (3, (0, 6)) => 50
      | (4, (0, 0)) => 50
      | _ => 500
      end
      in
      bindGen (freq [
        (weight_4, returnGen 4);
        (100-weight_4, returnGen 0)
      ]) (fun n4 =>
      let weight_8 :=
      match (size, ((stack1 : nat), (stack2 : nat))) with 
      | (1, (4, 4)) => 50
      | (1, (4, 5)) => 50
      | (1, (4, 6)) => 50
      | (1, (5, 4)) => 50
      | (1, (5, 5)) => 50
      | (1, (5, 6)) => 50
      | (1, (6, 4)) => 50
      | (1, (6, 5)) => 50
      | (1, (6, 6)) => 50
      | (2, (4, 4)) => 50
      | (2, (4, 5)) => 50
      | (2, (4, 6)) => 50
      | (2, (5, 4)) => 50
      | (2, (5, 5)) => 50
      | (2, (5, 6)) => 50
      | (2, (6, 4)) => 50
      | (2, (6, 5)) => 50
      | (2, (6, 6)) => 50
      | (3, (0, 4)) => 50
      | (3, (0, 5)) => 50
      | (3, (0, 6)) => 50
      | (4, (0, 0)) => 50
      | _ => 500
      end
      in
      bindGen (freq [
        (weight_8, returnGen 8);
        (100-weight_8, returnGen 0)
      ]) (fun n8 =>
      let weight_16 :=
      match (size, ((stack1 : nat), (stack2 : nat))) with 
      | (1, (4, 4)) => 50
      | (1, (4, 5)) => 50
      | (1, (4, 6)) => 50
      | (1, (5, 4)) => 50
      | (1, (5, 5)) => 50
      | (1, (5, 6)) => 50
      | (1, (6, 4)) => 50
      | (1, (6, 5)) => 50
      | (1, (6, 6)) => 50
      | (2, (4, 4)) => 50
      | (2, (4, 5)) => 50
      | (2, (4, 6)) => 50
      | (2, (5, 4)) => 50
      | (2, (5, 5)) => 50
      | (2, (5, 6)) => 50
      | (2, (6, 4)) => 50
      | (2, (6, 5)) => 50
      | (2, (6, 6)) => 50
      | (3, (0, 4)) => 50
      | (3, (0, 5)) => 50
      | (3, (0, 6)) => 50
      | (4, (0, 0)) => 50
      | _ => 500
      end
      in
      bindGen (freq [
        (weight_16, returnGen 16);
        (100-weight_16, returnGen 0)
      ]) (fun n16 =>
      let weight_32 :=
      match (size, ((stack1 : nat), (stack2 : nat))) with 
      | (1, (4, 4)) => 50
      | (1, (4, 5)) => 50
      | (1, (4, 6)) => 50
      | (1, (5, 4)) => 50
      | (1, (5, 5)) => 50
      | (1, (5, 6)) => 50
      | (1, (6, 4)) => 50
      | (1, (6, 5)) => 50
      | (1, (6, 6)) => 50
      | (2, (4, 4)) => 50
      | (2, (4, 5)) => 50
      | (2, (4, 6)) => 50
      | (2, (5, 4)) => 50
      | (2, (5, 5)) => 50
      | (2, (5, 6)) => 50
      | (2, (6, 4)) => 50
      | (2, (6, 5)) => 50
      | (2, (6, 6)) => 50
      | (3, (0, 4)) => 50
      | (3, (0, 5)) => 50
      | (3, (0, 6)) => 50
      | (4, (0, 0)) => 50
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
      | (1, (4, 4)) => 50
      | (1, (4, 5)) => 50
      | (1, (4, 6)) => 50
      | (1, (5, 4)) => 50
      | (1, (5, 5)) => 50
      | (1, (5, 6)) => 50
      | (1, (6, 4)) => 50
      | (1, (6, 5)) => 50
      | (1, (6, 6)) => 50
      | (2, (4, 4)) => 50
      | (2, (4, 5)) => 50
      | (2, (4, 6)) => 50
      | (2, (5, 4)) => 50
      | (2, (5, 5)) => 50
      | (2, (5, 6)) => 50
      | (2, (6, 4)) => 50
      | (2, (6, 5)) => 50
      | (2, (6, 6)) => 50
      | (3, (0, 4)) => 50
      | (3, (0, 5)) => 50
      | (3, (0, 6)) => 50
      | (4, (0, 0)) => 50
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
          | (1, (4, 4)) => 49
          | (1, (4, 5)) => 49
          | (1, (4, 6)) => 49
          | (1, (5, 4)) => 39
          | (1, (5, 5)) => 27
          | (1, (5, 6)) => 21
          | (1, (6, 4)) => 46
          | (1, (6, 5)) => 17
          | (1, (6, 6)) => 14
          | (2, (4, 4)) => 44
          | (2, (4, 5)) => 6
          | (2, (4, 6)) => 6
          | (2, (5, 4)) => 50
          | (2, (5, 5)) => 50
          | (2, (5, 6)) => 50
          | (2, (6, 4)) => 50
          | (2, (6, 5)) => 50
          | (2, (6, 6)) => 50
          | (3, (0, 4)) => 23
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
          | (1, (4, 5)) => 49
          | (1, (4, 6)) => 49
          | (1, (5, 4)) => 39
          | (1, (5, 5)) => 27
          | (1, (5, 6)) => 21
          | (1, (6, 4)) => 46
          | (1, (6, 5)) => 17
          | (1, (6, 6)) => 14
          | (2, (4, 4)) => 44
          | (2, (4, 5)) => 6
          | (2, (4, 6)) => 6
          | (2, (5, 4)) => 50
          | (2, (5, 5)) => 50
          | (2, (5, 6)) => 50
          | (2, (6, 4)) => 50
          | (2, (6, 5)) => 50
          | (2, (6, 6)) => 50
          | (3, (0, 4)) => 23
          | (3, (0, 5)) => 50
          | (3, (0, 6)) => 50
          | (4, (0, 0)) => 0
          | _ => 500
          end,
          returnGen (MkTyp_ctor_Expr_ctor Ctor_TFun Ctor_Var)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (4, 4)) => 49
          | (1, (4, 5)) => 51
          | (1, (4, 6)) => 52
          | (1, (5, 4)) => 39
          | (1, (5, 5)) => 19
          | (1, (5, 6)) => 21
          | (1, (6, 4)) => 45
          | (1, (6, 5)) => 34
          | (1, (6, 6)) => 20
          | (2, (4, 4)) => 46
          | (2, (4, 5)) => 7
          | (2, (4, 6)) => 8
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
          returnGen (MkTyp_ctor_Expr_ctor Ctor_TBool Ctor_Bool)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (4, 4)) => 49
          | (1, (4, 5)) => 51
          | (1, (4, 6)) => 52
          | (1, (5, 4)) => 39
          | (1, (5, 5)) => 19
          | (1, (5, 6)) => 21
          | (1, (6, 4)) => 45
          | (1, (6, 5)) => 34
          | (1, (6, 6)) => 20
          | (2, (4, 4)) => 46
          | (2, (4, 5)) => 7
          | (2, (4, 6)) => 8
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
          returnGen (MkTyp_ctor_Expr_ctor Ctor_TFun Ctor_Bool)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (4, 4)) => 50
          | (1, (4, 5)) => 51
          | (1, (4, 6)) => 50
          | (1, (5, 4)) => 62
          | (1, (5, 5)) => 49
          | (1, (5, 6)) => 47
          | (1, (6, 4)) => 51
          | (1, (6, 5)) => 42
          | (1, (6, 6)) => 54
          | (2, (4, 4)) => 51
          | (2, (4, 5)) => 27
          | (2, (4, 6)) => 33
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
          | (1, (4, 5)) => 51
          | (1, (4, 6)) => 50
          | (1, (5, 4)) => 62
          | (1, (5, 5)) => 49
          | (1, (5, 6)) => 47
          | (1, (6, 4)) => 51
          | (1, (6, 5)) => 42
          | (1, (6, 6)) => 54
          | (2, (4, 4)) => 51
          | (2, (4, 5)) => 27
          | (2, (4, 6)) => 33
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
          returnGen (MkTyp_ctor_Expr_ctor Ctor_TFun Ctor_Abs)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (4, 4)) => 52
          | (1, (4, 5)) => 49
          | (1, (4, 6)) => 49
          | (1, (5, 4)) => 56
          | (1, (5, 5)) => 81
          | (1, (5, 6)) => 81
          | (1, (6, 4)) => 57
          | (1, (6, 5)) => 81
          | (1, (6, 6)) => 82
          | (2, (4, 4)) => 58
          | (2, (4, 5)) => 89
          | (2, (4, 6)) => 88
          | (2, (5, 4)) => 50
          | (2, (5, 5)) => 50
          | (2, (5, 6)) => 50
          | (2, (6, 4)) => 50
          | (2, (6, 5)) => 50
          | (2, (6, 6)) => 50
          | (3, (0, 4)) => 79
          | (3, (0, 5)) => 50
          | (3, (0, 6)) => 50
          | (4, (0, 0)) => 96
          | _ => 500
          end,
          returnGen (MkTyp_ctor_Expr_ctor Ctor_TBool Ctor_App)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (4, 4)) => 52
          | (1, (4, 5)) => 49
          | (1, (4, 6)) => 49
          | (1, (5, 4)) => 56
          | (1, (5, 5)) => 81
          | (1, (5, 6)) => 81
          | (1, (6, 4)) => 57
          | (1, (6, 5)) => 81
          | (1, (6, 6)) => 82
          | (2, (4, 4)) => 58
          | (2, (4, 5)) => 89
          | (2, (4, 6)) => 88
          | (2, (5, 4)) => 50
          | (2, (5, 5)) => 50
          | (2, (5, 6)) => 50
          | (2, (6, 4)) => 50
          | (2, (6, 5)) => 50
          | (2, (6, 6)) => 50
          | (3, (0, 4)) => 79
          | (3, (0, 5)) => 50
          | (3, (0, 6)) => 50
          | (4, (0, 0)) => 96
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
          | (1, (4, 4)) => 49
          | (1, (4, 5)) => 49
          | (1, (4, 6)) => 48
          | (1, (5, 4)) => 32
          | (1, (5, 5)) => 6
          | (1, (5, 6)) => 10
          | (1, (6, 4)) => 34
          | (1, (6, 5)) => 11
          | (1, (6, 6)) => 6
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
          returnGen (MkExpr_ctor_Expr_ctor Ctor_Var Ctor_Var)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (4, 4)) => 49
          | (1, (4, 5)) => 48
          | (1, (4, 6)) => 51
          | (1, (5, 4)) => 41
          | (1, (5, 5)) => 3
          | (1, (5, 6)) => 10
          | (1, (6, 4)) => 20
          | (1, (6, 5)) => 5
          | (1, (6, 6)) => 15
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
          returnGen (MkExpr_ctor_Expr_ctor Ctor_Bool Ctor_Var)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (4, 4)) => 50
          | (1, (4, 5)) => 50
          | (1, (4, 6)) => 49
          | (1, (5, 4)) => 46
          | (1, (5, 5)) => 21
          | (1, (5, 6)) => 17
          | (1, (6, 4)) => 55
          | (1, (6, 5)) => 27
          | (1, (6, 6)) => 21
          | (2, (4, 4)) => 49
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
          | (1, (4, 4)) => 50
          | (1, (4, 5)) => 52
          | (1, (4, 6)) => 50
          | (1, (5, 4)) => 52
          | (1, (5, 5)) => 44
          | (1, (5, 6)) => 58
          | (1, (6, 4)) => 58
          | (1, (6, 5)) => 10
          | (1, (6, 6)) => 37
          | (2, (4, 4)) => 55
          | (2, (4, 5)) => 0
          | (2, (4, 6)) => 2
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
          | (1, (4, 5)) => 49
          | (1, (4, 6)) => 50
          | (1, (5, 4)) => 34
          | (1, (5, 5)) => 9
          | (1, (5, 6)) => 5
          | (1, (6, 4)) => 31
          | (1, (6, 5)) => 6
          | (1, (6, 6)) => 9
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
          | (1, (4, 4)) => 51
          | (1, (4, 5)) => 50
          | (1, (4, 6)) => 51
          | (1, (5, 4)) => 41
          | (1, (5, 5)) => 8
          | (1, (5, 6)) => 4
          | (1, (6, 4)) => 40
          | (1, (6, 5)) => 12
          | (1, (6, 6)) => 7
          | (2, (4, 4)) => 42
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
          | (1, (4, 4)) => 49
          | (1, (4, 5)) => 49
          | (1, (4, 6)) => 51
          | (1, (5, 4)) => 41
          | (1, (5, 5)) => 27
          | (1, (5, 6)) => 3
          | (1, (6, 4)) => 34
          | (1, (6, 5)) => 21
          | (1, (6, 6)) => 7
          | (2, (4, 4)) => 47
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
          | (1, (4, 4)) => 50
          | (1, (4, 5)) => 49
          | (1, (4, 6)) => 52
          | (1, (5, 4)) => 58
          | (1, (5, 5)) => 42
          | (1, (5, 6)) => 16
          | (1, (6, 4)) => 66
          | (1, (6, 5)) => 40
          | (1, (6, 6)) => 66
          | (2, (4, 4)) => 51
          | (2, (4, 5)) => 1
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
          returnGen (MkExpr_ctor_Expr_ctor Ctor_App Ctor_Bool)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (4, 4)) => 49
          | (1, (4, 5)) => 49
          | (1, (4, 6)) => 51
          | (1, (5, 4)) => 36
          | (1, (5, 5)) => 29
          | (1, (5, 6)) => 19
          | (1, (6, 4)) => 58
          | (1, (6, 5)) => 13
          | (1, (6, 6)) => 35
          | (2, (4, 4)) => 49
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
          | (1, (4, 4)) => 51
          | (1, (4, 5)) => 50
          | (1, (4, 6)) => 50
          | (1, (5, 4)) => 54
          | (1, (5, 5)) => 27
          | (1, (5, 6)) => 19
          | (1, (6, 4)) => 26
          | (1, (6, 5)) => 31
          | (1, (6, 6)) => 13
          | (2, (4, 4)) => 49
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
          returnGen (MkExpr_ctor_Expr_ctor Ctor_Bool Ctor_Abs)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (4, 4)) => 50
          | (1, (4, 5)) => 51
          | (1, (4, 6)) => 50
          | (1, (5, 4)) => 58
          | (1, (5, 5)) => 17
          | (1, (5, 6)) => 28
          | (1, (6, 4)) => 55
          | (1, (6, 5)) => 19
          | (1, (6, 6)) => 15
          | (2, (4, 4)) => 53
          | (2, (4, 5)) => 2
          | (2, (4, 6)) => 2
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
          | (1, (4, 4)) => 49
          | (1, (4, 5)) => 50
          | (1, (4, 6)) => 47
          | (1, (5, 4)) => 69
          | (1, (5, 5)) => 83
          | (1, (5, 6)) => 70
          | (1, (6, 4)) => 67
          | (1, (6, 5)) => 69
          | (1, (6, 6)) => 76
          | (2, (4, 4)) => 56
          | (2, (4, 5)) => 9
          | (2, (4, 6)) => 10
          | (2, (5, 4)) => 50
          | (2, (5, 5)) => 50
          | (2, (5, 6)) => 50
          | (2, (6, 4)) => 50
          | (2, (6, 5)) => 50
          | (2, (6, 6)) => 50
          | (3, (0, 4)) => 1
          | (3, (0, 5)) => 50
          | (3, (0, 6)) => 50
          | (4, (0, 0)) => 50
          | _ => 500
          end,
          returnGen (MkExpr_ctor_Expr_ctor Ctor_App Ctor_Abs)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (4, 4)) => 52
          | (1, (4, 5)) => 52
          | (1, (4, 6)) => 49
          | (1, (5, 4)) => 51
          | (1, (5, 5)) => 43
          | (1, (5, 6)) => 21
          | (1, (6, 4)) => 50
          | (1, (6, 5)) => 60
          | (1, (6, 6)) => 46
          | (2, (4, 4)) => 52
          | (2, (4, 5)) => 1
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
          returnGen (MkExpr_ctor_Expr_ctor Ctor_Var Ctor_App)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (4, 4)) => 51
          | (1, (4, 5)) => 51
          | (1, (4, 6)) => 45
          | (1, (5, 4)) => 43
          | (1, (5, 5)) => 23
          | (1, (5, 6)) => 55
          | (1, (6, 4)) => 53
          | (1, (6, 5)) => 8
          | (1, (6, 6)) => 43
          | (2, (4, 4)) => 50
          | (2, (4, 5)) => 2
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
          returnGen (MkExpr_ctor_Expr_ctor Ctor_Bool Ctor_App)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (4, 4)) => 51
          | (1, (4, 5)) => 51
          | (1, (4, 6)) => 49
          | (1, (5, 4)) => 61
          | (1, (5, 5)) => 74
          | (1, (5, 6)) => 37
          | (1, (6, 4)) => 50
          | (1, (6, 5)) => 69
          | (1, (6, 6)) => 50
          | (2, (4, 4)) => 59
          | (2, (4, 5)) => 13
          | (2, (4, 6)) => 8
          | (2, (5, 4)) => 50
          | (2, (5, 5)) => 50
          | (2, (5, 6)) => 50
          | (2, (6, 4)) => 50
          | (2, (6, 5)) => 50
          | (2, (6, 6)) => 50
          | (3, (0, 4)) => 1
          | (3, (0, 5)) => 50
          | (3, (0, 6)) => 50
          | (4, (0, 0)) => 50
          | _ => 500
          end,
          returnGen (MkExpr_ctor_Expr_ctor Ctor_Abs Ctor_App)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (4, 4)) => 51
          | (1, (4, 5)) => 51
          | (1, (4, 6)) => 55
          | (1, (5, 4)) => 68
          | (1, (5, 5)) => 97
          | (1, (5, 6)) => 97
          | (1, (6, 4)) => 75
          | (1, (6, 5)) => 97
          | (1, (6, 6)) => 97
          | (2, (4, 4)) => 56
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
      96,
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
          
