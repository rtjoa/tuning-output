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
          end,
          returnGen (MkTyp_ctor_Expr_leaf_ctor Ctor_TBool Ctor_leaf_Var)
        );
        (
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
          end,
          returnGen (MkTyp_ctor_Expr_leaf_ctor Ctor_TFun Ctor_leaf_Var)
        );
        (
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
          end,
          returnGen (MkTyp_ctor_Expr_leaf_ctor Ctor_TBool Ctor_leaf_Bool)
        );
        (
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
          end,
          returnGen (MkExpr_leaf_ctor_Expr_leaf_ctor Ctor_leaf_Var Ctor_leaf_Var)
        );
        (
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
          end,
          returnGen (MkExpr_leaf_ctor_Expr_leaf_ctor Ctor_leaf_Bool Ctor_leaf_Var)
        );
        (
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
          end,
          returnGen (MkExpr_leaf_ctor_Expr_leaf_ctor Ctor_leaf_Var Ctor_leaf_Bool)
        );
        (
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
          | (1, (4, 5)) => 36
          | (1, (4, 6)) => 36
          | (1, (5, 4)) => 49
          | (1, (5, 5)) => 30
          | (1, (5, 6)) => 30
          | (1, (6, 4)) => 49
          | (1, (6, 5)) => 30
          | (1, (6, 6)) => 30
          | (2, (4, 4)) => 50
          | (2, (4, 5)) => 50
          | (2, (4, 6)) => 50
          | (2, (5, 4)) => 44
          | (2, (5, 5)) => 14
          | (2, (5, 6)) => 14
          | (2, (6, 4)) => 44
          | (2, (6, 5)) => 14
          | (2, (6, 6)) => 14
          | (3, (0, 4)) => 49
          | (3, (0, 5)) => 3
          | (3, (0, 6)) => 3
          | (4, (0, 0)) => 45
          | _ => 500
          end,
          returnGen (MkTyp_ctor_Expr_ctor Ctor_TBool Ctor_Var)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (4, 4)) => 49
          | (1, (4, 5)) => 36
          | (1, (4, 6)) => 36
          | (1, (5, 4)) => 49
          | (1, (5, 5)) => 30
          | (1, (5, 6)) => 30
          | (1, (6, 4)) => 49
          | (1, (6, 5)) => 30
          | (1, (6, 6)) => 30
          | (2, (4, 4)) => 50
          | (2, (4, 5)) => 50
          | (2, (4, 6)) => 50
          | (2, (5, 4)) => 44
          | (2, (5, 5)) => 14
          | (2, (5, 6)) => 14
          | (2, (6, 4)) => 44
          | (2, (6, 5)) => 14
          | (2, (6, 6)) => 14
          | (3, (0, 4)) => 49
          | (3, (0, 5)) => 3
          | (3, (0, 6)) => 3
          | (4, (0, 0)) => 45
          | _ => 500
          end,
          returnGen (MkTyp_ctor_Expr_ctor Ctor_TFun Ctor_Var)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (4, 4)) => 49
          | (1, (4, 5)) => 36
          | (1, (4, 6)) => 36
          | (1, (5, 4)) => 49
          | (1, (5, 5)) => 30
          | (1, (5, 6)) => 30
          | (1, (6, 4)) => 49
          | (1, (6, 5)) => 30
          | (1, (6, 6)) => 30
          | (2, (4, 4)) => 50
          | (2, (4, 5)) => 50
          | (2, (4, 6)) => 50
          | (2, (5, 4)) => 44
          | (2, (5, 5)) => 14
          | (2, (5, 6)) => 14
          | (2, (6, 4)) => 44
          | (2, (6, 5)) => 14
          | (2, (6, 6)) => 14
          | (3, (0, 4)) => 49
          | (3, (0, 5)) => 3
          | (3, (0, 6)) => 3
          | (4, (0, 0)) => 45
          | _ => 500
          end,
          returnGen (MkTyp_ctor_Expr_ctor Ctor_TBool Ctor_Bool)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (4, 4)) => 49
          | (1, (4, 5)) => 36
          | (1, (4, 6)) => 36
          | (1, (5, 4)) => 49
          | (1, (5, 5)) => 30
          | (1, (5, 6)) => 30
          | (1, (6, 4)) => 49
          | (1, (6, 5)) => 30
          | (1, (6, 6)) => 30
          | (2, (4, 4)) => 50
          | (2, (4, 5)) => 50
          | (2, (4, 6)) => 50
          | (2, (5, 4)) => 44
          | (2, (5, 5)) => 14
          | (2, (5, 6)) => 14
          | (2, (6, 4)) => 44
          | (2, (6, 5)) => 14
          | (2, (6, 6)) => 14
          | (3, (0, 4)) => 49
          | (3, (0, 5)) => 3
          | (3, (0, 6)) => 3
          | (4, (0, 0)) => 45
          | _ => 500
          end,
          returnGen (MkTyp_ctor_Expr_ctor Ctor_TFun Ctor_Bool)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (4, 4)) => 49
          | (1, (4, 5)) => 36
          | (1, (4, 6)) => 36
          | (1, (5, 4)) => 49
          | (1, (5, 5)) => 30
          | (1, (5, 6)) => 30
          | (1, (6, 4)) => 49
          | (1, (6, 5)) => 30
          | (1, (6, 6)) => 30
          | (2, (4, 4)) => 50
          | (2, (4, 5)) => 50
          | (2, (4, 6)) => 50
          | (2, (5, 4)) => 47
          | (2, (5, 5)) => 13
          | (2, (5, 6)) => 13
          | (2, (6, 4)) => 47
          | (2, (6, 5)) => 13
          | (2, (6, 6)) => 13
          | (3, (0, 4)) => 50
          | (3, (0, 5)) => 4
          | (3, (0, 6)) => 4
          | (4, (0, 0)) => 47
          | _ => 500
          end,
          returnGen (MkTyp_ctor_Expr_ctor Ctor_TBool Ctor_Abs)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (4, 4)) => 49
          | (1, (4, 5)) => 36
          | (1, (4, 6)) => 36
          | (1, (5, 4)) => 49
          | (1, (5, 5)) => 30
          | (1, (5, 6)) => 30
          | (1, (6, 4)) => 49
          | (1, (6, 5)) => 30
          | (1, (6, 6)) => 30
          | (2, (4, 4)) => 50
          | (2, (4, 5)) => 50
          | (2, (4, 6)) => 50
          | (2, (5, 4)) => 47
          | (2, (5, 5)) => 13
          | (2, (5, 6)) => 13
          | (2, (6, 4)) => 47
          | (2, (6, 5)) => 13
          | (2, (6, 6)) => 13
          | (3, (0, 4)) => 50
          | (3, (0, 5)) => 4
          | (3, (0, 6)) => 4
          | (4, (0, 0)) => 47
          | _ => 500
          end,
          returnGen (MkTyp_ctor_Expr_ctor Ctor_TFun Ctor_Abs)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (4, 4)) => 54
          | (1, (4, 5)) => 75
          | (1, (4, 6)) => 75
          | (1, (5, 4)) => 55
          | (1, (5, 5)) => 92
          | (1, (5, 6)) => 92
          | (1, (6, 4)) => 55
          | (1, (6, 5)) => 92
          | (1, (6, 6)) => 92
          | (2, (4, 4)) => 50
          | (2, (4, 5)) => 51
          | (2, (4, 6)) => 51
          | (2, (5, 4)) => 63
          | (2, (5, 5)) => 91
          | (2, (5, 6)) => 91
          | (2, (6, 4)) => 63
          | (2, (6, 5)) => 91
          | (2, (6, 6)) => 91
          | (3, (0, 4)) => 51
          | (3, (0, 5)) => 94
          | (3, (0, 6)) => 94
          | (4, (0, 0)) => 62
          | _ => 500
          end,
          returnGen (MkTyp_ctor_Expr_ctor Ctor_TBool Ctor_App)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (4, 4)) => 54
          | (1, (4, 5)) => 75
          | (1, (4, 6)) => 75
          | (1, (5, 4)) => 55
          | (1, (5, 5)) => 92
          | (1, (5, 6)) => 92
          | (1, (6, 4)) => 55
          | (1, (6, 5)) => 92
          | (1, (6, 6)) => 92
          | (2, (4, 4)) => 50
          | (2, (4, 5)) => 51
          | (2, (4, 6)) => 51
          | (2, (5, 4)) => 63
          | (2, (5, 5)) => 91
          | (2, (5, 6)) => 91
          | (2, (6, 4)) => 63
          | (2, (6, 5)) => 91
          | (2, (6, 6)) => 91
          | (3, (0, 4)) => 51
          | (3, (0, 5)) => 94
          | (3, (0, 6)) => 94
          | (4, (0, 0)) => 62
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
          | (1, (4, 4)) => 48
          | (1, (4, 5)) => 16
          | (1, (4, 6)) => 16
          | (1, (5, 4)) => 11
          | (1, (5, 5)) => 0
          | (1, (5, 6)) => 0
          | (1, (6, 4)) => 11
          | (1, (6, 5)) => 0
          | (1, (6, 6)) => 0
          | (2, (4, 4)) => 50
          | (2, (4, 5)) => 49
          | (2, (4, 6)) => 49
          | (2, (5, 4)) => 10
          | (2, (5, 5)) => 0
          | (2, (5, 6)) => 0
          | (2, (6, 4)) => 10
          | (2, (6, 5)) => 0
          | (2, (6, 6)) => 0
          | (3, (0, 4)) => 48
          | (3, (0, 5)) => 1
          | (3, (0, 6)) => 1
          | (4, (0, 0)) => 0
          | _ => 500
          end,
          returnGen (MkExpr_ctor_Expr_ctor Ctor_Var Ctor_Var)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (4, 4)) => 48
          | (1, (4, 5)) => 16
          | (1, (4, 6)) => 16
          | (1, (5, 4)) => 11
          | (1, (5, 5)) => 0
          | (1, (5, 6)) => 0
          | (1, (6, 4)) => 11
          | (1, (6, 5)) => 0
          | (1, (6, 6)) => 0
          | (2, (4, 4)) => 50
          | (2, (4, 5)) => 49
          | (2, (4, 6)) => 49
          | (2, (5, 4)) => 10
          | (2, (5, 5)) => 0
          | (2, (5, 6)) => 0
          | (2, (6, 4)) => 10
          | (2, (6, 5)) => 0
          | (2, (6, 6)) => 0
          | (3, (0, 4)) => 48
          | (3, (0, 5)) => 1
          | (3, (0, 6)) => 1
          | (4, (0, 0)) => 0
          | _ => 500
          end,
          returnGen (MkExpr_ctor_Expr_ctor Ctor_Bool Ctor_Var)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (4, 4)) => 48
          | (1, (4, 5)) => 16
          | (1, (4, 6)) => 16
          | (1, (5, 4)) => 11
          | (1, (5, 5)) => 0
          | (1, (5, 6)) => 0
          | (1, (6, 4)) => 11
          | (1, (6, 5)) => 0
          | (1, (6, 6)) => 0
          | (2, (4, 4)) => 50
          | (2, (4, 5)) => 49
          | (2, (4, 6)) => 49
          | (2, (5, 4)) => 12
          | (2, (5, 5)) => 1
          | (2, (5, 6)) => 1
          | (2, (6, 4)) => 12
          | (2, (6, 5)) => 1
          | (2, (6, 6)) => 1
          | (3, (0, 4)) => 48
          | (3, (0, 5)) => 2
          | (3, (0, 6)) => 2
          | (4, (0, 0)) => 0
          | _ => 500
          end,
          returnGen (MkExpr_ctor_Expr_ctor Ctor_Abs Ctor_Var)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (4, 4)) => 52
          | (1, (4, 5)) => 62
          | (1, (4, 6)) => 62
          | (1, (5, 4)) => 45
          | (1, (5, 5)) => 2
          | (1, (5, 6)) => 2
          | (1, (6, 4)) => 45
          | (1, (6, 5)) => 2
          | (1, (6, 6)) => 2
          | (2, (4, 4)) => 50
          | (2, (4, 5)) => 50
          | (2, (4, 6)) => 50
          | (2, (5, 4)) => 38
          | (2, (5, 5)) => 0
          | (2, (5, 6)) => 0
          | (2, (6, 4)) => 38
          | (2, (6, 5)) => 0
          | (2, (6, 6)) => 0
          | (3, (0, 4)) => 50
          | (3, (0, 5)) => 1
          | (3, (0, 6)) => 1
          | (4, (0, 0)) => 0
          | _ => 500
          end,
          returnGen (MkExpr_ctor_Expr_ctor Ctor_App Ctor_Var)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (4, 4)) => 48
          | (1, (4, 5)) => 16
          | (1, (4, 6)) => 16
          | (1, (5, 4)) => 11
          | (1, (5, 5)) => 0
          | (1, (5, 6)) => 0
          | (1, (6, 4)) => 11
          | (1, (6, 5)) => 0
          | (1, (6, 6)) => 0
          | (2, (4, 4)) => 50
          | (2, (4, 5)) => 49
          | (2, (4, 6)) => 49
          | (2, (5, 4)) => 10
          | (2, (5, 5)) => 0
          | (2, (5, 6)) => 0
          | (2, (6, 4)) => 10
          | (2, (6, 5)) => 0
          | (2, (6, 6)) => 0
          | (3, (0, 4)) => 48
          | (3, (0, 5)) => 1
          | (3, (0, 6)) => 1
          | (4, (0, 0)) => 0
          | _ => 500
          end,
          returnGen (MkExpr_ctor_Expr_ctor Ctor_Var Ctor_Bool)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (4, 4)) => 48
          | (1, (4, 5)) => 16
          | (1, (4, 6)) => 16
          | (1, (5, 4)) => 11
          | (1, (5, 5)) => 0
          | (1, (5, 6)) => 0
          | (1, (6, 4)) => 11
          | (1, (6, 5)) => 0
          | (1, (6, 6)) => 0
          | (2, (4, 4)) => 50
          | (2, (4, 5)) => 49
          | (2, (4, 6)) => 49
          | (2, (5, 4)) => 10
          | (2, (5, 5)) => 0
          | (2, (5, 6)) => 0
          | (2, (6, 4)) => 10
          | (2, (6, 5)) => 0
          | (2, (6, 6)) => 0
          | (3, (0, 4)) => 48
          | (3, (0, 5)) => 1
          | (3, (0, 6)) => 1
          | (4, (0, 0)) => 0
          | _ => 500
          end,
          returnGen (MkExpr_ctor_Expr_ctor Ctor_Bool Ctor_Bool)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (4, 4)) => 48
          | (1, (4, 5)) => 16
          | (1, (4, 6)) => 16
          | (1, (5, 4)) => 11
          | (1, (5, 5)) => 0
          | (1, (5, 6)) => 0
          | (1, (6, 4)) => 11
          | (1, (6, 5)) => 0
          | (1, (6, 6)) => 0
          | (2, (4, 4)) => 50
          | (2, (4, 5)) => 49
          | (2, (4, 6)) => 49
          | (2, (5, 4)) => 12
          | (2, (5, 5)) => 1
          | (2, (5, 6)) => 1
          | (2, (6, 4)) => 12
          | (2, (6, 5)) => 1
          | (2, (6, 6)) => 1
          | (3, (0, 4)) => 48
          | (3, (0, 5)) => 2
          | (3, (0, 6)) => 2
          | (4, (0, 0)) => 0
          | _ => 500
          end,
          returnGen (MkExpr_ctor_Expr_ctor Ctor_Abs Ctor_Bool)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (4, 4)) => 52
          | (1, (4, 5)) => 62
          | (1, (4, 6)) => 62
          | (1, (5, 4)) => 45
          | (1, (5, 5)) => 2
          | (1, (5, 6)) => 2
          | (1, (6, 4)) => 45
          | (1, (6, 5)) => 2
          | (1, (6, 6)) => 2
          | (2, (4, 4)) => 50
          | (2, (4, 5)) => 50
          | (2, (4, 6)) => 50
          | (2, (5, 4)) => 38
          | (2, (5, 5)) => 0
          | (2, (5, 6)) => 0
          | (2, (6, 4)) => 38
          | (2, (6, 5)) => 0
          | (2, (6, 6)) => 0
          | (3, (0, 4)) => 50
          | (3, (0, 5)) => 1
          | (3, (0, 6)) => 1
          | (4, (0, 0)) => 0
          | _ => 500
          end,
          returnGen (MkExpr_ctor_Expr_ctor Ctor_App Ctor_Bool)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (4, 4)) => 48
          | (1, (4, 5)) => 16
          | (1, (4, 6)) => 16
          | (1, (5, 4)) => 11
          | (1, (5, 5)) => 0
          | (1, (5, 6)) => 0
          | (1, (6, 4)) => 11
          | (1, (6, 5)) => 0
          | (1, (6, 6)) => 0
          | (2, (4, 4)) => 50
          | (2, (4, 5)) => 49
          | (2, (4, 6)) => 49
          | (2, (5, 4)) => 12
          | (2, (5, 5)) => 1
          | (2, (5, 6)) => 1
          | (2, (6, 4)) => 12
          | (2, (6, 5)) => 1
          | (2, (6, 6)) => 1
          | (3, (0, 4)) => 48
          | (3, (0, 5)) => 2
          | (3, (0, 6)) => 2
          | (4, (0, 0)) => 0
          | _ => 500
          end,
          returnGen (MkExpr_ctor_Expr_ctor Ctor_Var Ctor_Abs)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (4, 4)) => 48
          | (1, (4, 5)) => 16
          | (1, (4, 6)) => 16
          | (1, (5, 4)) => 11
          | (1, (5, 5)) => 0
          | (1, (5, 6)) => 0
          | (1, (6, 4)) => 11
          | (1, (6, 5)) => 0
          | (1, (6, 6)) => 0
          | (2, (4, 4)) => 50
          | (2, (4, 5)) => 49
          | (2, (4, 6)) => 49
          | (2, (5, 4)) => 12
          | (2, (5, 5)) => 1
          | (2, (5, 6)) => 1
          | (2, (6, 4)) => 12
          | (2, (6, 5)) => 1
          | (2, (6, 6)) => 1
          | (3, (0, 4)) => 48
          | (3, (0, 5)) => 2
          | (3, (0, 6)) => 2
          | (4, (0, 0)) => 0
          | _ => 500
          end,
          returnGen (MkExpr_ctor_Expr_ctor Ctor_Bool Ctor_Abs)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (4, 4)) => 48
          | (1, (4, 5)) => 16
          | (1, (4, 6)) => 16
          | (1, (5, 4)) => 11
          | (1, (5, 5)) => 0
          | (1, (5, 6)) => 0
          | (1, (6, 4)) => 11
          | (1, (6, 5)) => 0
          | (1, (6, 6)) => 0
          | (2, (4, 4)) => 50
          | (2, (4, 5)) => 49
          | (2, (4, 6)) => 49
          | (2, (5, 4)) => 14
          | (2, (5, 5)) => 0
          | (2, (5, 6)) => 0
          | (2, (6, 4)) => 14
          | (2, (6, 5)) => 0
          | (2, (6, 6)) => 0
          | (3, (0, 4)) => 49
          | (3, (0, 5)) => 0
          | (3, (0, 6)) => 0
          | (4, (0, 0)) => 100
          | _ => 500
          end,
          returnGen (MkExpr_ctor_Expr_ctor Ctor_Abs Ctor_Abs)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (4, 4)) => 52
          | (1, (4, 5)) => 62
          | (1, (4, 6)) => 62
          | (1, (5, 4)) => 45
          | (1, (5, 5)) => 2
          | (1, (5, 6)) => 2
          | (1, (6, 4)) => 45
          | (1, (6, 5)) => 2
          | (1, (6, 6)) => 2
          | (2, (4, 4)) => 50
          | (2, (4, 5)) => 51
          | (2, (4, 6)) => 51
          | (2, (5, 4)) => 67
          | (2, (5, 5)) => 0
          | (2, (5, 6)) => 0
          | (2, (6, 4)) => 67
          | (2, (6, 5)) => 0
          | (2, (6, 6)) => 0
          | (3, (0, 4)) => 52
          | (3, (0, 5)) => 100
          | (3, (0, 6)) => 100
          | (4, (0, 0)) => 0
          | _ => 500
          end,
          returnGen (MkExpr_ctor_Expr_ctor Ctor_App Ctor_Abs)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (4, 4)) => 52
          | (1, (4, 5)) => 62
          | (1, (4, 6)) => 62
          | (1, (5, 4)) => 45
          | (1, (5, 5)) => 2
          | (1, (5, 6)) => 2
          | (1, (6, 4)) => 45
          | (1, (6, 5)) => 2
          | (1, (6, 6)) => 2
          | (2, (4, 4)) => 50
          | (2, (4, 5)) => 50
          | (2, (4, 6)) => 50
          | (2, (5, 4)) => 38
          | (2, (5, 5)) => 0
          | (2, (5, 6)) => 0
          | (2, (6, 4)) => 38
          | (2, (6, 5)) => 0
          | (2, (6, 6)) => 0
          | (3, (0, 4)) => 50
          | (3, (0, 5)) => 1
          | (3, (0, 6)) => 1
          | (4, (0, 0)) => 0
          | _ => 500
          end,
          returnGen (MkExpr_ctor_Expr_ctor Ctor_Var Ctor_App)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (4, 4)) => 52
          | (1, (4, 5)) => 62
          | (1, (4, 6)) => 62
          | (1, (5, 4)) => 45
          | (1, (5, 5)) => 2
          | (1, (5, 6)) => 2
          | (1, (6, 4)) => 45
          | (1, (6, 5)) => 2
          | (1, (6, 6)) => 2
          | (2, (4, 4)) => 50
          | (2, (4, 5)) => 50
          | (2, (4, 6)) => 50
          | (2, (5, 4)) => 38
          | (2, (5, 5)) => 0
          | (2, (5, 6)) => 0
          | (2, (6, 4)) => 38
          | (2, (6, 5)) => 0
          | (2, (6, 6)) => 0
          | (3, (0, 4)) => 50
          | (3, (0, 5)) => 1
          | (3, (0, 6)) => 1
          | (4, (0, 0)) => 0
          | _ => 500
          end,
          returnGen (MkExpr_ctor_Expr_ctor Ctor_Bool Ctor_App)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (4, 4)) => 52
          | (1, (4, 5)) => 62
          | (1, (4, 6)) => 62
          | (1, (5, 4)) => 45
          | (1, (5, 5)) => 2
          | (1, (5, 6)) => 2
          | (1, (6, 4)) => 45
          | (1, (6, 5)) => 2
          | (1, (6, 6)) => 2
          | (2, (4, 4)) => 50
          | (2, (4, 5)) => 51
          | (2, (4, 6)) => 51
          | (2, (5, 4)) => 67
          | (2, (5, 5)) => 0
          | (2, (5, 6)) => 0
          | (2, (6, 4)) => 67
          | (2, (6, 5)) => 0
          | (2, (6, 6)) => 0
          | (3, (0, 4)) => 52
          | (3, (0, 5)) => 100
          | (3, (0, 6)) => 100
          | (4, (0, 0)) => 0
          | _ => 500
          end,
          returnGen (MkExpr_ctor_Expr_ctor Ctor_Abs Ctor_App)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (4, 4)) => 58
          | (1, (4, 5)) => 95
          | (1, (4, 6)) => 95
          | (1, (5, 4)) => 97
          | (1, (5, 5)) => 100
          | (1, (5, 6)) => 100
          | (1, (6, 4)) => 97
          | (1, (6, 5)) => 100
          | (1, (6, 6)) => 100
          | (2, (4, 4)) => 51
          | (2, (4, 5)) => 56
          | (2, (4, 6)) => 56
          | (2, (5, 4)) => 97
          | (2, (5, 5)) => 100
          | (2, (5, 6)) => 100
          | (2, (6, 4)) => 97
          | (2, (6, 5)) => 100
          | (2, (6, 6)) => 100
          | (3, (0, 4)) => 63
          | (3, (0, 5)) => 100
          | (3, (0, 6)) => 100
          | (4, (0, 0)) => 100
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
      0,
      returnGen Ctor_Abs
    );
    (
      100,
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
          
