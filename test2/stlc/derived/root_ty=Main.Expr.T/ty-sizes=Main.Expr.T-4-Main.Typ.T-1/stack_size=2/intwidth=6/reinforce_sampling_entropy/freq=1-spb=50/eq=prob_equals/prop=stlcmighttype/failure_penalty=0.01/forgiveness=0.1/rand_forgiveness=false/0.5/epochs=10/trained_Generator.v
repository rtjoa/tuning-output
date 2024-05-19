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
    | (4, 4) => 44
    | (4, 5) => 45
    | (4, 6) => 40
    | (5, 4) => 39
    | (5, 5) => 41
    | (5, 6) => 50
    | (6, 4) => 42
    | (6, 5) => 51
    | (6, 6) => 57
    | _ => 500
    end
    in
    bindGen (freq [
      (weight_1, returnGen 1);
      (100-weight_1, returnGen 0)
    ]) (fun n1 =>
    let weight_2 :=
    match ((stack1 : nat), (stack2 : nat)) with 
    | (4, 4) => 44
    | (4, 5) => 52
    | (4, 6) => 60
    | (5, 4) => 53
    | (5, 5) => 60
    | (5, 6) => 48
    | (6, 4) => 48
    | (6, 5) => 63
    | (6, 6) => 63
    | _ => 500
    end
    in
    bindGen (freq [
      (weight_2, returnGen 2);
      (100-weight_2, returnGen 0)
    ]) (fun n2 =>
    let weight_4 :=
    match ((stack1 : nat), (stack2 : nat)) with 
    | (4, 4) => 49
    | (4, 5) => 57
    | (4, 6) => 53
    | (5, 4) => 54
    | (5, 5) => 48
    | (5, 6) => 37
    | (6, 4) => 52
    | (6, 5) => 64
    | (6, 6) => 45
    | _ => 500
    end
    in
    bindGen (freq [
      (weight_4, returnGen 4);
      (100-weight_4, returnGen 0)
    ]) (fun n4 =>
    let weight_8 :=
    match ((stack1 : nat), (stack2 : nat)) with 
    | (4, 4) => 42
    | (4, 5) => 44
    | (4, 6) => 54
    | (5, 4) => 52
    | (5, 5) => 60
    | (5, 6) => 50
    | (6, 4) => 49
    | (6, 5) => 53
    | (6, 6) => 61
    | _ => 500
    end
    in
    bindGen (freq [
      (weight_8, returnGen 8);
      (100-weight_8, returnGen 0)
    ]) (fun n8 =>
    let weight_16 :=
    match ((stack1 : nat), (stack2 : nat)) with 
    | (4, 4) => 62
    | (4, 5) => 63
    | (4, 6) => 53
    | (5, 4) => 50
    | (5, 5) => 60
    | (5, 6) => 34
    | (6, 4) => 60
    | (6, 5) => 55
    | (6, 6) => 46
    | _ => 500
    end
    in
    bindGen (freq [
      (weight_16, returnGen 16);
      (100-weight_16, returnGen 0)
    ]) (fun n16 =>
    let weight_32 :=
    match ((stack1 : nat), (stack2 : nat)) with 
    | (4, 4) => 39
    | (4, 5) => 44
    | (4, 6) => 54
    | (5, 4) => 45
    | (5, 5) => 46
    | (5, 6) => 66
    | (6, 4) => 47
    | (6, 5) => 32
    | (6, 6) => 63
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
    | (4, 4) => 48
    | (4, 5) => 54
    | (4, 6) => 54
    | (5, 4) => 59
    | (5, 5) => 47
    | (5, 6) => 56
    | (6, 4) => 35
    | (6, 5) => 33
    | (6, 6) => 55
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
          | (1, (0, 3)) => 42
          | (1, (4, 3)) => 55
          | (1, (5, 3)) => 58
          | (1, (6, 3)) => 48
          | _ => 500
          end,
          returnGen (MkTyp_ctor_Typ_ctor Ctor_TBool Ctor_TBool)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (0, 3)) => 51
          | (1, (4, 3)) => 47
          | (1, (5, 3)) => 55
          | (1, (6, 3)) => 50
          | _ => 500
          end,
          returnGen (MkTyp_ctor_Typ_ctor Ctor_TFun Ctor_TBool)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (0, 3)) => 56
          | (1, (4, 3)) => 56
          | (1, (5, 3)) => 46
          | (1, (6, 3)) => 57
          | _ => 500
          end,
          returnGen (MkTyp_ctor_Typ_ctor Ctor_TBool Ctor_TFun)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (0, 3)) => 55
          | (1, (4, 3)) => 44
          | (1, (5, 3)) => 41
          | (1, (6, 3)) => 47
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
      | (0, (4, 4)) => 46
      | (0, (4, 5)) => 55
      | (0, (4, 6)) => 52
      | (0, (5, 4)) => 57
      | (0, (5, 5)) => 47
      | (0, (5, 6)) => 51
      | (0, (6, 4)) => 51
      | (0, (6, 5)) => 54
      | (0, (6, 6)) => 57
      | _ => 500
      end
      in
      bindGen (freq [
        (weight_1, returnGen 1);
        (100-weight_1, returnGen 0)
      ]) (fun n1 =>
      let weight_2 :=
      match (size, ((stack1 : nat), (stack2 : nat))) with 
      | (0, (4, 4)) => 51
      | (0, (4, 5)) => 43
      | (0, (4, 6)) => 35
      | (0, (5, 4)) => 51
      | (0, (5, 5)) => 47
      | (0, (5, 6)) => 57
      | (0, (6, 4)) => 62
      | (0, (6, 5)) => 44
      | (0, (6, 6)) => 52
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
      | (0, (4, 5)) => 57
      | (0, (4, 6)) => 46
      | (0, (5, 4)) => 51
      | (0, (5, 5)) => 53
      | (0, (5, 6)) => 43
      | (0, (6, 4)) => 52
      | (0, (6, 5)) => 48
      | (0, (6, 6)) => 60
      | _ => 500
      end
      in
      bindGen (freq [
        (weight_4, returnGen 4);
        (100-weight_4, returnGen 0)
      ]) (fun n4 =>
      let weight_8 :=
      match (size, ((stack1 : nat), (stack2 : nat))) with 
      | (0, (4, 4)) => 46
      | (0, (4, 5)) => 43
      | (0, (4, 6)) => 46
      | (0, (5, 4)) => 43
      | (0, (5, 5)) => 53
      | (0, (5, 6)) => 43
      | (0, (6, 4)) => 43
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
      | (0, (4, 5)) => 53
      | (0, (4, 6)) => 65
      | (0, (5, 4)) => 54
      | (0, (5, 5)) => 53
      | (0, (5, 6)) => 57
      | (0, (6, 4)) => 56
      | (0, (6, 5)) => 56
      | (0, (6, 6)) => 57
      | _ => 500
      end
      in
      bindGen (freq [
        (weight_16, returnGen 16);
        (100-weight_16, returnGen 0)
      ]) (fun n16 =>
      let weight_32 :=
      match (size, ((stack1 : nat), (stack2 : nat))) with 
      | (0, (4, 4)) => 54
      | (0, (4, 5)) => 51
      | (0, (4, 6)) => 43
      | (0, (5, 4)) => 57
      | (0, (5, 5)) => 47
      | (0, (5, 6)) => 43
      | (0, (6, 4)) => 47
      | (0, (6, 5)) => 52
      | (0, (6, 6)) => 51
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
      | (0, (4, 4)) => 52
      | (0, (4, 5)) => 44
      | (0, (4, 6)) => 58
      | (0, (5, 4)) => 47
      | (0, (5, 5)) => 38
      | (0, (5, 6)) => 49
      | (0, (6, 4)) => 45
      | (0, (6, 5)) => 57
      | (0, (6, 6)) => 54
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
          | (0, (4, 5)) => 61
          | (0, (4, 6)) => 49
          | (0, (5, 4)) => 47
          | (0, (5, 5)) => 49
          | (0, (5, 6)) => 51
          | (0, (6, 4)) => 50
          | (0, (6, 5)) => 47
          | (0, (6, 6)) => 46
          | _ => 500
          end,
          returnGen (MkTyp_ctor_Expr_leaf_ctor Ctor_TBool Ctor_leaf_Var)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (0, (4, 4)) => 50
          | (0, (4, 5)) => 44
          | (0, (4, 6)) => 52
          | (0, (5, 4)) => 51
          | (0, (5, 5)) => 49
          | (0, (5, 6)) => 49
          | (0, (6, 4)) => 52
          | (0, (6, 5)) => 54
          | (0, (6, 6)) => 53
          | _ => 500
          end,
          returnGen (MkTyp_ctor_Expr_leaf_ctor Ctor_TFun Ctor_leaf_Var)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (0, (4, 4)) => 50
          | (0, (4, 5)) => 51
          | (0, (4, 6)) => 51
          | (0, (5, 4)) => 52
          | (0, (5, 5)) => 49
          | (0, (5, 6)) => 46
          | (0, (6, 4)) => 53
          | (0, (6, 5)) => 48
          | (0, (6, 6)) => 50
          | _ => 500
          end,
          returnGen (MkTyp_ctor_Expr_leaf_ctor Ctor_TBool Ctor_leaf_Bool)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (0, (4, 4)) => 50
          | (0, (4, 5)) => 44
          | (0, (4, 6)) => 48
          | (0, (5, 4)) => 50
          | (0, (5, 5)) => 53
          | (0, (5, 6)) => 53
          | (0, (6, 4)) => 46
          | (0, (6, 5)) => 51
          | (0, (6, 6)) => 51
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
          | (0, (4, 4)) => 57
          | (0, (4, 5)) => 51
          | (0, (4, 6)) => 52
          | (0, (5, 4)) => 47
          | (0, (5, 5)) => 46
          | (0, (5, 6)) => 45
          | (0, (6, 4)) => 52
          | (0, (6, 5)) => 53
          | (0, (6, 6)) => 50
          | _ => 500
          end,
          returnGen (MkExpr_leaf_ctor_Expr_leaf_ctor Ctor_leaf_Var Ctor_leaf_Var)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (0, (4, 4)) => 46
          | (0, (4, 5)) => 50
          | (0, (4, 6)) => 45
          | (0, (5, 4)) => 51
          | (0, (5, 5)) => 56
          | (0, (5, 6)) => 48
          | (0, (6, 4)) => 47
          | (0, (6, 5)) => 48
          | (0, (6, 6)) => 54
          | _ => 500
          end,
          returnGen (MkExpr_leaf_ctor_Expr_leaf_ctor Ctor_leaf_Bool Ctor_leaf_Var)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (0, (4, 4)) => 49
          | (0, (4, 5)) => 50
          | (0, (4, 6)) => 55
          | (0, (5, 4)) => 54
          | (0, (5, 5)) => 47
          | (0, (5, 6)) => 53
          | (0, (6, 4)) => 47
          | (0, (6, 5)) => 49
          | (0, (6, 6)) => 46
          | _ => 500
          end,
          returnGen (MkExpr_leaf_ctor_Expr_leaf_ctor Ctor_leaf_Var Ctor_leaf_Bool)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (0, (4, 4)) => 48
          | (0, (4, 5)) => 49
          | (0, (4, 6)) => 47
          | (0, (5, 4)) => 47
          | (0, (5, 5)) => 51
          | (0, (5, 6)) => 53
          | (0, (6, 4)) => 54
          | (0, (6, 5)) => 50
          | (0, (6, 6)) => 49
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
      | (1, (4, 4)) => 51
      | (1, (4, 5)) => 60
      | (1, (4, 6)) => 48
      | (1, (5, 4)) => 53
      | (1, (5, 5)) => 41
      | (1, (5, 6)) => 60
      | (1, (6, 4)) => 43
      | (1, (6, 5)) => 50
      | (1, (6, 6)) => 46
      | (2, (4, 4)) => 42
      | (2, (4, 5)) => 55
      | (2, (4, 6)) => 26
      | (2, (5, 4)) => 50
      | (2, (5, 5)) => 49
      | (2, (5, 6)) => 50
      | (2, (6, 4)) => 50
      | (2, (6, 5)) => 49
      | (2, (6, 6)) => 50
      | (3, (0, 4)) => 41
      | (3, (0, 5)) => 50
      | (3, (0, 6)) => 52
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
      | (1, (4, 4)) => 49
      | (1, (4, 5)) => 44
      | (1, (4, 6)) => 51
      | (1, (5, 4)) => 43
      | (1, (5, 5)) => 55
      | (1, (5, 6)) => 58
      | (1, (6, 4)) => 56
      | (1, (6, 5)) => 65
      | (1, (6, 6)) => 54
      | (2, (4, 4)) => 41
      | (2, (4, 5)) => 42
      | (2, (4, 6)) => 41
      | (2, (5, 4)) => 50
      | (2, (5, 5)) => 50
      | (2, (5, 6)) => 50
      | (2, (6, 4)) => 49
      | (2, (6, 5)) => 48
      | (2, (6, 6)) => 51
      | (3, (0, 4)) => 63
      | (3, (0, 5)) => 49
      | (3, (0, 6)) => 50
      | (4, (0, 0)) => 56
      | _ => 500
      end
      in
      bindGen (freq [
        (weight_2, returnGen 2);
        (100-weight_2, returnGen 0)
      ]) (fun n2 =>
      let weight_4 :=
      match (size, ((stack1 : nat), (stack2 : nat))) with 
      | (1, (4, 4)) => 49
      | (1, (4, 5)) => 47
      | (1, (4, 6)) => 56
      | (1, (5, 4)) => 47
      | (1, (5, 5)) => 53
      | (1, (5, 6)) => 46
      | (1, (6, 4)) => 58
      | (1, (6, 5)) => 40
      | (1, (6, 6)) => 31
      | (2, (4, 4)) => 44
      | (2, (4, 5)) => 52
      | (2, (4, 6)) => 56
      | (2, (5, 4)) => 50
      | (2, (5, 5)) => 50
      | (2, (5, 6)) => 49
      | (2, (6, 4)) => 51
      | (2, (6, 5)) => 50
      | (2, (6, 6)) => 50
      | (3, (0, 4)) => 49
      | (3, (0, 5)) => 51
      | (3, (0, 6)) => 50
      | (4, (0, 0)) => 66
      | _ => 500
      end
      in
      bindGen (freq [
        (weight_4, returnGen 4);
        (100-weight_4, returnGen 0)
      ]) (fun n4 =>
      let weight_8 :=
      match (size, ((stack1 : nat), (stack2 : nat))) with 
      | (1, (4, 4)) => 54
      | (1, (4, 5)) => 47
      | (1, (4, 6)) => 57
      | (1, (5, 4)) => 47
      | (1, (5, 5)) => 50
      | (1, (5, 6)) => 57
      | (1, (6, 4)) => 43
      | (1, (6, 5)) => 53
      | (1, (6, 6)) => 42
      | (2, (4, 4)) => 42
      | (2, (4, 5)) => 57
      | (2, (4, 6)) => 47
      | (2, (5, 4)) => 50
      | (2, (5, 5)) => 51
      | (2, (5, 6)) => 49
      | (2, (6, 4)) => 50
      | (2, (6, 5)) => 50
      | (2, (6, 6)) => 51
      | (3, (0, 4)) => 61
      | (3, (0, 5)) => 50
      | (3, (0, 6)) => 50
      | (4, (0, 0)) => 63
      | _ => 500
      end
      in
      bindGen (freq [
        (weight_8, returnGen 8);
        (100-weight_8, returnGen 0)
      ]) (fun n8 =>
      let weight_16 :=
      match (size, ((stack1 : nat), (stack2 : nat))) with 
      | (1, (4, 4)) => 49
      | (1, (4, 5)) => 59
      | (1, (4, 6)) => 57
      | (1, (5, 4)) => 57
      | (1, (5, 5)) => 50
      | (1, (5, 6)) => 40
      | (1, (6, 4)) => 52
      | (1, (6, 5)) => 35
      | (1, (6, 6)) => 40
      | (2, (4, 4)) => 42
      | (2, (4, 5)) => 50
      | (2, (4, 6)) => 47
      | (2, (5, 4)) => 50
      | (2, (5, 5)) => 49
      | (2, (5, 6)) => 50
      | (2, (6, 4)) => 50
      | (2, (6, 5)) => 51
      | (2, (6, 6)) => 50
      | (3, (0, 4)) => 52
      | (3, (0, 5)) => 50
      | (3, (0, 6)) => 52
      | (4, (0, 0)) => 40
      | _ => 500
      end
      in
      bindGen (freq [
        (weight_16, returnGen 16);
        (100-weight_16, returnGen 0)
      ]) (fun n16 =>
      let weight_32 :=
      match (size, ((stack1 : nat), (stack2 : nat))) with 
      | (1, (4, 4)) => 57
      | (1, (4, 5)) => 41
      | (1, (4, 6)) => 54
      | (1, (5, 4)) => 43
      | (1, (5, 5)) => 41
      | (1, (5, 6)) => 53
      | (1, (6, 4)) => 43
      | (1, (6, 5)) => 52
      | (1, (6, 6)) => 45
      | (2, (4, 4)) => 49
      | (2, (4, 5)) => 37
      | (2, (4, 6)) => 46
      | (2, (5, 4)) => 49
      | (2, (5, 5)) => 50
      | (2, (5, 6)) => 51
      | (2, (6, 4)) => 50
      | (2, (6, 5)) => 49
      | (2, (6, 6)) => 51
      | (3, (0, 4)) => 48
      | (3, (0, 5)) => 51
      | (3, (0, 6)) => 50
      | (4, (0, 0)) => 56
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
      | (1, (4, 5)) => 45
      | (1, (4, 6)) => 49
      | (1, (5, 4)) => 44
      | (1, (5, 5)) => 43
      | (1, (5, 6)) => 44
      | (1, (6, 4)) => 47
      | (1, (6, 5)) => 47
      | (1, (6, 6)) => 58
      | (2, (4, 4)) => 46
      | (2, (4, 5)) => 38
      | (2, (4, 6)) => 62
      | (2, (5, 4)) => 50
      | (2, (5, 5)) => 51
      | (2, (5, 6)) => 50
      | (2, (6, 4)) => 50
      | (2, (6, 5)) => 50
      | (2, (6, 6)) => 50
      | (3, (0, 4)) => 50
      | (3, (0, 5)) => 50
      | (3, (0, 6)) => 50
      | (4, (0, 0)) => 51
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
          | (1, (4, 4)) => 51
          | (1, (4, 5)) => 51
          | (1, (4, 6)) => 53
          | (1, (5, 4)) => 48
          | (1, (5, 5)) => 45
          | (1, (5, 6)) => 47
          | (1, (6, 4)) => 51
          | (1, (6, 5)) => 51
          | (1, (6, 6)) => 54
          | (2, (4, 4)) => 51
          | (2, (4, 5)) => 49
          | (2, (4, 6)) => 50
          | (2, (5, 4)) => 50
          | (2, (5, 5)) => 50
          | (2, (5, 6)) => 50
          | (2, (6, 4)) => 50
          | (2, (6, 5)) => 50
          | (2, (6, 6)) => 50
          | (3, (0, 4)) => 45
          | (3, (0, 5)) => 50
          | (3, (0, 6)) => 50
          | (4, (0, 0)) => 29
          | _ => 500
          end,
          returnGen (MkTyp_ctor_Expr_ctor Ctor_TBool Ctor_Var)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (4, 4)) => 49
          | (1, (4, 5)) => 51
          | (1, (4, 6)) => 49
          | (1, (5, 4)) => 48
          | (1, (5, 5)) => 44
          | (1, (5, 6)) => 59
          | (1, (6, 4)) => 53
          | (1, (6, 5)) => 50
          | (1, (6, 6)) => 47
          | (2, (4, 4)) => 50
          | (2, (4, 5)) => 42
          | (2, (4, 6)) => 46
          | (2, (5, 4)) => 50
          | (2, (5, 5)) => 50
          | (2, (5, 6)) => 50
          | (2, (6, 4)) => 50
          | (2, (6, 5)) => 50
          | (2, (6, 6)) => 50
          | (3, (0, 4)) => 46
          | (3, (0, 5)) => 50
          | (3, (0, 6)) => 50
          | (4, (0, 0)) => 33
          | _ => 500
          end,
          returnGen (MkTyp_ctor_Expr_ctor Ctor_TFun Ctor_Var)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (4, 4)) => 51
          | (1, (4, 5)) => 56
          | (1, (4, 6)) => 49
          | (1, (5, 4)) => 55
          | (1, (5, 5)) => 47
          | (1, (5, 6)) => 47
          | (1, (6, 4)) => 53
          | (1, (6, 5)) => 47
          | (1, (6, 6)) => 52
          | (2, (4, 4)) => 48
          | (2, (4, 5)) => 52
          | (2, (4, 6)) => 45
          | (2, (5, 4)) => 50
          | (2, (5, 5)) => 50
          | (2, (5, 6)) => 50
          | (2, (6, 4)) => 50
          | (2, (6, 5)) => 50
          | (2, (6, 6)) => 50
          | (3, (0, 4)) => 41
          | (3, (0, 5)) => 50
          | (3, (0, 6)) => 50
          | (4, (0, 0)) => 20
          | _ => 500
          end,
          returnGen (MkTyp_ctor_Expr_ctor Ctor_TBool Ctor_Bool)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (4, 4)) => 49
          | (1, (4, 5)) => 48
          | (1, (4, 6)) => 51
          | (1, (5, 4)) => 49
          | (1, (5, 5)) => 57
          | (1, (5, 6)) => 49
          | (1, (6, 4)) => 48
          | (1, (6, 5)) => 54
          | (1, (6, 6)) => 47
          | (2, (4, 4)) => 46
          | (2, (4, 5)) => 56
          | (2, (4, 6)) => 45
          | (2, (5, 4)) => 50
          | (2, (5, 5)) => 50
          | (2, (5, 6)) => 50
          | (2, (6, 4)) => 50
          | (2, (6, 5)) => 50
          | (2, (6, 6)) => 51
          | (3, (0, 4)) => 45
          | (3, (0, 5)) => 50
          | (3, (0, 6)) => 50
          | (4, (0, 0)) => 26
          | _ => 500
          end,
          returnGen (MkTyp_ctor_Expr_ctor Ctor_TFun Ctor_Bool)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (4, 4)) => 49
          | (1, (4, 5)) => 48
          | (1, (4, 6)) => 52
          | (1, (5, 4)) => 48
          | (1, (5, 5)) => 55
          | (1, (5, 6)) => 56
          | (1, (6, 4)) => 48
          | (1, (6, 5)) => 52
          | (1, (6, 6)) => 47
          | (2, (4, 4)) => 48
          | (2, (4, 5)) => 50
          | (2, (4, 6)) => 48
          | (2, (5, 4)) => 50
          | (2, (5, 5)) => 51
          | (2, (5, 6)) => 50
          | (2, (6, 4)) => 50
          | (2, (6, 5)) => 50
          | (2, (6, 6)) => 50
          | (3, (0, 4)) => 51
          | (3, (0, 5)) => 50
          | (3, (0, 6)) => 50
          | (4, (0, 0)) => 51
          | _ => 500
          end,
          returnGen (MkTyp_ctor_Expr_ctor Ctor_TBool Ctor_Abs)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (4, 4)) => 49
          | (1, (4, 5)) => 48
          | (1, (4, 6)) => 49
          | (1, (5, 4)) => 48
          | (1, (5, 5)) => 52
          | (1, (5, 6)) => 47
          | (1, (6, 4)) => 49
          | (1, (6, 5)) => 52
          | (1, (6, 6)) => 50
          | (2, (4, 4)) => 53
          | (2, (4, 5)) => 49
          | (2, (4, 6)) => 54
          | (2, (5, 4)) => 50
          | (2, (5, 5)) => 51
          | (2, (5, 6)) => 50
          | (2, (6, 4)) => 50
          | (2, (6, 5)) => 50
          | (2, (6, 6)) => 50
          | (3, (0, 4)) => 53
          | (3, (0, 5)) => 50
          | (3, (0, 6)) => 50
          | (4, (0, 0)) => 47
          | _ => 500
          end,
          returnGen (MkTyp_ctor_Expr_ctor Ctor_TFun Ctor_Abs)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (4, 4)) => 49
          | (1, (4, 5)) => 48
          | (1, (4, 6)) => 49
          | (1, (5, 4)) => 52
          | (1, (5, 5)) => 54
          | (1, (5, 6)) => 47
          | (1, (6, 4)) => 48
          | (1, (6, 5)) => 47
          | (1, (6, 6)) => 51
          | (2, (4, 4)) => 52
          | (2, (4, 5)) => 45
          | (2, (4, 6)) => 60
          | (2, (5, 4)) => 50
          | (2, (5, 5)) => 50
          | (2, (5, 6)) => 50
          | (2, (6, 4)) => 50
          | (2, (6, 5)) => 50
          | (2, (6, 6)) => 50
          | (3, (0, 4)) => 58
          | (3, (0, 5)) => 50
          | (3, (0, 6)) => 51
          | (4, (0, 0)) => 69
          | _ => 500
          end,
          returnGen (MkTyp_ctor_Expr_ctor Ctor_TBool Ctor_App)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (4, 4)) => 54
          | (1, (4, 5)) => 48
          | (1, (4, 6)) => 49
          | (1, (5, 4)) => 51
          | (1, (5, 5)) => 44
          | (1, (5, 6)) => 47
          | (1, (6, 4)) => 50
          | (1, (6, 5)) => 47
          | (1, (6, 6)) => 54
          | (2, (4, 4)) => 52
          | (2, (4, 5)) => 57
          | (2, (4, 6)) => 51
          | (2, (5, 4)) => 50
          | (2, (5, 5)) => 50
          | (2, (5, 6)) => 50
          | (2, (6, 4)) => 50
          | (2, (6, 5)) => 50
          | (2, (6, 6)) => 50
          | (3, (0, 4)) => 59
          | (3, (0, 5)) => 50
          | (3, (0, 6)) => 50
          | (4, (0, 0)) => 83
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
          | (1, (4, 6)) => 49
          | (1, (5, 4)) => 52
          | (1, (5, 5)) => 48
          | (1, (5, 6)) => 48
          | (1, (6, 4)) => 48
          | (1, (6, 5)) => 49
          | (1, (6, 6)) => 48
          | (2, (4, 4)) => 51
          | (2, (4, 5)) => 44
          | (2, (4, 6)) => 53
          | (2, (5, 4)) => 50
          | (2, (5, 5)) => 50
          | (2, (5, 6)) => 50
          | (2, (6, 4)) => 50
          | (2, (6, 5)) => 50
          | (2, (6, 6)) => 50
          | (3, (0, 4)) => 39
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
          | (1, (4, 5)) => 49
          | (1, (4, 6)) => 49
          | (1, (5, 4)) => 49
          | (1, (5, 5)) => 48
          | (1, (5, 6)) => 53
          | (1, (6, 4)) => 52
          | (1, (6, 5)) => 56
          | (1, (6, 6)) => 48
          | (2, (4, 4)) => 53
          | (2, (4, 5)) => 48
          | (2, (4, 6)) => 50
          | (2, (5, 4)) => 50
          | (2, (5, 5)) => 50
          | (2, (5, 6)) => 50
          | (2, (6, 4)) => 50
          | (2, (6, 5)) => 50
          | (2, (6, 6)) => 51
          | (3, (0, 4)) => 42
          | (3, (0, 5)) => 50
          | (3, (0, 6)) => 50
          | (4, (0, 0)) => 49
          | _ => 500
          end,
          returnGen (MkExpr_ctor_Expr_ctor Ctor_Bool Ctor_Var)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (4, 4)) => 49
          | (1, (4, 5)) => 49
          | (1, (4, 6)) => 53
          | (1, (5, 4)) => 53
          | (1, (5, 5)) => 48
          | (1, (5, 6)) => 48
          | (1, (6, 4)) => 55
          | (1, (6, 5)) => 49
          | (1, (6, 6)) => 49
          | (2, (4, 4)) => 54
          | (2, (4, 5)) => 55
          | (2, (4, 6)) => 48
          | (2, (5, 4)) => 50
          | (2, (5, 5)) => 50
          | (2, (5, 6)) => 50
          | (2, (6, 4)) => 50
          | (2, (6, 5)) => 50
          | (2, (6, 6)) => 50
          | (3, (0, 4)) => 52
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
          | (1, (4, 6)) => 52
          | (1, (5, 4)) => 49
          | (1, (5, 5)) => 48
          | (1, (5, 6)) => 54
          | (1, (6, 4)) => 48
          | (1, (6, 5)) => 49
          | (1, (6, 6)) => 48
          | (2, (4, 4)) => 49
          | (2, (4, 5)) => 60
          | (2, (4, 6)) => 49
          | (2, (5, 4)) => 50
          | (2, (5, 5)) => 50
          | (2, (5, 6)) => 50
          | (2, (6, 4)) => 50
          | (2, (6, 5)) => 50
          | (2, (6, 6)) => 50
          | (3, (0, 4)) => 51
          | (3, (0, 5)) => 50
          | (3, (0, 6)) => 50
          | (4, (0, 0)) => 51
          | _ => 500
          end,
          returnGen (MkExpr_ctor_Expr_ctor Ctor_App Ctor_Var)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (4, 4)) => 51
          | (1, (4, 5)) => 49
          | (1, (4, 6)) => 51
          | (1, (5, 4)) => 49
          | (1, (5, 5)) => 48
          | (1, (5, 6)) => 52
          | (1, (6, 4)) => 52
          | (1, (6, 5)) => 49
          | (1, (6, 6)) => 48
          | (2, (4, 4)) => 49
          | (2, (4, 5)) => 46
          | (2, (4, 6)) => 52
          | (2, (5, 4)) => 50
          | (2, (5, 5)) => 50
          | (2, (5, 6)) => 50
          | (2, (6, 4)) => 50
          | (2, (6, 5)) => 50
          | (2, (6, 6)) => 50
          | (3, (0, 4)) => 40
          | (3, (0, 5)) => 50
          | (3, (0, 6)) => 50
          | (4, (0, 0)) => 49
          | _ => 500
          end,
          returnGen (MkExpr_ctor_Expr_ctor Ctor_Var Ctor_Bool)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (4, 4)) => 49
          | (1, (4, 5)) => 52
          | (1, (4, 6)) => 52
          | (1, (5, 4)) => 49
          | (1, (5, 5)) => 52
          | (1, (5, 6)) => 48
          | (1, (6, 4)) => 48
          | (1, (6, 5)) => 52
          | (1, (6, 6)) => 53
          | (2, (4, 4)) => 50
          | (2, (4, 5)) => 44
          | (2, (4, 6)) => 46
          | (2, (5, 4)) => 50
          | (2, (5, 5)) => 50
          | (2, (5, 6)) => 50
          | (2, (6, 4)) => 50
          | (2, (6, 5)) => 50
          | (2, (6, 6)) => 50
          | (3, (0, 4)) => 41
          | (3, (0, 5)) => 50
          | (3, (0, 6)) => 50
          | (4, (0, 0)) => 49
          | _ => 500
          end,
          returnGen (MkExpr_ctor_Expr_ctor Ctor_Bool Ctor_Bool)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (4, 4)) => 49
          | (1, (4, 5)) => 49
          | (1, (4, 6)) => 49
          | (1, (5, 4)) => 54
          | (1, (5, 5)) => 48
          | (1, (5, 6)) => 52
          | (1, (6, 4)) => 48
          | (1, (6, 5)) => 53
          | (1, (6, 6)) => 48
          | (2, (4, 4)) => 47
          | (2, (4, 5)) => 50
          | (2, (4, 6)) => 51
          | (2, (5, 4)) => 50
          | (2, (5, 5)) => 50
          | (2, (5, 6)) => 50
          | (2, (6, 4)) => 50
          | (2, (6, 5)) => 50
          | (2, (6, 6)) => 50
          | (3, (0, 4)) => 48
          | (3, (0, 5)) => 50
          | (3, (0, 6)) => 50
          | (4, (0, 0)) => 50
          | _ => 500
          end,
          returnGen (MkExpr_ctor_Expr_ctor Ctor_Abs Ctor_Bool)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (4, 4)) => 51
          | (1, (4, 5)) => 50
          | (1, (4, 6)) => 49
          | (1, (5, 4)) => 49
          | (1, (5, 5)) => 48
          | (1, (5, 6)) => 48
          | (1, (6, 4)) => 48
          | (1, (6, 5)) => 49
          | (1, (6, 6)) => 48
          | (2, (4, 4)) => 47
          | (2, (4, 5)) => 48
          | (2, (4, 6)) => 47
          | (2, (5, 4)) => 50
          | (2, (5, 5)) => 50
          | (2, (5, 6)) => 50
          | (2, (6, 4)) => 50
          | (2, (6, 5)) => 50
          | (2, (6, 6)) => 50
          | (3, (0, 4)) => 55
          | (3, (0, 5)) => 50
          | (3, (0, 6)) => 50
          | (4, (0, 0)) => 50
          | _ => 500
          end,
          returnGen (MkExpr_ctor_Expr_ctor Ctor_App Ctor_Bool)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (4, 4)) => 50
          | (1, (4, 5)) => 49
          | (1, (4, 6)) => 49
          | (1, (5, 4)) => 49
          | (1, (5, 5)) => 48
          | (1, (5, 6)) => 48
          | (1, (6, 4)) => 48
          | (1, (6, 5)) => 49
          | (1, (6, 6)) => 53
          | (2, (4, 4)) => 49
          | (2, (4, 5)) => 47
          | (2, (4, 6)) => 52
          | (2, (5, 4)) => 50
          | (2, (5, 5)) => 50
          | (2, (5, 6)) => 50
          | (2, (6, 4)) => 50
          | (2, (6, 5)) => 50
          | (2, (6, 6)) => 50
          | (3, (0, 4)) => 43
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
          | (1, (4, 5)) => 52
          | (1, (4, 6)) => 49
          | (1, (5, 4)) => 49
          | (1, (5, 5)) => 48
          | (1, (5, 6)) => 48
          | (1, (6, 4)) => 48
          | (1, (6, 5)) => 53
          | (1, (6, 6)) => 52
          | (2, (4, 4)) => 47
          | (2, (4, 5)) => 44
          | (2, (4, 6)) => 56
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
          end,
          returnGen (MkExpr_ctor_Expr_ctor Ctor_Bool Ctor_Abs)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (4, 4)) => 49
          | (1, (4, 5)) => 49
          | (1, (4, 6)) => 49
          | (1, (5, 4)) => 49
          | (1, (5, 5)) => 48
          | (1, (5, 6)) => 48
          | (1, (6, 4)) => 52
          | (1, (6, 5)) => 49
          | (1, (6, 6)) => 48
          | (2, (4, 4)) => 50
          | (2, (4, 5)) => 59
          | (2, (4, 6)) => 47
          | (2, (5, 4)) => 50
          | (2, (5, 5)) => 50
          | (2, (5, 6)) => 50
          | (2, (6, 4)) => 50
          | (2, (6, 5)) => 50
          | (2, (6, 6)) => 50
          | (3, (0, 4)) => 45
          | (3, (0, 5)) => 52
          | (3, (0, 6)) => 50
          | (4, (0, 0)) => 50
          | _ => 500
          end,
          returnGen (MkExpr_ctor_Expr_ctor Ctor_Abs Ctor_Abs)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (4, 4)) => 52
          | (1, (4, 5)) => 54
          | (1, (4, 6)) => 49
          | (1, (5, 4)) => 49
          | (1, (5, 5)) => 51
          | (1, (5, 6)) => 48
          | (1, (6, 4)) => 48
          | (1, (6, 5)) => 49
          | (1, (6, 6)) => 56
          | (2, (4, 4)) => 51
          | (2, (4, 5)) => 52
          | (2, (4, 6)) => 48
          | (2, (5, 4)) => 50
          | (2, (5, 5)) => 50
          | (2, (5, 6)) => 50
          | (2, (6, 4)) => 50
          | (2, (6, 5)) => 50
          | (2, (6, 6)) => 50
          | (3, (0, 4)) => 57
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
          | (1, (4, 5)) => 49
          | (1, (4, 6)) => 49
          | (1, (5, 4)) => 49
          | (1, (5, 5)) => 52
          | (1, (5, 6)) => 52
          | (1, (6, 4)) => 48
          | (1, (6, 5)) => 49
          | (1, (6, 6)) => 53
          | (2, (4, 4)) => 54
          | (2, (4, 5)) => 50
          | (2, (4, 6)) => 49
          | (2, (5, 4)) => 50
          | (2, (5, 5)) => 50
          | (2, (5, 6)) => 50
          | (2, (6, 4)) => 50
          | (2, (6, 5)) => 50
          | (2, (6, 6)) => 50
          | (3, (0, 4)) => 53
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
          | (1, (4, 5)) => 49
          | (1, (4, 6)) => 49
          | (1, (5, 4)) => 49
          | (1, (5, 5)) => 57
          | (1, (5, 6)) => 48
          | (1, (6, 4)) => 51
          | (1, (6, 5)) => 49
          | (1, (6, 6)) => 48
          | (2, (4, 4)) => 49
          | (2, (4, 5)) => 48
          | (2, (4, 6)) => 48
          | (2, (5, 4)) => 50
          | (2, (5, 5)) => 50
          | (2, (5, 6)) => 50
          | (2, (6, 4)) => 50
          | (2, (6, 5)) => 50
          | (2, (6, 6)) => 50
          | (3, (0, 4)) => 49
          | (3, (0, 5)) => 51
          | (3, (0, 6)) => 50
          | (4, (0, 0)) => 50
          | _ => 500
          end,
          returnGen (MkExpr_ctor_Expr_ctor Ctor_Bool Ctor_App)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (4, 4)) => 53
          | (1, (4, 5)) => 50
          | (1, (4, 6)) => 49
          | (1, (5, 4)) => 52
          | (1, (5, 5)) => 48
          | (1, (5, 6)) => 53
          | (1, (6, 4)) => 48
          | (1, (6, 5)) => 49
          | (1, (6, 6)) => 48
          | (2, (4, 4)) => 51
          | (2, (4, 5)) => 59
          | (2, (4, 6)) => 54
          | (2, (5, 4)) => 50
          | (2, (5, 5)) => 50
          | (2, (5, 6)) => 50
          | (2, (6, 4)) => 50
          | (2, (6, 5)) => 50
          | (2, (6, 6)) => 50
          | (3, (0, 4)) => 63
          | (3, (0, 5)) => 50
          | (3, (0, 6)) => 50
          | (4, (0, 0)) => 50
          | _ => 500
          end,
          returnGen (MkExpr_ctor_Expr_ctor Ctor_Abs Ctor_App)
        );
        (
          match (size, ((stack1 : nat), (stack2 : nat))) with 
          | (1, (4, 4)) => 49
          | (1, (4, 5)) => 49
          | (1, (4, 6)) => 52
          | (1, (5, 4)) => 53
          | (1, (5, 5)) => 56
          | (1, (5, 6)) => 48
          | (1, (6, 4)) => 52
          | (1, (6, 5)) => 49
          | (1, (6, 6)) => 48
          | (2, (4, 4)) => 50
          | (2, (4, 5)) => 44
          | (2, (4, 6)) => 52
          | (2, (5, 4)) => 50
          | (2, (5, 5)) => 50
          | (2, (5, 6)) => 50
          | (2, (6, 4)) => 50
          | (2, (6, 5)) => 51
          | (2, (6, 6)) => 50
          | (3, (0, 4)) => 67
          | (3, (0, 5)) => 50
          | (3, (0, 6)) => 51
          | (4, (0, 0)) => 51
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
      13,
      returnGen Ctor_Var
    );
    (
      7,
      returnGen Ctor_Bool
    );
    (
      91,
      returnGen Ctor_Abs
    );
    (
      5,
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
          
