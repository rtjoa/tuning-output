From QuickChick Require Import QuickChick. Import QcNotation.
From Coq Require Import Bool ZArith List. Import ListNotations.
From ExtLib Require Import Monad.
From ExtLib.Data.Monads Require Import OptionMonad.
Import MonadNotation.

From STLC Require Import Impl Spec.

Inductive Typ_leaf_ctor : Type :=
  | Ctor_leaf_TBool : Typ_leaf_ctor.

Inductive Expr_leaf_ctor : Type :=
  | Ctor_leaf_Var : Expr_leaf_ctor
  | Ctor_leaf_Bool : Expr_leaf_ctor.

Inductive Typ_ctor : Type :=
  | Ctor_TBool : Typ_ctor
  | Ctor_TFun : Typ_ctor.

Inductive Expr_ctor : Type :=
  | Ctor_Var : Expr_ctor
  | Ctor_Bool : Expr_ctor
  | Ctor_Abs : Expr_ctor
  | Ctor_App : Expr_ctor.

Definition gen_leaf_Typ (chosen_ctor : Typ_leaf_ctor) (stack1 : nat) : G Typ :=
  match chosen_ctor with
  | Ctor_leaf_TBool =>
    returnGen (TBool )
  end.

Definition gen_leaf_Expr (chosen_ctor : Expr_leaf_ctor) (stack1 : nat) : G Expr :=
  match chosen_ctor with
  | Ctor_leaf_Var =>
    let weight_1 :=
    match ((stack1 : nat)) with 
    | (4) => 500
    | (5) => 500
    | (6) => 500
    | _ => 500
    end
    in
    bindGen (freq [
      (weight_1, returnGen 1);
      (1000-weight_1, returnGen 0)
    ]) (fun n1 : nat =>
    let weight_2 :=
    match ((stack1 : nat)) with 
    | (4) => 500
    | (5) => 500
    | (6) => 500
    | _ => 500
    end
    in
    bindGen (freq [
      (weight_2, returnGen 2);
      (1000-weight_2, returnGen 0)
    ]) (fun n2 : nat =>
    let weight_4 :=
    match ((stack1 : nat)) with 
    | (4) => 500
    | (5) => 500
    | (6) => 500
    | _ => 500
    end
    in
    bindGen (freq [
      (weight_4, returnGen 4);
      (1000-weight_4, returnGen 0)
    ]) (fun n4 : nat =>
    let weight_8 :=
    match ((stack1 : nat)) with 
    | (4) => 500
    | (5) => 500
    | (6) => 500
    | _ => 500
    end
    in
    bindGen (freq [
      (weight_8, returnGen 8);
      (1000-weight_8, returnGen 0)
    ]) (fun n8 : nat =>
    let p1 := n1 + n2 + n4 + n8 in 
    returnGen (Var p1)))))
  | Ctor_leaf_Bool =>
    let weight_true :=
    match ((stack1 : nat)) with 
    | (4) => 500
    | (5) => 500
    | (6) => 500
    | _ => 500
    end
    in
    bindGen (freq [
      (weight_true, returnGen true);
      (1000-weight_true, returnGen false)
    ]) (fun p1 : bool =>
    returnGen (Bool p1))
  end.

Fixpoint gen_Typ (chosen_ctor : Typ_ctor) (size : nat) (stack1 : nat) : G Typ :=
  match size with
  | 0 =>
    match chosen_ctor with
    | Ctor_TBool =>
      returnGen (TBool )
    | Ctor_TFun =>
      bindGen (freq [
        (* no alternatives, so lets just put this again *)
        (
          match (size, ((stack1 : nat))) with 
          | (0, (1)) => 500
          | (0, (2)) => 500
          | _ => 500
          end,
          returnGen (Ctor_leaf_TBool, Ctor_leaf_TBool)
        );
        (
          match (size, ((stack1 : nat))) with 
          | (0, (1)) => 500
          | (0, (2)) => 500
          | _ => 500
          end,
          returnGen (Ctor_leaf_TBool, Ctor_leaf_TBool)
        )
      ]) (fun param_variantis =>
      let '(param1_ctor, param2_ctor) := param_variantis in
      bindGen (gen_leaf_Typ param1_ctor  1)
      (fun p1 : Typ =>
      bindGen (gen_leaf_Typ param2_ctor  2)
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
          match (size, ((stack1 : nat))) with 
          | (1, (3)) => 500
          | _ => 500
          end,
          returnGen (Ctor_TBool, Ctor_TBool)
        );
        (
          match (size, ((stack1 : nat))) with 
          | (1, (3)) => 500
          | _ => 500
          end,
          returnGen (Ctor_TFun, Ctor_TBool)
        );
        (
          match (size, ((stack1 : nat))) with 
          | (1, (3)) => 500
          | _ => 500
          end,
          returnGen (Ctor_TBool, Ctor_TFun)
        );
        (
          match (size, ((stack1 : nat))) with 
          | (1, (3)) => 500
          | _ => 500
          end,
          returnGen (Ctor_TFun, Ctor_TFun)
        )
      ]) (fun param_variantis =>
      let '(param1_ctor, param2_ctor) := param_variantis in
      bindGen (gen_Typ param1_ctor size'  1)
      (fun p1 : Typ =>
      bindGen (gen_Typ param2_ctor size'  2)
      (fun p2 : Typ =>
      returnGen (TFun p1 p2))))
  end
  end.

Fixpoint gen_Expr (chosen_ctor : Expr_ctor) (size : nat) (stack1 : nat) : G Expr :=
  match size with
  | 0 =>
    match chosen_ctor with
    | Ctor_Var =>
      let weight_1 :=
      match (size, ((stack1 : nat))) with 
      | (0, (4)) => 500
      | (0, (5)) => 500
      | (0, (6)) => 500
      | _ => 500
      end
      in
      bindGen (freq [
        (weight_1, returnGen 1);
        (1000-weight_1, returnGen 0)
      ]) (fun n1 : nat =>
      let weight_2 :=
      match (size, ((stack1 : nat))) with 
      | (0, (4)) => 500
      | (0, (5)) => 500
      | (0, (6)) => 500
      | _ => 500
      end
      in
      bindGen (freq [
        (weight_2, returnGen 2);
        (1000-weight_2, returnGen 0)
      ]) (fun n2 : nat =>
      let weight_4 :=
      match (size, ((stack1 : nat))) with 
      | (0, (4)) => 500
      | (0, (5)) => 500
      | (0, (6)) => 500
      | _ => 500
      end
      in
      bindGen (freq [
        (weight_4, returnGen 4);
        (1000-weight_4, returnGen 0)
      ]) (fun n4 : nat =>
      let weight_8 :=
      match (size, ((stack1 : nat))) with 
      | (0, (4)) => 500
      | (0, (5)) => 500
      | (0, (6)) => 500
      | _ => 500
      end
      in
      bindGen (freq [
        (weight_8, returnGen 8);
        (1000-weight_8, returnGen 0)
      ]) (fun n8 : nat =>
      let p1 := n1 + n2 + n4 + n8 in 
      returnGen (Var p1)))))
    | Ctor_Bool =>
      let weight_true :=
      match (size, ((stack1 : nat))) with 
      | (0, (4)) => 500
      | (0, (5)) => 500
      | (0, (6)) => 500
      | _ => 500
      end
      in
      bindGen (freq [
        (weight_true, returnGen true);
        (1000-weight_true, returnGen false)
      ]) (fun p1 : bool =>
      returnGen (Bool p1))
    | Ctor_Abs =>
      bindGen (freq [
        (
          match (size, ((stack1 : nat))) with 
          | (0, (4)) => 500
          | (0, (5)) => 500
          | (0, (6)) => 500
          | _ => 500
          end,
          returnGen (Ctor_TBool, Ctor_leaf_Var)
        );
        (
          match (size, ((stack1 : nat))) with 
          | (0, (4)) => 500
          | (0, (5)) => 500
          | (0, (6)) => 500
          | _ => 500
          end,
          returnGen (Ctor_TFun, Ctor_leaf_Var)
        );
        (
          match (size, ((stack1 : nat))) with 
          | (0, (4)) => 500
          | (0, (5)) => 500
          | (0, (6)) => 500
          | _ => 500
          end,
          returnGen (Ctor_TBool, Ctor_leaf_Bool)
        );
        (
          match (size, ((stack1 : nat))) with 
          | (0, (4)) => 500
          | (0, (5)) => 500
          | (0, (6)) => 500
          | _ => 500
          end,
          returnGen (Ctor_TFun, Ctor_leaf_Bool)
        )
      ]) (fun param_variantis =>
      let '(param1_ctor, param2_ctor) := param_variantis in
      bindGen (gen_Typ param1_ctor 1  3)
      (fun p1 : Typ =>
      bindGen (gen_leaf_Expr param2_ctor  4)
      (fun p2 : Expr =>
      returnGen (Abs p1 p2))))
    | Ctor_App =>
      bindGen (freq [
        (
          match (size, ((stack1 : nat))) with 
          | (0, (4)) => 500
          | (0, (5)) => 500
          | (0, (6)) => 500
          | _ => 500
          end,
          returnGen (Ctor_leaf_Var, Ctor_leaf_Var)
        );
        (
          match (size, ((stack1 : nat))) with 
          | (0, (4)) => 500
          | (0, (5)) => 500
          | (0, (6)) => 500
          | _ => 500
          end,
          returnGen (Ctor_leaf_Bool, Ctor_leaf_Var)
        );
        (
          match (size, ((stack1 : nat))) with 
          | (0, (4)) => 500
          | (0, (5)) => 500
          | (0, (6)) => 500
          | _ => 500
          end,
          returnGen (Ctor_leaf_Var, Ctor_leaf_Bool)
        );
        (
          match (size, ((stack1 : nat))) with 
          | (0, (4)) => 500
          | (0, (5)) => 500
          | (0, (6)) => 500
          | _ => 500
          end,
          returnGen (Ctor_leaf_Bool, Ctor_leaf_Bool)
        )
      ]) (fun param_variantis =>
      let '(param1_ctor, param2_ctor) := param_variantis in
      bindGen (gen_leaf_Expr param1_ctor  5)
      (fun p1 : Expr =>
      bindGen (gen_leaf_Expr param2_ctor  6)
      (fun p2 : Expr =>
      returnGen (App p1 p2))))
  end
  | S size' =>
    match chosen_ctor with
    | Ctor_Var =>
      let weight_1 :=
      match (size, ((stack1 : nat))) with 
      | (1, (0)) => 500
      | _ => 500
      end
      in
      bindGen (freq [
        (weight_1, returnGen 1);
        (1000-weight_1, returnGen 0)
      ]) (fun n1 : nat =>
      let weight_2 :=
      match (size, ((stack1 : nat))) with 
      | (1, (0)) => 500
      | _ => 500
      end
      in
      bindGen (freq [
        (weight_2, returnGen 2);
        (1000-weight_2, returnGen 0)
      ]) (fun n2 : nat =>
      let weight_4 :=
      match (size, ((stack1 : nat))) with 
      | (1, (0)) => 500
      | _ => 500
      end
      in
      bindGen (freq [
        (weight_4, returnGen 4);
        (1000-weight_4, returnGen 0)
      ]) (fun n4 : nat =>
      let weight_8 :=
      match (size, ((stack1 : nat))) with 
      | (1, (0)) => 500
      | _ => 500
      end
      in
      bindGen (freq [
        (weight_8, returnGen 8);
        (1000-weight_8, returnGen 0)
      ]) (fun n8 : nat =>
      let p1 := n1 + n2 + n4 + n8 in 
      returnGen (Var p1)))))
    | Ctor_Bool =>
      let weight_true :=
      match (size, ((stack1 : nat))) with 
      | (1, (0)) => 500
      | _ => 500
      end
      in
      bindGen (freq [
        (weight_true, returnGen true);
        (1000-weight_true, returnGen false)
      ]) (fun p1 : bool =>
      returnGen (Bool p1))
    | Ctor_Abs =>
      bindGen (freq [
        (
          match (size, ((stack1 : nat))) with 
          | (1, (0)) => 533
          | _ => 500
          end,
          returnGen (Ctor_TBool, Ctor_Var)
        );
        (
          match (size, ((stack1 : nat))) with 
          | (1, (0)) => 533
          | _ => 500
          end,
          returnGen (Ctor_TFun, Ctor_Var)
        );
        (
          match (size, ((stack1 : nat))) with 
          | (1, (0)) => 533
          | _ => 500
          end,
          returnGen (Ctor_TBool, Ctor_Bool)
        );
        (
          match (size, ((stack1 : nat))) with 
          | (1, (0)) => 533
          | _ => 500
          end,
          returnGen (Ctor_TFun, Ctor_Bool)
        );
        (
          match (size, ((stack1 : nat))) with 
          | (1, (0)) => 441
          | _ => 500
          end,
          returnGen (Ctor_TBool, Ctor_Abs)
        );
        (
          match (size, ((stack1 : nat))) with 
          | (1, (0)) => 441
          | _ => 500
          end,
          returnGen (Ctor_TFun, Ctor_Abs)
        );
        (
          match (size, ((stack1 : nat))) with 
          | (1, (0)) => 489
          | _ => 500
          end,
          returnGen (Ctor_TBool, Ctor_App)
        );
        (
          match (size, ((stack1 : nat))) with 
          | (1, (0)) => 489
          | _ => 500
          end,
          returnGen (Ctor_TFun, Ctor_App)
        )
      ]) (fun param_variantis =>
      let '(param1_ctor, param2_ctor) := param_variantis in
      bindGen (gen_Typ param1_ctor 1  3)
      (fun p1 : Typ =>
      bindGen (gen_Expr param2_ctor size'  4)
      (fun p2 : Expr =>
      returnGen (Abs p1 p2))))
    | Ctor_App =>
      bindGen (freq [
        (
          match (size, ((stack1 : nat))) with 
          | (1, (0)) => 184
          | _ => 500
          end,
          returnGen (Ctor_Var, Ctor_Var)
        );
        (
          match (size, ((stack1 : nat))) with 
          | (1, (0)) => 184
          | _ => 500
          end,
          returnGen (Ctor_Bool, Ctor_Var)
        );
        (
          match (size, ((stack1 : nat))) with 
          | (1, (0)) => 233
          | _ => 500
          end,
          returnGen (Ctor_Abs, Ctor_Var)
        );
        (
          match (size, ((stack1 : nat))) with 
          | (1, (0)) => 274
          | _ => 500
          end,
          returnGen (Ctor_App, Ctor_Var)
        );
        (
          match (size, ((stack1 : nat))) with 
          | (1, (0)) => 184
          | _ => 500
          end,
          returnGen (Ctor_Var, Ctor_Bool)
        );
        (
          match (size, ((stack1 : nat))) with 
          | (1, (0)) => 184
          | _ => 500
          end,
          returnGen (Ctor_Bool, Ctor_Bool)
        );
        (
          match (size, ((stack1 : nat))) with 
          | (1, (0)) => 233
          | _ => 500
          end,
          returnGen (Ctor_Abs, Ctor_Bool)
        );
        (
          match (size, ((stack1 : nat))) with 
          | (1, (0)) => 274
          | _ => 500
          end,
          returnGen (Ctor_App, Ctor_Bool)
        );
        (
          match (size, ((stack1 : nat))) with 
          | (1, (0)) => 233
          | _ => 500
          end,
          returnGen (Ctor_Var, Ctor_Abs)
        );
        (
          match (size, ((stack1 : nat))) with 
          | (1, (0)) => 233
          | _ => 500
          end,
          returnGen (Ctor_Bool, Ctor_Abs)
        );
        (
          match (size, ((stack1 : nat))) with 
          | (1, (0)) => 274
          | _ => 500
          end,
          returnGen (Ctor_Abs, Ctor_Abs)
        );
        (
          match (size, ((stack1 : nat))) with 
          | (1, (0)) => 746
          | _ => 500
          end,
          returnGen (Ctor_App, Ctor_Abs)
        );
        (
          match (size, ((stack1 : nat))) with 
          | (1, (0)) => 274
          | _ => 500
          end,
          returnGen (Ctor_Var, Ctor_App)
        );
        (
          match (size, ((stack1 : nat))) with 
          | (1, (0)) => 274
          | _ => 500
          end,
          returnGen (Ctor_Bool, Ctor_App)
        );
        (
          match (size, ((stack1 : nat))) with 
          | (1, (0)) => 746
          | _ => 500
          end,
          returnGen (Ctor_Abs, Ctor_App)
        );
        (
          match (size, ((stack1 : nat))) with 
          | (1, (0)) => 954
          | _ => 500
          end,
          returnGen (Ctor_App, Ctor_App)
        )
      ]) (fun param_variantis =>
      let '(param1_ctor, param2_ctor) := param_variantis in
      bindGen (gen_Expr param1_ctor size'  5)
      (fun p1 : Expr =>
      bindGen (gen_Expr param2_ctor size'  6)
      (fun p2 : Expr =>
      returnGen (App p1 p2))))
  end
  end.

Definition gSized :=
  bindGen (freq [
    (
      match (tt) with 
      | (tt) => 23
      end,
      Ctor_Var
    );
    (
      match (tt) with 
      | (tt) => 23
      end,
      Ctor_Bool
    );
    (
      match (tt) with 
      | (tt) => 131
      end,
      Ctor_Abs
    );
    (
      match (tt) with 
      | (tt) => 978
      end,
      Ctor_App
    )
  ]) (fun init_ctor =>
  gen_Expr init_ctor 1 0.).

  Definition test_prop_SinglePreserve :=
forAll gSized (fun (e: Expr) =>
  prop_SinglePreserve e).

(*! QuickChick test_prop_SinglePreserve. *)

Definition test_prop_MultiPreserve :=
forAll gSized (fun (e: Expr) =>
  prop_MultiPreserve e).

(*! QuickChick test_prop_MultiPreserve. *)
          
