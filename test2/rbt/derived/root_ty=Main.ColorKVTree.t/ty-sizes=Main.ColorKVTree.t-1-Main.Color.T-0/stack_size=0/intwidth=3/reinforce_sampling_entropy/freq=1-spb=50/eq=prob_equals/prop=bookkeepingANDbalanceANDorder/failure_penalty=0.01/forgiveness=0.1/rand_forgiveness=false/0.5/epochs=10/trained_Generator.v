Require Import ZArith.
From QuickChick Require Import QuickChick.
From ExtLib Require Import Monad.
From ExtLib.Data.Monads Require Import OptionMonad.
Import QcNotation.
Import MonadNotation.
From Coq Require Import List.
Import ListNotations.

From RBT Require Import Impl Spec.

Inductive Color_leaf_ctor :=
  | Ctor_leaf_R
  | Ctor_leaf_B.

Inductive Tree_leaf_ctor :=
  | Ctor_leaf_E.

Inductive Color_ctor :=
  | Ctor_R
  | Ctor_B.

Inductive Tree_ctor :=
  | Ctor_E
  | Ctor_T.

Inductive Color_ctor_Tree_ctor_Tree_ctor :=
  | MkColor_ctor_Tree_ctor_Tree_ctor : Color_ctor -> Tree_ctor -> Tree_ctor -> Color_ctor_Tree_ctor_Tree_ctor.
Inductive Color_ctor_Tree_leaf_ctor_Tree_leaf_ctor :=
  | MkColor_ctor_Tree_leaf_ctor_Tree_leaf_ctor : Color_ctor -> Tree_leaf_ctor -> Tree_leaf_ctor -> Color_ctor_Tree_leaf_ctor_Tree_leaf_ctor.
Definition gen_leaf_Color (chosen_ctor : Color_leaf_ctor)  : G Color :=
  match chosen_ctor with
  | Ctor_leaf_R =>
    returnGen (R )
  | Ctor_leaf_B =>
    returnGen (B )
  end.

Definition gen_leaf_Tree (chosen_ctor : Tree_leaf_ctor)  : G Tree :=
  match chosen_ctor with
  | Ctor_leaf_E =>
    returnGen (E )
  end.

Fixpoint gen_Color (chosen_ctor : Color_ctor) (size : nat)  : G Color :=
  match size with
  | 0 =>
    match chosen_ctor with
    | Ctor_R =>
      returnGen (R )
    | Ctor_B =>
      returnGen (B )
  end
  | S size' =>
    match chosen_ctor with
    | Ctor_R =>
      returnGen (R )
    | Ctor_B =>
      returnGen (B )
  end
  end.

Fixpoint gen_Tree (size : nat) (chosen_ctor : Tree_ctor)   : G Tree :=
  match size with
  | 0 =>
    match chosen_ctor with
    | Ctor_E =>
      returnGen (E )
    | Ctor_T =>
      bindGen (freq [
        (
          match (size, tt) with 
          | (0, tt) => 60
          | _ => 500
          end,
          returnGen (MkColor_ctor_Tree_leaf_ctor_Tree_leaf_ctor Ctor_R Ctor_leaf_E Ctor_leaf_E)
        );
        (
          match (size, tt) with 
          | (0, tt) => 39
          | _ => 500
          end,
          returnGen (MkColor_ctor_Tree_leaf_ctor_Tree_leaf_ctor Ctor_B Ctor_leaf_E Ctor_leaf_E)
        )
      ]) (fun param_variantis =>
      let '(MkColor_ctor_Tree_leaf_ctor_Tree_leaf_ctor param1_ctor param2_ctor param5_ctor) := param_variantis in
      bindGen (gen_Color param1_ctor 0 )
      (fun p1 : Color =>
      bindGen (gen_leaf_Tree param2_ctor )
      (fun p2 : Tree =>
      let weight_1 :=
      match (size, tt) with 
      | (0, tt) => 49
      | _ => 500
      end
      in
      bindGen (freq [
        (weight_1, returnGen 1%Z);
        (100-weight_1, returnGen 0%Z)
      ]) (fun n1 =>
      let weight_2 :=
      match (size, tt) with 
      | (0, tt) => 54
      | _ => 500
      end
      in
      bindGen (freq [
        (weight_2, returnGen 2%Z);
        (100-weight_2, returnGen 0%Z)
      ]) (fun n2 =>
      let weight_4 :=
      match (size, tt) with 
      | (0, tt) => 46
      | _ => 500
      end
      in
      bindGen (freq [
        (weight_4, returnGen 4%Z);
        (100-weight_4, returnGen 0%Z)
      ]) (fun n4 =>
      let p3 := (n1 + n2 + n4)%Z in 
      let weight_1 :=
      match (size, tt) with 
      | (0, tt) => 39
      | _ => 500
      end
      in
      bindGen (freq [
        (weight_1, returnGen 1%Z);
        (100-weight_1, returnGen 0%Z)
      ]) (fun n1 =>
      let weight_2 :=
      match (size, tt) with 
      | (0, tt) => 58
      | _ => 500
      end
      in
      bindGen (freq [
        (weight_2, returnGen 2%Z);
        (100-weight_2, returnGen 0%Z)
      ]) (fun n2 =>
      let weight_4 :=
      match (size, tt) with 
      | (0, tt) => 59
      | _ => 500
      end
      in
      bindGen (freq [
        (weight_4, returnGen 4%Z);
        (100-weight_4, returnGen 0%Z)
      ]) (fun n4 =>
      let p4 := (n1 + n2 + n4)%Z in 
      bindGen (gen_leaf_Tree param5_ctor )
      (fun p5 : Tree =>
      returnGen (T p1 p2 p3 p4 p5)))))))))))
  end
  | S size' =>
    match chosen_ctor with
    | Ctor_E =>
      returnGen (E )
    | Ctor_T =>
      bindGen (freq [
        (
          match (size, tt) with 
          | (1, tt) => 68
          | _ => 500
          end,
          returnGen (MkColor_ctor_Tree_ctor_Tree_ctor Ctor_R Ctor_E Ctor_E)
        );
        (
          match (size, tt) with 
          | (1, tt) => 64
          | _ => 500
          end,
          returnGen (MkColor_ctor_Tree_ctor_Tree_ctor Ctor_B Ctor_E Ctor_E)
        );
        (
          match (size, tt) with 
          | (1, tt) => 37
          | _ => 500
          end,
          returnGen (MkColor_ctor_Tree_ctor_Tree_ctor Ctor_R Ctor_T Ctor_E)
        );
        (
          match (size, tt) with 
          | (1, tt) => 49
          | _ => 500
          end,
          returnGen (MkColor_ctor_Tree_ctor_Tree_ctor Ctor_B Ctor_T Ctor_E)
        );
        (
          match (size, tt) with 
          | (1, tt) => 38
          | _ => 500
          end,
          returnGen (MkColor_ctor_Tree_ctor_Tree_ctor Ctor_R Ctor_E Ctor_T)
        );
        (
          match (size, tt) with 
          | (1, tt) => 47
          | _ => 500
          end,
          returnGen (MkColor_ctor_Tree_ctor_Tree_ctor Ctor_B Ctor_E Ctor_T)
        );
        (
          match (size, tt) with 
          | (1, tt) => 42
          | _ => 500
          end,
          returnGen (MkColor_ctor_Tree_ctor_Tree_ctor Ctor_R Ctor_T Ctor_T)
        );
        (
          match (size, tt) with 
          | (1, tt) => 44
          | _ => 500
          end,
          returnGen (MkColor_ctor_Tree_ctor_Tree_ctor Ctor_B Ctor_T Ctor_T)
        )
      ]) (fun param_variantis =>
      let '(MkColor_ctor_Tree_ctor_Tree_ctor param1_ctor param2_ctor param5_ctor) := param_variantis in
      bindGen (gen_Color param1_ctor 0 )
      (fun p1 : Color =>
      bindGen (gen_Tree size' param2_ctor )
      (fun p2 : Tree =>
      let weight_1 :=
      match (size, tt) with 
      | (1, tt) => 51
      | _ => 500
      end
      in
      bindGen (freq [
        (weight_1, returnGen 1%Z);
        (100-weight_1, returnGen 0%Z)
      ]) (fun n1 =>
      let weight_2 :=
      match (size, tt) with 
      | (1, tt) => 46
      | _ => 500
      end
      in
      bindGen (freq [
        (weight_2, returnGen 2%Z);
        (100-weight_2, returnGen 0%Z)
      ]) (fun n2 =>
      let weight_4 :=
      match (size, tt) with 
      | (1, tt) => 60
      | _ => 500
      end
      in
      bindGen (freq [
        (weight_4, returnGen 4%Z);
        (100-weight_4, returnGen 0%Z)
      ]) (fun n4 =>
      let p3 := (n1 + n2 + n4)%Z in 
      let weight_1 :=
      match (size, tt) with 
      | (1, tt) => 39
      | _ => 500
      end
      in
      bindGen (freq [
        (weight_1, returnGen 1%Z);
        (100-weight_1, returnGen 0%Z)
      ]) (fun n1 =>
      let weight_2 :=
      match (size, tt) with 
      | (1, tt) => 57
      | _ => 500
      end
      in
      bindGen (freq [
        (weight_2, returnGen 2%Z);
        (100-weight_2, returnGen 0%Z)
      ]) (fun n2 =>
      let weight_4 :=
      match (size, tt) with 
      | (1, tt) => 59
      | _ => 500
      end
      in
      bindGen (freq [
        (weight_4, returnGen 4%Z);
        (100-weight_4, returnGen 0%Z)
      ]) (fun n4 =>
      let p4 := (n1 + n2 + n4)%Z in 
      bindGen (gen_Tree size' param5_ctor )
      (fun p5 : Tree =>
      returnGen (T p1 p2 p3 p4 p5)))))))))))
  end
  end.

Definition gSized :=
  bindGen (freq [
    (
      match (tt) with 
      | (tt) => 17
      end,
      returnGen Ctor_E
    );
    (
      match (tt) with 
      | (tt) => 72
      end,
      returnGen Ctor_T
    )
  ]) (fun init_ctor =>
  gen_Tree 1 init_ctor ).

(* --------------------- Tests --------------------- *)

Definition test_prop_InsertValid :=  
    forAll gSized (fun t =>    
    forAll arbitrary (fun k =>
    forAll arbitrary (fun v =>
        (prop_InsertValid t k v)))).

(*! QuickChick test_prop_InsertValid. *)

Definition test_prop_DeleteValid :=  
    forAll gSized (fun t =>    
    forAll arbitrary (fun k =>
        prop_DeleteValid t k)).

(*! QuickChick test_prop_DeleteValid. *)

Definition test_prop_InsertPost :=  
    forAll gSized (fun t =>    
    forAll arbitrary (fun k =>
    forAll arbitrary (fun k' =>
     forAll arbitrary (fun v =>
        prop_InsertPost t k k' v)))).

(*! QuickChick test_prop_InsertPost. *)

Definition test_prop_DeletePost := 
    forAll gSized (fun t =>    
    forAll arbitrary (fun k =>
    forAll arbitrary (fun k' =>
        prop_DeletePost t k k'))).

(*! QuickChick test_prop_DeletePost. *)
    
Definition test_prop_InsertModel :=  
    forAll gSized (fun t =>    
    forAll arbitrary (fun k =>
    forAll arbitrary (fun v =>
        prop_InsertModel t k v))).

(*! QuickChick test_prop_InsertModel. *)
    
Definition test_prop_DeleteModel :=  
    forAll gSized (fun t =>    
    forAll arbitrary (fun k =>
            prop_DeleteModel t k)).

(*! QuickChick test_prop_DeleteModel. *)

Definition test_prop_InsertInsert :=  
    forAll gSized (fun t =>    
    forAll arbitrary (fun k =>
    forAll arbitrary (fun k' =>
    forAll arbitrary (fun v =>
    forAll arbitrary (fun v' =>     
        prop_InsertInsert t k k' v v'))))).

(*! QuickChick test_prop_InsertInsert. *)
    
Definition test_prop_InsertDelete := 
    forAll gSized (fun t =>    
    forAll arbitrary (fun k =>
    forAll arbitrary (fun k' =>
    forAll arbitrary (fun v =>
        prop_InsertDelete t k k' v)))).

(*! QuickChick test_prop_InsertDelete. *)
    
Definition test_prop_DeleteInsert := 
    forAll gSized (fun t =>    
    forAll arbitrary (fun k =>
    forAll arbitrary (fun k' =>
    forAll arbitrary (fun v' =>
        prop_DeleteInsert t k k' v')))).

(*! QuickChick test_prop_DeleteInsert. *)
    
Definition test_prop_DeleteDelete :=  
    forAll gSized (fun t =>    
    forAll arbitrary (fun k =>
    forAll arbitrary (fun k' =>
        prop_DeleteDelete t k k'))).

(*! QuickChick test_prop_DeleteDelete. *)
          
