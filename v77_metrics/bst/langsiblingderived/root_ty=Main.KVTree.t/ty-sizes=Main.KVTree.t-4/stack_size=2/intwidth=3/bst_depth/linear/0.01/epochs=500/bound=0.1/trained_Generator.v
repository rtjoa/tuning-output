From QuickChick Require Import QuickChick. Import QcNotation.
From Coq Require Import List. Import ListNotations.
From Coq Require Import ZArith.
From ExtLib Require Import Monad.
Import MonadNotation.

From BST Require Import Impl.
From BST Require Import Spec.

Inductive CtorKVTree :=
  | CtorKVTree_E
  | CtorKVTree_T.

Inductive LeafCtorKVTree :=
  | LeafCtorKVTree_E.

Inductive TupLeafCtorKVTreeLeafCtorKVTree :=
  | MkLeafCtorKVTreeLeafCtorKVTree : LeafCtorKVTree -> LeafCtorKVTree -> TupLeafCtorKVTreeLeafCtorKVTree.

Inductive TupCtorKVTreeCtorKVTree :=
  | MkCtorKVTreeCtorKVTree : CtorKVTree -> CtorKVTree -> TupCtorKVTreeCtorKVTree.

Definition genLeafTree (chosen_ctor : LeafCtorKVTree) (stack1 : nat) (stack2 : nat) : G (Tree) :=
  match chosen_ctor with
  | LeafCtorKVTree_E  => 
    (returnGen (E ))
  end.

Fixpoint genTree (size : nat) (chosen_ctor : CtorKVTree) (stack1 : nat) (stack2 : nat) : G (Tree) :=
  match size with
  | O  => match chosen_ctor with
    | CtorKVTree_E  => 
      (returnGen (E ))
    | CtorKVTree_T  => 
      (bindGen 
      (* Frequency2 (single-branch) *) 
      (returnGen (MkLeafCtorKVTreeLeafCtorKVTree (LeafCtorKVTree_E ) (LeafCtorKVTree_E ))) 
      (fun param_variantis => (let '(MkLeafCtorKVTreeLeafCtorKVTree ctor1 ctor2) := param_variantis in

        (bindGen (genLeafTree ctor1 stack2 1) 
        (fun p1 => 
          (bindGen 
          (* GenNat1 *)
          (let _weight_1 := match (stack1, stack2) with
          | (2, 2) => 50
          | (2, 4) => 50
          | (4, 2) => 50
          | (4, 4) => 50
          | _ => 500
          end
          in
          bindGen (freq [
            (_weight_1, returnGen 1);
            (100-_weight_1, returnGen 0)
          ]) (fun n1 =>
          (let _weight_2 := match (stack1, stack2) with
          | (2, 2) => 50
          | (2, 4) => 50
          | (4, 2) => 50
          | (4, 4) => 50
          | _ => 500
          end
          in
          bindGen (freq [
            (_weight_2, returnGen 2);
            (100-_weight_2, returnGen 0)
          ]) (fun n2 =>
          (let _weight_4 := match (stack1, stack2) with
          | (2, 2) => 50
          | (2, 4) => 50
          | (4, 2) => 50
          | (4, 4) => 50
          | _ => 500
          end
          in
          bindGen (freq [
            (_weight_4, returnGen 4);
            (100-_weight_4, returnGen 0)
          ]) (fun n4 =>
            returnGen (n1 + n2 + n4)
          )))))) 
          (fun p2 => 
            (bindGen 
            (* GenNat3 *)
            (let _weight_1 := match (stack1, stack2) with
            | (2, 2) => 50
            | (2, 4) => 50
            | (4, 2) => 50
            | (4, 4) => 50
            | _ => 500
            end
            in
            bindGen (freq [
              (_weight_1, returnGen 1);
              (100-_weight_1, returnGen 0)
            ]) (fun n1 =>
            (let _weight_2 := match (stack1, stack2) with
            | (2, 2) => 50
            | (2, 4) => 50
            | (4, 2) => 50
            | (4, 4) => 50
            | _ => 500
            end
            in
            bindGen (freq [
              (_weight_2, returnGen 2);
              (100-_weight_2, returnGen 0)
            ]) (fun n2 =>
            (let _weight_4 := match (stack1, stack2) with
            | (2, 2) => 50
            | (2, 4) => 50
            | (4, 2) => 50
            | (4, 4) => 50
            | _ => 500
            end
            in
            bindGen (freq [
              (_weight_4, returnGen 4);
              (100-_weight_4, returnGen 0)
            ]) (fun n4 =>
              returnGen (n1 + n2 + n4)
            )))))) 
            (fun p3 => 
              (bindGen (genLeafTree ctor2 stack2 3) 
              (fun p4 => 
                (returnGen (T p1 p2 p3 p4)))))))))))))
    end
  | S size1 => match chosen_ctor with
    | CtorKVTree_E  => 
      (returnGen (E ))
    | CtorKVTree_T  => 
      (bindGen 
      (* Frequency3 *) (freq [
        (* 1 *) (match (size, stack1, stack2) with
        | (1, 2, 2) => 82
        | (1, 2, 4) => 82
        | (1, 4, 2) => 82
        | (1, 4, 4) => 82
        | (2, 0, 2) => 21
        | (2, 0, 4) => 21
        | (3, 0, 0) => 10
        | _ => 500
        end,
        (returnGen (MkCtorKVTreeCtorKVTree (CtorKVTree_E ) (CtorKVTree_E )))); 
        (* 2 *) (match (size, stack1, stack2) with
        | (1, 2, 2) => 26
        | (1, 2, 4) => 26
        | (1, 4, 2) => 26
        | (1, 4, 4) => 26
        | (2, 0, 2) => 10
        | (2, 0, 4) => 10
        | (3, 0, 0) => 10
        | _ => 500
        end,
        (returnGen (MkCtorKVTreeCtorKVTree (CtorKVTree_T ) (CtorKVTree_E )))); 
        (* 3 *) (match (size, stack1, stack2) with
        | (1, 2, 2) => 26
        | (1, 2, 4) => 26
        | (1, 4, 2) => 26
        | (1, 4, 4) => 26
        | (2, 0, 2) => 10
        | (2, 0, 4) => 10
        | (3, 0, 0) => 10
        | _ => 500
        end,
        (returnGen (MkCtorKVTreeCtorKVTree (CtorKVTree_E ) (CtorKVTree_T )))); 
        (* 4 *) (match (size, stack1, stack2) with
        | (1, 2, 2) => 26
        | (1, 2, 4) => 26
        | (1, 4, 2) => 26
        | (1, 4, 4) => 26
        | (2, 0, 2) => 90
        | (2, 0, 4) => 90
        | (3, 0, 0) => 90
        | _ => 500
        end,
        (returnGen (MkCtorKVTreeCtorKVTree (CtorKVTree_T ) (CtorKVTree_T ))))]) 
      (fun param_variantis => (let '(MkCtorKVTreeCtorKVTree ctor1 ctor2) := param_variantis in

        (bindGen (genTree size1 ctor1 stack2 2) 
        (fun p1 => 
          (bindGen 
          (* GenNat2 *)
          (let _weight_1 := match (size, stack1, stack2) with
          | (1, 2, 2) => 50
          | (1, 2, 4) => 50
          | (1, 4, 2) => 50
          | (1, 4, 4) => 50
          | (2, 0, 2) => 50
          | (2, 0, 4) => 50
          | (3, 0, 0) => 50
          | _ => 500
          end
          in
          bindGen (freq [
            (_weight_1, returnGen 1);
            (100-_weight_1, returnGen 0)
          ]) (fun n1 =>
          (let _weight_2 := match (size, stack1, stack2) with
          | (1, 2, 2) => 50
          | (1, 2, 4) => 50
          | (1, 4, 2) => 50
          | (1, 4, 4) => 50
          | (2, 0, 2) => 50
          | (2, 0, 4) => 50
          | (3, 0, 0) => 50
          | _ => 500
          end
          in
          bindGen (freq [
            (_weight_2, returnGen 2);
            (100-_weight_2, returnGen 0)
          ]) (fun n2 =>
          (let _weight_4 := match (size, stack1, stack2) with
          | (1, 2, 2) => 50
          | (1, 2, 4) => 50
          | (1, 4, 2) => 50
          | (1, 4, 4) => 50
          | (2, 0, 2) => 50
          | (2, 0, 4) => 50
          | (3, 0, 0) => 50
          | _ => 500
          end
          in
          bindGen (freq [
            (_weight_4, returnGen 4);
            (100-_weight_4, returnGen 0)
          ]) (fun n4 =>
            returnGen (n1 + n2 + n4)
          )))))) 
          (fun p2 => 
            (bindGen 
            (* GenNat4 *)
            (let _weight_1 := match (size, stack1, stack2) with
            | (1, 2, 2) => 50
            | (1, 2, 4) => 50
            | (1, 4, 2) => 50
            | (1, 4, 4) => 50
            | (2, 0, 2) => 50
            | (2, 0, 4) => 50
            | (3, 0, 0) => 50
            | _ => 500
            end
            in
            bindGen (freq [
              (_weight_1, returnGen 1);
              (100-_weight_1, returnGen 0)
            ]) (fun n1 =>
            (let _weight_2 := match (size, stack1, stack2) with
            | (1, 2, 2) => 50
            | (1, 2, 4) => 50
            | (1, 4, 2) => 50
            | (1, 4, 4) => 50
            | (2, 0, 2) => 50
            | (2, 0, 4) => 50
            | (3, 0, 0) => 50
            | _ => 500
            end
            in
            bindGen (freq [
              (_weight_2, returnGen 2);
              (100-_weight_2, returnGen 0)
            ]) (fun n2 =>
            (let _weight_4 := match (size, stack1, stack2) with
            | (1, 2, 2) => 50
            | (1, 2, 4) => 50
            | (1, 4, 2) => 50
            | (1, 4, 4) => 50
            | (2, 0, 2) => 50
            | (2, 0, 4) => 50
            | (3, 0, 0) => 50
            | _ => 500
            end
            in
            bindGen (freq [
              (_weight_4, returnGen 4);
              (100-_weight_4, returnGen 0)
            ]) (fun n4 =>
              returnGen (n1 + n2 + n4)
            )))))) 
            (fun p3 => 
              (bindGen (genTree size1 ctor2 stack2 4) 
              (fun p4 => 
                (returnGen (T p1 p2 p3 p4)))))))))))))
    end
  end.

Definition gSized :=

  (bindGen 
  (* Frequency1 *) (freq [
    (* 1 *) (match (tt) with
    | tt => 10
    end,
    (returnGen (CtorKVTree_E ))); 
    (* 2 *) (match (tt) with
    | tt => 90
    end,
    (returnGen (CtorKVTree_T )))]) 
  (fun init_ctor => (genTree 3 init_ctor 0 0))).

Definition manual_shrink_tree := 
fun x : Tree =>
let
  fix aux_shrink (x' : Tree) : list Tree :=
    match x' with
    | E => []
    | T p0 p1 p2 p3 =>
        ([p0] ++
         map (fun shrunk : Tree => T shrunk p1 p2 p3) (aux_shrink p0) ++
         []) ++
        (map (fun shrunk : nat => T p0 shrunk p2 p3) (shrink p1) ++ []) ++
        (map (fun shrunk : nat => T p0 p1 shrunk p3) (shrink p2) ++ []) ++
        ([p3] ++
         map (fun shrunk : Tree => T p0 p1 p2 shrunk) (aux_shrink p3) ++
         []) ++ []
    end in
aux_shrink x.


#[global]
Instance shrTree : Shrink (Tree) := 
{| shrink x := manual_shrink_tree x |}.

Definition test_prop_InsertValid   :=
forAll gSized (fun (t: Tree)  =>
forAll arbitrary (fun (k: nat)  =>
forAll arbitrary (fun (v: nat) =>
prop_InsertValid t k v)))
.

(*! QuickChick test_prop_InsertValid. *)

Definition test_prop_DeleteValid   :=
forAll gSized (fun (t: Tree)  =>
forAll arbitrary (fun (k: nat) =>
prop_DeleteValid t k))
.

(*! QuickChick test_prop_DeleteValid. *)


Definition test_prop_UnionValid    :=
forAll gSized (fun (t1: Tree)  =>
forAll gSized (fun (t2: Tree) =>
prop_UnionValid t1 t2))
.

(*! QuickChick test_prop_UnionValid. *)

Definition test_prop_InsertPost    :=
forAll gSized (fun (t: Tree)  =>
forAll arbitrary (fun (k: nat)  =>
forAll arbitrary (fun (k': nat)  =>
forAll arbitrary (fun (v: nat) =>
prop_InsertPost t k k' v))))
.

(*! QuickChick test_prop_InsertPost. *)

Definition test_prop_DeletePost    :=
forAll gSized (fun (t: Tree)  =>
forAll arbitrary (fun (k: nat)  =>
forAll arbitrary (fun (k': nat) =>
prop_DeletePost t k k')))
.

(*! QuickChick test_prop_DeletePost. *)

Definition test_prop_UnionPost   :=
forAll gSized (fun (t: Tree)  =>
forAll gSized (fun (t': Tree)  =>
forAll arbitrary (fun (k: nat) =>
prop_UnionPost t t' k)))
.

(*! QuickChick test_prop_UnionPost. *)

Definition test_prop_InsertModel   :=
forAll gSized (fun (t: Tree)  =>
forAll arbitrary (fun (k: nat)  =>
forAll arbitrary (fun (v: nat) =>
prop_InsertModel t k v)))
.

(*! QuickChick test_prop_InsertModel. *)

Definition test_prop_DeleteModel   :=
forAll gSized (fun (t: Tree)  =>
forAll arbitrary (fun (k: nat) =>
prop_DeleteModel t k))
.

(*! QuickChick test_prop_DeleteModel. *)

Definition test_prop_UnionModel    :=
forAll gSized (fun (t: Tree)  =>
forAll gSized (fun (t': Tree) =>
prop_UnionModel t t'))
.

(*! QuickChick test_prop_UnionModel. *)

Definition test_prop_InsertInsert    :=
forAll gSized (fun (t: Tree)  =>
forAll arbitrary (fun (k: nat)  =>
forAll arbitrary (fun (k': nat)  =>
forAll arbitrary (fun (v: nat)  =>
forAll arbitrary (fun (v': nat) =>
prop_InsertInsert t k k' v v')))))
.

(*! QuickChick test_prop_InsertInsert. *)

Definition test_prop_InsertDelete    :=
forAll gSized (fun (t: Tree)  =>
forAll arbitrary (fun (k: nat)  =>
forAll arbitrary (fun (k': nat)  =>
forAll arbitrary (fun (v: nat) =>
prop_InsertDelete t k k' v))))
.

(*! QuickChick test_prop_InsertDelete. *)

Definition test_prop_InsertUnion   :=
forAll gSized (fun (t: Tree)  =>
forAll gSized (fun (t': Tree)  =>
forAll arbitrary (fun (k: nat)  =>
forAll arbitrary (fun (v: nat) =>
prop_InsertUnion t t' k v))))
.

(*! QuickChick test_prop_InsertUnion. *)

Definition test_prop_DeleteInsert    :=
forAll gSized (fun (t: Tree)  =>
forAll arbitrary (fun (k: nat)  =>
forAll arbitrary (fun (k': nat)  =>
forAll arbitrary (fun (v': nat) =>
prop_DeleteInsert t k k' v'))))
.

(*! QuickChick test_prop_DeleteInsert. *)

Definition test_prop_DeleteDelete    :=
forAllShrink gSized shrink (fun (t: Tree)  =>
forAllShrink arbitrary shrink (fun (k: nat)  =>
forAllShrink arbitrary shrink (fun (k': nat) =>
whenFail' (fun tt => show (t, k, k', delete k t, delete k' t, delete k (delete k' t), delete k' (delete k t)))
(prop_DeleteDelete t k k'))))
.

(*! QuickChick test_prop_DeleteDelete. *)

Definition test_prop_DeleteUnion   :=
forAll gSized (fun (t: Tree)  =>
forAll gSized (fun (t': Tree)  =>
forAll arbitrary (fun (k: nat) =>
prop_DeleteUnion t t' k)))
.

(*! QuickChick test_prop_DeleteUnion. *)

Definition test_prop_UnionDeleteInsert   :=
forAll gSized (fun (t :Tree)  =>
forAll gSized (fun (t': Tree)  =>
forAll arbitrary (fun (k: nat)  =>
forAll arbitrary (fun (v: nat) =>
prop_UnionDeleteInsert t t' k v))))
.

(*! QuickChick test_prop_UnionDeleteInsert. *)

Definition test_prop_UnionUnionIdem    :=
forAll gSized (fun (t: Tree) =>
prop_UnionUnionIdem t)
.

(*! QuickChick test_prop_UnionUnionIdem. *)

Definition test_prop_UnionUnionAssoc   :=
forAll gSized (fun (t1: Tree)  =>
forAll gSized (fun (t2: Tree)  =>
forAll gSized (fun (t3: Tree) =>
prop_UnionUnionAssoc t1 t2 t3)))
.

(*! QuickChick test_prop_UnionUnionAssoc. *)
     
