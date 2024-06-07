From QuickChick Require Import QuickChick. Import QcNotation.
From Coq Require Import List. Import ListNotations.
From Coq Require Import ZArith.
From ExtLib Require Import Monad.
Import MonadNotation.

From BST Require Import Impl.
From BST Require Import Spec.

Fixpoint genTree (size : nat) (stack1 : nat) (stack2 : nat) : G (Tree) :=
  match size with
  | O  => 
    (* Frequency1 (single-branch) *) 
    (returnGen (E ))
  | S size1 => 
    (* Frequency2 *) (freq [
      (* E *) (match (size, stack1, stack2) with
      | (1, 1, 1) => 50
      | (1, 1, 2) => 50
      | (1, 2, 1) => 50
      | (1, 2, 2) => 50
      | (2, 1, 1) => 50
      | (2, 1, 2) => 50
      | (2, 2, 1) => 50
      | (2, 2, 2) => 50
      | (3, 1, 1) => 56
      | (3, 1, 2) => 56
      | (3, 2, 1) => 55
      | (3, 2, 2) => 55
      | (4, 0, 1) => 78
      | (4, 0, 2) => 79
      | (5, 0, 0) => 7
      | _ => 500
      end,
      (returnGen (E ))); 
      (* T *) (match (size, stack1, stack2) with
      | (1, 1, 1) => 50
      | (1, 1, 2) => 50
      | (1, 2, 1) => 50
      | (1, 2, 2) => 50
      | (2, 1, 1) => 50
      | (2, 1, 2) => 50
      | (2, 2, 1) => 50
      | (2, 2, 2) => 50
      | (3, 1, 1) => 44
      | (3, 1, 2) => 44
      | (3, 2, 1) => 45
      | (3, 2, 2) => 45
      | (4, 0, 1) => 7
      | (4, 0, 2) => 6
      | (5, 0, 0) => 78
      | _ => 500
      end,
      (bindGen (genTree size1 stack2 1) 
      (fun p1 => 
        (bindGen 
        (* GenNat1 *)
        (let _weight_1 := match (size, stack1, stack2) with
        | (1, 1, 1) => 50
        | (1, 1, 2) => 50
        | (1, 2, 1) => 50
        | (1, 2, 2) => 50
        | (2, 1, 1) => 50
        | (2, 1, 2) => 50
        | (2, 2, 1) => 50
        | (2, 2, 2) => 50
        | (3, 1, 1) => 50
        | (3, 1, 2) => 50
        | (3, 2, 1) => 50
        | (3, 2, 2) => 50
        | (4, 0, 1) => 43
        | (4, 0, 2) => 59
        | (5, 0, 0) => 43
        | _ => 500
        end
        in
        bindGen (freq [
          (_weight_1, returnGen 1);
          (100-_weight_1, returnGen 0)
        ]) (fun n1 =>
        (let _weight_2 := match (size, stack1, stack2) with
        | (1, 1, 1) => 50
        | (1, 1, 2) => 50
        | (1, 2, 1) => 50
        | (1, 2, 2) => 50
        | (2, 1, 1) => 50
        | (2, 1, 2) => 50
        | (2, 2, 1) => 50
        | (2, 2, 2) => 50
        | (3, 1, 1) => 50
        | (3, 1, 2) => 50
        | (3, 2, 1) => 50
        | (3, 2, 2) => 50
        | (4, 0, 1) => 48
        | (4, 0, 2) => 50
        | (5, 0, 0) => 48
        | _ => 500
        end
        in
        bindGen (freq [
          (_weight_2, returnGen 2);
          (100-_weight_2, returnGen 0)
        ]) (fun n2 =>
        (let _weight_4 := match (size, stack1, stack2) with
        | (1, 1, 1) => 50
        | (1, 1, 2) => 50
        | (1, 2, 1) => 50
        | (1, 2, 2) => 50
        | (2, 1, 1) => 50
        | (2, 1, 2) => 50
        | (2, 2, 1) => 50
        | (2, 2, 2) => 50
        | (3, 1, 1) => 50
        | (3, 1, 2) => 50
        | (3, 2, 1) => 50
        | (3, 2, 2) => 50
        | (4, 0, 1) => 43
        | (4, 0, 2) => 45
        | (5, 0, 0) => 71
        | _ => 500
        end
        in
        bindGen (freq [
          (_weight_4, returnGen 4);
          (100-_weight_4, returnGen 0)
        ]) (fun n4 =>
        (let _weight_8 := match (size, stack1, stack2) with
        | (1, 1, 1) => 50
        | (1, 1, 2) => 50
        | (1, 2, 1) => 50
        | (1, 2, 2) => 50
        | (2, 1, 1) => 50
        | (2, 1, 2) => 50
        | (2, 2, 1) => 50
        | (2, 2, 2) => 50
        | (3, 1, 1) => 50
        | (3, 1, 2) => 50
        | (3, 2, 1) => 50
        | (3, 2, 2) => 50
        | (4, 0, 1) => 57
        | (4, 0, 2) => 41
        | (5, 0, 0) => 54
        | _ => 500
        end
        in
        bindGen (freq [
          (_weight_8, returnGen 8);
          (100-_weight_8, returnGen 0)
        ]) (fun n8 =>
        (let _weight_16 := match (size, stack1, stack2) with
        | (1, 1, 1) => 50
        | (1, 1, 2) => 50
        | (1, 2, 1) => 50
        | (1, 2, 2) => 50
        | (2, 1, 1) => 50
        | (2, 1, 2) => 50
        | (2, 2, 1) => 50
        | (2, 2, 2) => 50
        | (3, 1, 1) => 50
        | (3, 1, 2) => 50
        | (3, 2, 1) => 50
        | (3, 2, 2) => 50
        | (4, 0, 1) => 48
        | (4, 0, 2) => 55
        | (5, 0, 0) => 63
        | _ => 500
        end
        in
        bindGen (freq [
          (_weight_16, returnGen 16);
          (100-_weight_16, returnGen 0)
        ]) (fun n16 =>
        (let _weight_32 := match (size, stack1, stack2) with
        | (1, 1, 1) => 50
        | (1, 1, 2) => 50
        | (1, 2, 1) => 50
        | (1, 2, 2) => 50
        | (2, 1, 1) => 50
        | (2, 1, 2) => 50
        | (2, 2, 1) => 50
        | (2, 2, 2) => 50
        | (3, 1, 1) => 50
        | (3, 1, 2) => 50
        | (3, 2, 1) => 50
        | (3, 2, 2) => 50
        | (4, 0, 1) => 48
        | (4, 0, 2) => 55
        | (5, 0, 0) => 64
        | _ => 500
        end
        in
        bindGen (freq [
          (_weight_32, returnGen 32);
          (100-_weight_32, returnGen 0)
        ]) (fun n32 =>
          returnGen (n1 + n2 + n4 + n8 + n16 + n32)
        )))))))))))) 
        (fun p2 => 
          (bindGen 
          (* GenNat2 *)
          (let _weight_1 := match (size, stack1, stack2) with
          | (1, 1, 1) => 50
          | (1, 1, 2) => 50
          | (1, 2, 1) => 50
          | (1, 2, 2) => 50
          | (2, 1, 1) => 50
          | (2, 1, 2) => 50
          | (2, 2, 1) => 50
          | (2, 2, 2) => 50
          | (3, 1, 1) => 50
          | (3, 1, 2) => 50
          | (3, 2, 1) => 50
          | (3, 2, 2) => 50
          | (4, 0, 1) => 52
          | (4, 0, 2) => 50
          | (5, 0, 0) => 57
          | _ => 500
          end
          in
          bindGen (freq [
            (_weight_1, returnGen 1);
            (100-_weight_1, returnGen 0)
          ]) (fun n1 =>
          (let _weight_2 := match (size, stack1, stack2) with
          | (1, 1, 1) => 50
          | (1, 1, 2) => 50
          | (1, 2, 1) => 50
          | (1, 2, 2) => 50
          | (2, 1, 1) => 50
          | (2, 1, 2) => 50
          | (2, 2, 1) => 50
          | (2, 2, 2) => 50
          | (3, 1, 1) => 50
          | (3, 1, 2) => 50
          | (3, 2, 1) => 50
          | (3, 2, 2) => 50
          | (4, 0, 1) => 57
          | (4, 0, 2) => 59
          | (5, 0, 0) => 51
          | _ => 500
          end
          in
          bindGen (freq [
            (_weight_2, returnGen 2);
            (100-_weight_2, returnGen 0)
          ]) (fun n2 =>
          (let _weight_4 := match (size, stack1, stack2) with
          | (1, 1, 1) => 50
          | (1, 1, 2) => 50
          | (1, 2, 1) => 50
          | (1, 2, 2) => 50
          | (2, 1, 1) => 50
          | (2, 1, 2) => 50
          | (2, 2, 1) => 50
          | (2, 2, 2) => 50
          | (3, 1, 1) => 50
          | (3, 1, 2) => 50
          | (3, 2, 1) => 50
          | (3, 2, 2) => 50
          | (4, 0, 1) => 53
          | (4, 0, 2) => 59
          | (5, 0, 0) => 73
          | _ => 500
          end
          in
          bindGen (freq [
            (_weight_4, returnGen 4);
            (100-_weight_4, returnGen 0)
          ]) (fun n4 =>
          (let _weight_8 := match (size, stack1, stack2) with
          | (1, 1, 1) => 50
          | (1, 1, 2) => 50
          | (1, 2, 1) => 50
          | (1, 2, 2) => 50
          | (2, 1, 1) => 50
          | (2, 1, 2) => 50
          | (2, 2, 1) => 50
          | (2, 2, 2) => 50
          | (3, 1, 1) => 50
          | (3, 1, 2) => 50
          | (3, 2, 1) => 50
          | (3, 2, 2) => 50
          | (4, 0, 1) => 47
          | (4, 0, 2) => 45
          | (5, 0, 0) => 43
          | _ => 500
          end
          in
          bindGen (freq [
            (_weight_8, returnGen 8);
            (100-_weight_8, returnGen 0)
          ]) (fun n8 =>
          (let _weight_16 := match (size, stack1, stack2) with
          | (1, 1, 1) => 50
          | (1, 1, 2) => 50
          | (1, 2, 1) => 50
          | (1, 2, 2) => 50
          | (2, 1, 1) => 50
          | (2, 1, 2) => 50
          | (2, 2, 1) => 50
          | (2, 2, 2) => 50
          | (3, 1, 1) => 50
          | (3, 1, 2) => 50
          | (3, 2, 1) => 50
          | (3, 2, 2) => 50
          | (4, 0, 1) => 43
          | (4, 0, 2) => 50
          | (5, 0, 0) => 60
          | _ => 500
          end
          in
          bindGen (freq [
            (_weight_16, returnGen 16);
            (100-_weight_16, returnGen 0)
          ]) (fun n16 =>
          (let _weight_32 := match (size, stack1, stack2) with
          | (1, 1, 1) => 50
          | (1, 1, 2) => 50
          | (1, 2, 1) => 50
          | (1, 2, 2) => 50
          | (2, 1, 1) => 50
          | (2, 1, 2) => 50
          | (2, 2, 1) => 50
          | (2, 2, 2) => 50
          | (3, 1, 1) => 50
          | (3, 1, 2) => 50
          | (3, 2, 1) => 50
          | (3, 2, 2) => 50
          | (4, 0, 1) => 56
          | (4, 0, 2) => 59
          | (5, 0, 0) => 51
          | _ => 500
          end
          in
          bindGen (freq [
            (_weight_32, returnGen 32);
            (100-_weight_32, returnGen 0)
          ]) (fun n32 =>
            returnGen (n1 + n2 + n4 + n8 + n16 + n32)
          )))))))))))) 
          (fun p3 => 
            (bindGen (genTree size1 stack2 2) 
            (fun p4 => 
              (returnGen (T p1 p2 p3 p4)))))))))))])
  end.

Definition gSized :=
  (genTree 5 0 0).

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
     
