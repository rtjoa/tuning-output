From QuickChick Require Import QuickChick. Import QcNotation.
From Coq Require Import List. Import ListNotations.
From Coq Require Import ZArith.
From ExtLib Require Import Monad.
Import MonadNotation.

From BST Require Import Impl.
From BST Require Import Spec.

Fixpoint manual_gen_tree (size : nat) (last_callsite : nat) : G Tree := 
  match size with
  | 0 => returnGen E
  | S size' =>
      let weight_leaf := match (size,last_callsite) with 
         | (1, 10) => 542
         | (1, 11) => 534
         | (2, 10) => 845
         | (2, 11) => 838
         | (3, 10) => 999
         | (3, 11) => 999
         | (4, 10) => 28
         | (4, 11) => 95
         | (5, 20) => 2
         | _ => 500
         end in
      freq [
      (1,
      returnGen E);
      (1,
      bindGen (manual_gen_tree size' 10)
        (fun p0 : Tree =>
         let weight_1 := match (size,last_callsite) with 
         | (1, 10) => 500
         | (1, 11) => 489
         | (2, 10) => 490
         | (2, 11) => 503
         | (3, 10) => 454
         | (3, 11) => 520
         | (4, 10) => 481
         | (4, 11) => 407
         | (5, 20) => 445
         | _ => 500
         end in
         let weight_2 := match (size,last_callsite) with 
         | (1, 10) => 500
         | (1, 11) => 497
         | (2, 10) => 490
         | (2, 11) => 491
         | (3, 10) => 457
         | (3, 11) => 555
         | (4, 10) => 447
         | (4, 11) => 516
         | (5, 20) => 499
         | _ => 500
         end in
         let weight_4 := match (size,last_callsite) with 
         | (1, 10) => 493
         | (1, 11) => 496
         | (2, 10) => 490
         | (2, 11) => 485
         | (3, 10) => 481
         | (3, 11) => 492
         | (4, 10) => 536
         | (4, 11) => 594
         | (5, 20) => 351
         | _ => 500
         end in
         let weight_8 := match (size,last_callsite) with 
         | (1, 10) => 493
         | (1, 11) => 489
         | (2, 10) => 495
         | (2, 11) => 502
         | (3, 10) => 478
         | (3, 11) => 565
         | (4, 10) => 575
         | (4, 11) => 452
         | (5, 20) => 510
         | _ => 500
         end in
         let weight_16 := match (size,last_callsite) with 
         | (1, 10) => 493
         | (1, 11) => 497
         | (2, 10) => 495
         | (2, 11) => 504
         | (3, 10) => 458
         | (3, 11) => 593
         | (4, 10) => 485
         | (4, 11) => 996
         | (5, 20) => 3
         | _ => 500
         end in
         let weight_32 := match (size,last_callsite) with 
         | (1, 10) => 507
         | (1, 11) => 503
         | (2, 10) => 497
         | (2, 11) => 507
         | (3, 10) => 471
         | (3, 11) => 485
         | (4, 10) => 1
         | (4, 11) => 999
         | (5, 20) => 999
         | _ => 500
         end in
bindGen (freq [ (weight_1, returnGen 1); (1000-weight_1, returnGen 0)])
(fun n1 : nat => 
bindGen (freq [ (weight_2, returnGen 2); (1000-weight_2, returnGen 0)])
(fun n2 : nat => 
bindGen (freq [ (weight_4, returnGen 4); (1000-weight_4, returnGen 0)])
(fun n4 : nat => 
bindGen (freq [ (weight_8, returnGen 8); (1000-weight_8, returnGen 0)])
(fun n8 : nat => 
bindGen (freq [ (weight_16, returnGen 16); (1000-weight_16, returnGen 0)])
(fun n16 : nat => 
bindGen (freq [ (weight_32, returnGen 32); (1000-weight_32, returnGen 0)])
(fun n32 : nat => 
let p1 := n1+n2+n4+n8+n16+n32 in
            bindGen arbitrary
              (fun p2 : nat =>
               bindGen (manual_gen_tree size' 11)
                 (fun p3 : Tree => returnGen (T p0 p1 p2 p3)))
                 )))))) 
                 ))]
  end.

Definition gSized : G Tree :=
  manual_gen_tree 5 20.

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


