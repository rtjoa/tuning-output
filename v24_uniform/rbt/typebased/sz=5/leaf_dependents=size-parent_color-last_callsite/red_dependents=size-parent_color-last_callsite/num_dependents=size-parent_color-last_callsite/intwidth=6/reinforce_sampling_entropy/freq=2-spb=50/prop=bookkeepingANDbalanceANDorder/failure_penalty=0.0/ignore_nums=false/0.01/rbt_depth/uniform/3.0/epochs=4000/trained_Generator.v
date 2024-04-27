Require Import ZArith.
From QuickChick Require Import QuickChick.
From ExtLib Require Import Monad.
From ExtLib.Data.Monads Require Import OptionMonad.
Import QcNotation.
Import MonadNotation.
From Coq Require Import List.
Import ListNotations.

From RBT Require Import Impl Spec.

Definition manual_gen_tree :=
    fun s : nat =>
    (let
       fix arb_aux (size : nat) (parent_color : Color) (last_callsite : nat) : G Tree :=
         let weight_red := match (size,parent_color,last_callsite) with 
         | (1, B, 20) => 500
         | (1, B, 30) => 500
         | (1, R, 20) => 500
         | (1, R, 30) => 500
         | (2, B, 20) => 500
         | (2, B, 30) => 500
         | (2, R, 20) => 500
         | (2, R, 30) => 500
         | (3, B, 20) => 509
         | (3, B, 30) => 506
         | (3, R, 20) => 500
         | (3, R, 30) => 500
         | (4, B, 20) => 827
         | (4, B, 30) => 801
         | (4, R, 20) => 310
         | (4, R, 30) => 310
         | (5, B, 10) => 94
         | _ => 500
         end in
         let weight_leaf := match (size,parent_color,last_callsite) with 
         | (1, B, 20) => 784
         | (1, B, 30) => 784
         | (1, R, 20) => 784
         | (1, R, 30) => 784
         | (2, B, 20) => 690
         | (2, B, 30) => 690
         | (2, R, 20) => 698
         | (2, R, 30) => 698
         | (3, B, 20) => 136
         | (3, B, 30) => 140
         | (3, R, 20) => 652
         | (3, R, 30) => 652
         | (4, B, 20) => 377
         | (4, B, 30) => 452
         | (4, R, 20) => 678
         | (4, R, 30) => 678
         | (5, B, 10) => 41
         | _ => 500
         end in
         let weight_1 := match (size,parent_color,last_callsite) with 
         | (1, B, 20) => 500
         | (1, B, 30) => 500
         | (1, R, 20) => 500
         | (1, R, 30) => 500
         | (2, B, 20) => 500
         | (2, B, 30) => 500
         | (2, R, 20) => 500
         | (2, R, 30) => 500
         | (3, B, 20) => 501
         | (3, B, 30) => 501
         | (3, R, 20) => 500
         | (3, R, 30) => 500
         | (4, B, 20) => 466
         | (4, B, 30) => 539
         | (4, R, 20) => 496
         | (4, R, 30) => 502
         | (5, B, 10) => 543
         | _ => 500
         end in
         let weight_2 := match (size,parent_color,last_callsite) with 
         | (1, B, 20) => 500
         | (1, B, 30) => 500
         | (1, R, 20) => 500
         | (1, R, 30) => 500
         | (2, B, 20) => 500
         | (2, B, 30) => 500
         | (2, R, 20) => 500
         | (2, R, 30) => 500
         | (3, B, 20) => 496
         | (3, B, 30) => 501
         | (3, R, 20) => 500
         | (3, R, 30) => 500
         | (4, B, 20) => 407
         | (4, B, 30) => 546
         | (4, R, 20) => 497
         | (4, R, 30) => 495
         | (5, B, 10) => 475
         | _ => 500
         end in
         let weight_4 := match (size,parent_color,last_callsite) with 
         | (1, B, 20) => 500
         | (1, B, 30) => 500
         | (1, R, 20) => 500
         | (1, R, 30) => 500
         | (2, B, 20) => 500
         | (2, B, 30) => 500
         | (2, R, 20) => 500
         | (2, R, 30) => 500
         | (3, B, 20) => 494
         | (3, B, 30) => 504
         | (3, R, 20) => 500
         | (3, R, 30) => 500
         | (4, B, 20) => 392
         | (4, B, 30) => 630
         | (4, R, 20) => 499
         | (4, R, 30) => 499
         | (5, B, 10) => 510
         | _ => 500
         end in
         let weight_8 := match (size,parent_color,last_callsite) with 
         | (1, B, 20) => 500
         | (1, B, 30) => 500
         | (1, R, 20) => 500
         | (1, R, 30) => 500
         | (2, B, 20) => 500
         | (2, B, 30) => 500
         | (2, R, 20) => 500
         | (2, R, 30) => 500
         | (3, B, 20) => 494
         | (3, B, 30) => 504
         | (3, R, 20) => 500
         | (3, R, 30) => 500
         | (4, B, 20) => 281
         | (4, B, 30) => 709
         | (4, R, 20) => 497
         | (4, R, 30) => 497
         | (5, B, 10) => 517
         | _ => 500
         end in
         let weight_16 := match (size,parent_color,last_callsite) with 
         | (1, B, 20) => 500
         | (1, B, 30) => 500
         | (1, R, 20) => 500
         | (1, R, 30) => 500
         | (2, B, 20) => 500
         | (2, B, 30) => 500
         | (2, R, 20) => 500
         | (2, R, 30) => 500
         | (3, B, 20) => 497
         | (3, B, 30) => 504
         | (3, R, 20) => 500
         | (3, R, 30) => 500
         | (4, B, 20) => 176
         | (4, B, 30) => 831
         | (4, R, 20) => 493
         | (4, R, 30) => 505
         | (5, B, 10) => 492
         | _ => 500
         end in
         let weight_32 := match (size,parent_color,last_callsite) with 
         | (1, B, 20) => 500
         | (1, B, 30) => 500
         | (1, R, 20) => 500
         | (1, R, 30) => 500
         | (2, B, 20) => 500
         | (2, B, 30) => 500
         | (2, R, 20) => 500
         | (2, R, 30) => 500
         | (3, B, 20) => 506
         | (3, B, 30) => 504
         | (3, R, 20) => 500
         | (3, R, 30) => 500
         | (4, B, 20) => 73
         | (4, B, 30) => 922
         | (4, R, 20) => 490
         | (4, R, 30) => 507
         | (5, B, 10) => 564
         | _ => 500
         end in
         match size with
         | 0 => returnGen E
         | S size' =>
             freq [ (weight_leaf, returnGen E);
             (1000 - weight_leaf,
             bindGen (freq [ (weight_red, returnGen R); (1000-weight_red, returnGen B)])
               (fun p0 : Color =>
                bindGen (arb_aux size' p0 20)
                  (fun p1 : Tree =>

bindGen (freq [ (weight_1, returnGen (1%Z)); (1000-weight_1, returnGen 0%Z)])
(fun n1 : Z => 
bindGen (freq [ (weight_2, returnGen (2%Z)); (1000-weight_2, returnGen 0%Z)])
(fun n2 : Z => 
bindGen (freq [ (weight_4, returnGen (4%Z)); (1000-weight_4, returnGen 0%Z)])
(fun n4 : Z => 
bindGen (freq [ (weight_8, returnGen (8%Z)); (1000-weight_8, returnGen 0%Z)])
(fun n8 : Z => 
bindGen (freq [ (weight_16, returnGen (16%Z)); (1000-weight_16, returnGen 0%Z)])
(fun n16 : Z => 
bindGen (freq [ (weight_32, returnGen (32%Z)); (1000-weight_32, returnGen 0%Z)])
(fun n32 : Z => 
                      bindGen arbitrary
                        (fun p3 : Z =>
let p2 := (n1+n2+n4+n8+n16+n32)%Z in
                         bindGen (arb_aux size' p0 30)
                           (fun p4 : Tree => returnGen (T p0 p1 p2 p3 p4))
                          )))))) 
                           ))))]
         end in
     arb_aux) s.

#[global]
Instance genTree : GenSized (Tree) := 
  {| arbitrarySized n := manual_gen_tree 5 B 10 |}.

(* --------------------- Tests --------------------- *)

Definition test_prop_InsertValid :=  
    forAll arbitrary (fun t =>    
    forAll arbitrary (fun k =>
    forAll arbitrary (fun v =>
        (prop_InsertValid t k v)))).

(*! QuickChick test_prop_InsertValid. *)

Definition test_prop_DeleteValid :=  
    forAll arbitrary (fun t =>    
    forAll arbitrary (fun k =>
        prop_DeleteValid t k)).

(*! QuickChick test_prop_DeleteValid. *)

Definition test_prop_InsertPost :=  
    forAll arbitrary (fun t =>    
    forAll arbitrary (fun k =>
    forAll arbitrary (fun k' =>
     forAll arbitrary (fun v =>
        prop_InsertPost t k k' v)))).

(*! QuickChick test_prop_InsertPost. *)

Definition test_prop_DeletePost := 
    forAll arbitrary (fun t =>    
    forAll arbitrary (fun k =>
    forAll arbitrary (fun k' =>
        prop_DeletePost t k k'))).

(*! QuickChick test_prop_DeletePost. *)
    
Definition test_prop_InsertModel :=  
    forAll arbitrary (fun t =>    
    forAll arbitrary (fun k =>
    forAll arbitrary (fun v =>
        prop_InsertModel t k v))).

(*! QuickChick test_prop_InsertModel. *)
    
Definition test_prop_DeleteModel :=  
    forAll arbitrary (fun t =>    
    forAll arbitrary (fun k =>
            prop_DeleteModel t k)).

(*! QuickChick test_prop_DeleteModel. *)

Definition test_prop_InsertInsert :=  
    forAll arbitrary (fun t =>    
    forAll arbitrary (fun k =>
    forAll arbitrary (fun k' =>
    forAll arbitrary (fun v =>
    forAll arbitrary (fun v' =>     
        prop_InsertInsert t k k' v v'))))).

(*! QuickChick test_prop_InsertInsert. *)
    
Definition test_prop_InsertDelete := 
    forAll arbitrary (fun t =>    
    forAll arbitrary (fun k =>
    forAll arbitrary (fun k' =>
    forAll arbitrary (fun v =>
        prop_InsertDelete t k k' v)))).

(*! QuickChick test_prop_InsertDelete. *)
    
Definition test_prop_DeleteInsert := 
    forAll arbitrary (fun t =>    
    forAll arbitrary (fun k =>
    forAll arbitrary (fun k' =>
    forAll arbitrary (fun v' =>
        prop_DeleteInsert t k k' v')))).

(*! QuickChick test_prop_DeleteInsert. *)
    
Definition test_prop_DeleteDelete :=  
    forAll arbitrary (fun t =>    
    forAll arbitrary (fun k =>
    forAll arbitrary (fun k' =>
        prop_DeleteDelete t k k'))).

(*! QuickChick test_prop_DeleteDelete. *)


