Require Import ZArith.
From QuickChick Require Import QuickChick.
From ExtLib Require Import Monad.
From ExtLib.Data.Monads Require Import OptionMonad.
Import QcNotation.
Import MonadNotation.
From Coq Require Import List.
Import ListNotations.

From RBT Require Import Impl Spec.

Fixpoint manual_gen_tree (size : nat) (parent_color : Color) (stack1 : nat) (stack2 : nat) :=
    let weight_red := match (size,parent_color,(stack1, stack2)) with 
         | (1, B, (10, 10)) => 500
         | (1, B, (10, 11)) => 500
         | (1, B, (11, 10)) => 500
         | (1, B, (11, 11)) => 500
         | (1, R, (10, 10)) => 500
         | (1, R, (10, 11)) => 500
         | (1, R, (11, 10)) => 500
         | (1, R, (11, 11)) => 500
         | (2, B, (0, 10)) => 500
         | (2, B, (0, 11)) => 500
         | (2, R, (0, 10)) => 500
         | (2, R, (0, 11)) => 500
         | (3, B, (0, 0)) => 500
         | _ => 500
         end in
    let weight_leaf := match (size,parent_color,(stack1, stack2)) with 
         | (1, B, (10, 10)) => 500
         | (1, B, (10, 11)) => 500
         | (1, B, (11, 10)) => 500
         | (1, B, (11, 11)) => 500
         | (1, R, (10, 10)) => 500
         | (1, R, (10, 11)) => 500
         | (1, R, (11, 10)) => 500
         | (1, R, (11, 11)) => 500
         | (2, B, (0, 10)) => 502
         | (2, B, (0, 11)) => 502
         | (2, R, (0, 10)) => 502
         | (2, R, (0, 11)) => 502
         | (3, B, (0, 0)) => 498
         | _ => 500
         end in
    match size with
    | 0 => returnGen E
    | S size' =>
        freq [ (weight_leaf, returnGen E);
        (1000 - weight_leaf,
        bindGen (freq [ (weight_red, returnGen R); (1000-weight_red, returnGen B)])
          (fun p0 : Color =>
           bindGen (manual_gen_tree size' p0 (stack2 : nat) 10)
             (fun p1 : Tree =>
         let weight_1 := match (size,parent_color,(stack1, stack2)) with 
         | (1, B, (10, 10)) => 500
         | (1, B, (10, 11)) => 500
         | (1, B, (11, 10)) => 500
         | (1, B, (11, 11)) => 500
         | (1, R, (10, 10)) => 500
         | (1, R, (10, 11)) => 500
         | (1, R, (11, 10)) => 500
         | (1, R, (11, 11)) => 500
         | (2, B, (0, 10)) => 500
         | (2, B, (0, 11)) => 500
         | (2, R, (0, 10)) => 500
         | (2, R, (0, 11)) => 500
         | (3, B, (0, 0)) => 499
         | _ => 500
         end in
        bindGen (freq [ (weight_1, returnGen (1%Z)); (1000-weight_1, returnGen 0%Z)])
        (fun n1 : Z =>  
         let weight_2 := match (size,parent_color,(stack1, stack2)) with 
         | (1, B, (10, 10)) => 500
         | (1, B, (10, 11)) => 500
         | (1, B, (11, 10)) => 500
         | (1, B, (11, 11)) => 500
         | (1, R, (10, 10)) => 500
         | (1, R, (10, 11)) => 500
         | (1, R, (11, 10)) => 500
         | (1, R, (11, 11)) => 500
         | (2, B, (0, 10)) => 500
         | (2, B, (0, 11)) => 500
         | (2, R, (0, 10)) => 500
         | (2, R, (0, 11)) => 500
         | (3, B, (0, 0)) => 500
         | _ => 500
         end in
        bindGen (freq [ (weight_2, returnGen (2%Z)); (1000-weight_2, returnGen 0%Z)])
        (fun n2 : Z =>  
         let weight_4 := match (size,parent_color,(stack1, stack2)) with 
         | (1, B, (10, 10)) => 500
         | (1, B, (10, 11)) => 500
         | (1, B, (11, 10)) => 500
         | (1, B, (11, 11)) => 500
         | (1, R, (10, 10)) => 500
         | (1, R, (10, 11)) => 500
         | (1, R, (11, 10)) => 500
         | (1, R, (11, 11)) => 500
         | (2, B, (0, 10)) => 500
         | (2, B, (0, 11)) => 500
         | (2, R, (0, 10)) => 500
         | (2, R, (0, 11)) => 500
         | (3, B, (0, 0)) => 501
         | _ => 500
         end in
        bindGen (freq [ (weight_4, returnGen (4%Z)); (1000-weight_4, returnGen 0%Z)])
        (fun n4 : Z =>  
         let weight_8 := match (size,parent_color,(stack1, stack2)) with 
         | (1, B, (10, 10)) => 500
         | (1, B, (10, 11)) => 500
         | (1, B, (11, 10)) => 500
         | (1, B, (11, 11)) => 500
         | (1, R, (10, 10)) => 500
         | (1, R, (10, 11)) => 500
         | (1, R, (11, 10)) => 500
         | (1, R, (11, 11)) => 500
         | (2, B, (0, 10)) => 500
         | (2, B, (0, 11)) => 500
         | (2, R, (0, 10)) => 500
         | (2, R, (0, 11)) => 500
         | (3, B, (0, 0)) => 501
         | _ => 500
         end in
        bindGen (freq [ (weight_8, returnGen (8%Z)); (1000-weight_8, returnGen 0%Z)])
        (fun n8 : Z =>  
         let weight_16 := match (size,parent_color,(stack1, stack2)) with 
         | (1, B, (10, 10)) => 500
         | (1, B, (10, 11)) => 500
         | (1, B, (11, 10)) => 500
         | (1, B, (11, 11)) => 500
         | (1, R, (10, 10)) => 500
         | (1, R, (10, 11)) => 500
         | (1, R, (11, 10)) => 500
         | (1, R, (11, 11)) => 500
         | (2, B, (0, 10)) => 500
         | (2, B, (0, 11)) => 500
         | (2, R, (0, 10)) => 500
         | (2, R, (0, 11)) => 500
         | (3, B, (0, 0)) => 501
         | _ => 500
         end in
        bindGen (freq [ (weight_16, returnGen (16%Z)); (1000-weight_16, returnGen 0%Z)])
        (fun n16 : Z =>  
         let weight_32 := match (size,parent_color,(stack1, stack2)) with 
         | (1, B, (10, 10)) => 500
         | (1, B, (10, 11)) => 500
         | (1, B, (11, 10)) => 500
         | (1, B, (11, 11)) => 500
         | (1, R, (10, 10)) => 500
         | (1, R, (10, 11)) => 500
         | (1, R, (11, 10)) => 500
         | (1, R, (11, 11)) => 500
         | (2, B, (0, 10)) => 500
         | (2, B, (0, 11)) => 500
         | (2, R, (0, 10)) => 500
         | (2, R, (0, 11)) => 500
         | (3, B, (0, 0)) => 499
         | _ => 500
         end in
        bindGen (freq [ (weight_32, returnGen (32%Z)); (1000-weight_32, returnGen 0%Z)])
        (fun n32 : Z =>  
let p2 := (n1+n2+n4+n8+n16+n32)%Z in
                  bindGen arbitrary
                    (fun p3 : Z =>
                     bindGen (manual_gen_tree size' p0 (stack2 : nat) 11)
                       (fun p4 : Tree => returnGen (T p0 p1 p2 p3 p4))
                      )))))) 
                       ))))]
         end.

#[global]
Instance genTree : GenSized (Tree) := 
  {| arbitrarySized n := manual_gen_tree 3 B 0 0 |}.

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


