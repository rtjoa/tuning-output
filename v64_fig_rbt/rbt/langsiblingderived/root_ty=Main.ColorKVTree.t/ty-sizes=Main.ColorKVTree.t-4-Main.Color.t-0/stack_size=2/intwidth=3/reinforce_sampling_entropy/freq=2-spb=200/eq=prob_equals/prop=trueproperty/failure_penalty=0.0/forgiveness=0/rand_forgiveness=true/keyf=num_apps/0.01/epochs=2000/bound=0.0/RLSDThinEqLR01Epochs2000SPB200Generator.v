Require Import ZArith.
From QuickChick Require Import QuickChick.
From ExtLib Require Import Monad.
From ExtLib.Data.Monads Require Import OptionMonad.
Import QcNotation.
Import MonadNotation.
From Coq Require Import List.
Import ListNotations.

From RBT Require Import Impl Spec.

Inductive CtorColor :=
  | CtorColor_R
  | CtorColor_B.

Inductive LeafCtorColor :=
  | LeafCtorColor_R
  | LeafCtorColor_B.

Inductive CtorColorKVTree :=
  | CtorColorKVTree_E
  | CtorColorKVTree_T.

Inductive LeafCtorColorKVTree :=
  | LeafCtorColorKVTree_E.

Inductive TupLeafCtorColorLeafCtorColorKVTreeLeafCtorColorKVTree :=
  | MkLeafCtorColorLeafCtorColorKVTreeLeafCtorColorKVTree : LeafCtorColor -> LeafCtorColorKVTree -> LeafCtorColorKVTree -> TupLeafCtorColorLeafCtorColorKVTreeLeafCtorColorKVTree.

Inductive TupLeafCtorColorCtorColorKVTreeCtorColorKVTree :=
  | MkLeafCtorColorCtorColorKVTreeCtorColorKVTree : LeafCtorColor -> CtorColorKVTree -> CtorColorKVTree -> TupLeafCtorColorCtorColorKVTreeCtorColorKVTree.

Definition genLeafColor (chosen_ctor : LeafCtorColor) (stack1 : nat) (stack2 : nat) : G (Color) :=
  match chosen_ctor with
  | LeafCtorColor_R  => 
    (returnGen (R ))
  | LeafCtorColor_B  => 
    (returnGen (B ))
  end.

Definition genLeafTree (chosen_ctor : LeafCtorColorKVTree) (stack1 : nat) (stack2 : nat) : G (Tree) :=
  match chosen_ctor with
  | LeafCtorColorKVTree_E  => 
    (returnGen (E ))
  end.

Fixpoint genTree (size : nat) (chosen_ctor : CtorColorKVTree) (stack1 : nat) (stack2 : nat) : G (Tree) :=
  match size with
  | O  => match chosen_ctor with
    | CtorColorKVTree_E  => 
      (returnGen (E ))
    | CtorColorKVTree_T  => 
      (bindGen 
      (* Frequency2 *) (freq [
        (* 1 *) (match (stack1, stack2) with
        | (4, 4) => 54
        | (4, 6) => 57
        | (6, 4) => 41
        | (6, 6) => 50
        | _ => 500
        end,
        (returnGen (MkLeafCtorColorLeafCtorColorKVTreeLeafCtorColorKVTree (LeafCtorColor_R ) (LeafCtorColorKVTree_E ) (LeafCtorColorKVTree_E )))); 
        (* 2 *) (match (stack1, stack2) with
        | (4, 4) => 49
        | (4, 6) => 46
        | (6, 4) => 60
        | (6, 6) => 53
        | _ => 500
        end,
        (returnGen (MkLeafCtorColorLeafCtorColorKVTreeLeafCtorColorKVTree (LeafCtorColor_B ) (LeafCtorColorKVTree_E ) (LeafCtorColorKVTree_E ))))]) 
      (fun param_variantis => (let '(MkLeafCtorColorLeafCtorColorKVTreeLeafCtorColorKVTree ctor1 ctor2 ctor3) := param_variantis in

        (bindGen (genLeafColor ctor1 stack2 1) 
        (fun p1 => 
          (bindGen (genLeafTree ctor2 stack2 3) 
          (fun p2 => 
            (bindGen 
            (* GenZ1 *)
            (let _weight_1 := match (stack1, stack2) with
            | (4, 4) => 47
            | (4, 6) => 62
            | (6, 4) => 50
            | (6, 6) => 60
            | _ => 500
            end
            in
            bindGen (freq [
              (_weight_1, returnGen 1%Z);
              (100-_weight_1, returnGen 0%Z)
            ]) (fun n1 =>
            (let _weight_2 := match (stack1, stack2) with
            | (4, 4) => 39
            | (4, 6) => 51
            | (6, 4) => 65
            | (6, 6) => 60
            | _ => 500
            end
            in
            bindGen (freq [
              (_weight_2, returnGen 2%Z);
              (100-_weight_2, returnGen 0%Z)
            ]) (fun n2 =>
            (let _weight_4 := match (stack1, stack2) with
            | (4, 4) => 52
            | (4, 6) => 56
            | (6, 4) => 61
            | (6, 6) => 57
            | _ => 500
            end
            in
            bindGen (freq [
              (_weight_4, returnGen 4%Z);
              (100-_weight_4, returnGen 0%Z)
            ]) (fun n4 =>
              returnGen (n1 + n2 + n4)%Z
            )))))) 
            (fun p3 => 
              (bindGen 
              (* GenZ3 *)
              (let _weight_1 := match (stack1, stack2) with
              | (4, 4) => 51
              | (4, 6) => 31
              | (6, 4) => 63
              | (6, 6) => 32
              | _ => 500
              end
              in
              bindGen (freq [
                (_weight_1, returnGen 1%Z);
                (100-_weight_1, returnGen 0%Z)
              ]) (fun n1 =>
              (let _weight_2 := match (stack1, stack2) with
              | (4, 4) => 74
              | (4, 6) => 51
              | (6, 4) => 39
              | (6, 6) => 47
              | _ => 500
              end
              in
              bindGen (freq [
                (_weight_2, returnGen 2%Z);
                (100-_weight_2, returnGen 0%Z)
              ]) (fun n2 =>
              (let _weight_4 := match (stack1, stack2) with
              | (4, 4) => 70
              | (4, 6) => 58
              | (6, 4) => 62
              | (6, 6) => 43
              | _ => 500
              end
              in
              bindGen (freq [
                (_weight_4, returnGen 4%Z);
                (100-_weight_4, returnGen 0%Z)
              ]) (fun n4 =>
                returnGen (n1 + n2 + n4)%Z
              )))))) 
              (fun p4 => 
                (bindGen (genLeafTree ctor3 stack2 5) 
                (fun p5 => 
                  (returnGen (T p1 p2 p3 p4 p5)))))))))))))))
    end
  | S size1 => match chosen_ctor with
    | CtorColorKVTree_E  => 
      (returnGen (E ))
    | CtorColorKVTree_T  => 
      (bindGen 
      (* Frequency3 *) (freq [
        (* 1 *) (match (size, stack1, stack2) with
        | (1, 4, 4) => 5
        | (1, 4, 6) => 5
        | (1, 6, 4) => 5
        | (1, 6, 6) => 5
        | (2, 0, 4) => 1
        | (2, 0, 6) => 1
        | (3, 0, 0) => 0
        | _ => 500
        end,
        (returnGen (MkLeafCtorColorCtorColorKVTreeCtorColorKVTree (LeafCtorColor_R ) (CtorColorKVTree_E ) (CtorColorKVTree_E )))); 
        (* 2 *) (match (size, stack1, stack2) with
        | (1, 4, 4) => 5
        | (1, 4, 6) => 4
        | (1, 6, 4) => 5
        | (1, 6, 6) => 5
        | (2, 0, 4) => 1
        | (2, 0, 6) => 1
        | (3, 0, 0) => 0
        | _ => 500
        end,
        (returnGen (MkLeafCtorColorCtorColorKVTreeCtorColorKVTree (LeafCtorColor_B ) (CtorColorKVTree_E ) (CtorColorKVTree_E )))); 
        (* 3 *) (match (size, stack1, stack2) with
        | (1, 4, 4) => 19
        | (1, 4, 6) => 17
        | (1, 6, 4) => 19
        | (1, 6, 6) => 12
        | (2, 0, 4) => 2
        | (2, 0, 6) => 2
        | (3, 0, 0) => 1
        | _ => 500
        end,
        (returnGen (MkLeafCtorColorCtorColorKVTreeCtorColorKVTree (LeafCtorColor_R ) (CtorColorKVTree_T ) (CtorColorKVTree_E )))); 
        (* 4 *) (match (size, stack1, stack2) with
        | (1, 4, 4) => 18
        | (1, 4, 6) => 14
        | (1, 6, 4) => 11
        | (1, 6, 6) => 13
        | (2, 0, 4) => 2
        | (2, 0, 6) => 2
        | (3, 0, 0) => 1
        | _ => 500
        end,
        (returnGen (MkLeafCtorColorCtorColorKVTreeCtorColorKVTree (LeafCtorColor_B ) (CtorColorKVTree_T ) (CtorColorKVTree_E )))); 
        (* 5 *) (match (size, stack1, stack2) with
        | (1, 4, 4) => 21
        | (1, 4, 6) => 18
        | (1, 6, 4) => 20
        | (1, 6, 6) => 28
        | (2, 0, 4) => 2
        | (2, 0, 6) => 2
        | (3, 0, 0) => 1
        | _ => 500
        end,
        (returnGen (MkLeafCtorColorCtorColorKVTreeCtorColorKVTree (LeafCtorColor_R ) (CtorColorKVTree_E ) (CtorColorKVTree_T )))); 
        (* 6 *) (match (size, stack1, stack2) with
        | (1, 4, 4) => 16
        | (1, 4, 6) => 18
        | (1, 6, 4) => 17
        | (1, 6, 6) => 18
        | (2, 0, 4) => 2
        | (2, 0, 6) => 2
        | (3, 0, 0) => 1
        | _ => 500
        end,
        (returnGen (MkLeafCtorColorCtorColorKVTreeCtorColorKVTree (LeafCtorColor_B ) (CtorColorKVTree_E ) (CtorColorKVTree_T )))); 
        (* 7 *) (match (size, stack1, stack2) with
        | (1, 4, 4) => 87
        | (1, 4, 6) => 87
        | (1, 6, 4) => 90
        | (1, 6, 6) => 88
        | (2, 0, 4) => 93
        | (2, 0, 6) => 93
        | (3, 0, 0) => 95
        | _ => 500
        end,
        (returnGen (MkLeafCtorColorCtorColorKVTreeCtorColorKVTree (LeafCtorColor_R ) (CtorColorKVTree_T ) (CtorColorKVTree_T )))); 
        (* 8 *) (match (size, stack1, stack2) with
        | (1, 4, 4) => 89
        | (1, 4, 6) => 90
        | (1, 6, 4) => 86
        | (1, 6, 6) => 89
        | (2, 0, 4) => 93
        | (2, 0, 6) => 94
        | (3, 0, 0) => 95
        | _ => 500
        end,
        (returnGen (MkLeafCtorColorCtorColorKVTreeCtorColorKVTree (LeafCtorColor_B ) (CtorColorKVTree_T ) (CtorColorKVTree_T ))))]) 
      (fun param_variantis => (let '(MkLeafCtorColorCtorColorKVTreeCtorColorKVTree ctor1 ctor2 ctor3) := param_variantis in

        (bindGen (genLeafColor ctor1 stack2 2) 
        (fun p1 => 
          (bindGen (genTree size1 ctor2 stack2 4) 
          (fun p2 => 
            (bindGen 
            (* GenZ2 *)
            (let _weight_1 := match (size, stack1, stack2) with
            | (1, 4, 4) => 55
            | (1, 4, 6) => 48
            | (1, 6, 4) => 49
            | (1, 6, 6) => 22
            | (2, 0, 4) => 36
            | (2, 0, 6) => 55
            | (3, 0, 0) => 61
            | _ => 500
            end
            in
            bindGen (freq [
              (_weight_1, returnGen 1%Z);
              (100-_weight_1, returnGen 0%Z)
            ]) (fun n1 =>
            (let _weight_2 := match (size, stack1, stack2) with
            | (1, 4, 4) => 50
            | (1, 4, 6) => 62
            | (1, 6, 4) => 48
            | (1, 6, 6) => 47
            | (2, 0, 4) => 63
            | (2, 0, 6) => 47
            | (3, 0, 0) => 66
            | _ => 500
            end
            in
            bindGen (freq [
              (_weight_2, returnGen 2%Z);
              (100-_weight_2, returnGen 0%Z)
            ]) (fun n2 =>
            (let _weight_4 := match (size, stack1, stack2) with
            | (1, 4, 4) => 40
            | (1, 4, 6) => 62
            | (1, 6, 4) => 66
            | (1, 6, 6) => 29
            | (2, 0, 4) => 62
            | (2, 0, 6) => 54
            | (3, 0, 0) => 56
            | _ => 500
            end
            in
            bindGen (freq [
              (_weight_4, returnGen 4%Z);
              (100-_weight_4, returnGen 0%Z)
            ]) (fun n4 =>
              returnGen (n1 + n2 + n4)%Z
            )))))) 
            (fun p3 => 
              (bindGen 
              (* GenZ4 *)
              (let _weight_1 := match (size, stack1, stack2) with
              | (1, 4, 4) => 76
              | (1, 4, 6) => 56
              | (1, 6, 4) => 30
              | (1, 6, 6) => 53
              | (2, 0, 4) => 47
              | (2, 0, 6) => 24
              | (3, 0, 0) => 45
              | _ => 500
              end
              in
              bindGen (freq [
                (_weight_1, returnGen 1%Z);
                (100-_weight_1, returnGen 0%Z)
              ]) (fun n1 =>
              (let _weight_2 := match (size, stack1, stack2) with
              | (1, 4, 4) => 45
              | (1, 4, 6) => 50
              | (1, 6, 4) => 59
              | (1, 6, 6) => 31
              | (2, 0, 4) => 54
              | (2, 0, 6) => 35
              | (3, 0, 0) => 39
              | _ => 500
              end
              in
              bindGen (freq [
                (_weight_2, returnGen 2%Z);
                (100-_weight_2, returnGen 0%Z)
              ]) (fun n2 =>
              (let _weight_4 := match (size, stack1, stack2) with
              | (1, 4, 4) => 61
              | (1, 4, 6) => 47
              | (1, 6, 4) => 59
              | (1, 6, 6) => 60
              | (2, 0, 4) => 68
              | (2, 0, 6) => 47
              | (3, 0, 0) => 53
              | _ => 500
              end
              in
              bindGen (freq [
                (_weight_4, returnGen 4%Z);
                (100-_weight_4, returnGen 0%Z)
              ]) (fun n4 =>
                returnGen (n1 + n2 + n4)%Z
              )))))) 
              (fun p4 => 
                (bindGen (genTree size1 ctor3 stack2 6) 
                (fun p5 => 
                  (returnGen (T p1 p2 p3 p4 p5)))))))))))))))
    end
  end.

Definition gSized :=

  (bindGen 
  (* Frequency1 *) (freq [
    (* 1 *) (match (tt) with
    | tt => 0
    end,
    (returnGen (CtorColorKVTree_E ))); 
    (* 2 *) (match (tt) with
    | tt => 88
    end,
    (returnGen (CtorColorKVTree_T )))]) 
  (fun init_ctor => (genTree 3 init_ctor 0 0))).

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
          
