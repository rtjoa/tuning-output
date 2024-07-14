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
        | (4, 4) => 43
        | (4, 6) => 67
        | (6, 4) => 58
        | (6, 6) => 37
        | _ => 500
        end,
        (returnGen (MkLeafCtorColorLeafCtorColorKVTreeLeafCtorColorKVTree (LeafCtorColor_R ) (LeafCtorColorKVTree_E ) (LeafCtorColorKVTree_E )))); 
        (* 2 *) (match (stack1, stack2) with
        | (4, 4) => 58
        | (4, 6) => 28
        | (6, 4) => 43
        | (6, 6) => 61
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
            | (4, 4) => 49
            | (4, 6) => 49
            | (6, 4) => 56
            | (6, 6) => 57
            | _ => 500
            end
            in
            bindGen (freq [
              (_weight_1, returnGen 1%Z);
              (100-_weight_1, returnGen 0%Z)
            ]) (fun n1 =>
            (let _weight_2 := match (stack1, stack2) with
            | (4, 4) => 59
            | (4, 6) => 50
            | (6, 4) => 48
            | (6, 6) => 43
            | _ => 500
            end
            in
            bindGen (freq [
              (_weight_2, returnGen 2%Z);
              (100-_weight_2, returnGen 0%Z)
            ]) (fun n2 =>
            (let _weight_4 := match (stack1, stack2) with
            | (4, 4) => 24
            | (4, 6) => 52
            | (6, 4) => 48
            | (6, 6) => 51
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
              | (4, 4) => 54
              | (4, 6) => 72
              | (6, 4) => 69
              | (6, 6) => 71
              | _ => 500
              end
              in
              bindGen (freq [
                (_weight_1, returnGen 1%Z);
                (100-_weight_1, returnGen 0%Z)
              ]) (fun n1 =>
              (let _weight_2 := match (stack1, stack2) with
              | (4, 4) => 64
              | (4, 6) => 57
              | (6, 4) => 67
              | (6, 6) => 55
              | _ => 500
              end
              in
              bindGen (freq [
                (_weight_2, returnGen 2%Z);
                (100-_weight_2, returnGen 0%Z)
              ]) (fun n2 =>
              (let _weight_4 := match (stack1, stack2) with
              | (4, 4) => 63
              | (4, 6) => 43
              | (6, 4) => 49
              | (6, 6) => 59
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
        | (1, 4, 4) => 10
        | (1, 4, 6) => 10
        | (1, 6, 4) => 10
        | (1, 6, 6) => 11
        | (2, 0, 4) => 10
        | (2, 0, 6) => 10
        | (3, 0, 0) => 10
        | _ => 500
        end,
        (returnGen (MkLeafCtorColorCtorColorKVTreeCtorColorKVTree (LeafCtorColor_R ) (CtorColorKVTree_E ) (CtorColorKVTree_E )))); 
        (* 2 *) (match (size, stack1, stack2) with
        | (1, 4, 4) => 10
        | (1, 4, 6) => 11
        | (1, 6, 4) => 12
        | (1, 6, 6) => 10
        | (2, 0, 4) => 10
        | (2, 0, 6) => 10
        | (3, 0, 0) => 10
        | _ => 500
        end,
        (returnGen (MkLeafCtorColorCtorColorKVTreeCtorColorKVTree (LeafCtorColor_B ) (CtorColorKVTree_E ) (CtorColorKVTree_E )))); 
        (* 3 *) (match (size, stack1, stack2) with
        | (1, 4, 4) => 30
        | (1, 4, 6) => 38
        | (1, 6, 4) => 25
        | (1, 6, 6) => 37
        | (2, 0, 4) => 10
        | (2, 0, 6) => 10
        | (3, 0, 0) => 10
        | _ => 500
        end,
        (returnGen (MkLeafCtorColorCtorColorKVTreeCtorColorKVTree (LeafCtorColor_R ) (CtorColorKVTree_T ) (CtorColorKVTree_E )))); 
        (* 4 *) (match (size, stack1, stack2) with
        | (1, 4, 4) => 38
        | (1, 4, 6) => 23
        | (1, 6, 4) => 36
        | (1, 6, 6) => 43
        | (2, 0, 4) => 10
        | (2, 0, 6) => 10
        | (3, 0, 0) => 10
        | _ => 500
        end,
        (returnGen (MkLeafCtorColorCtorColorKVTreeCtorColorKVTree (LeafCtorColor_B ) (CtorColorKVTree_T ) (CtorColorKVTree_E )))); 
        (* 5 *) (match (size, stack1, stack2) with
        | (1, 4, 4) => 31
        | (1, 4, 6) => 26
        | (1, 6, 4) => 30
        | (1, 6, 6) => 39
        | (2, 0, 4) => 10
        | (2, 0, 6) => 10
        | (3, 0, 0) => 10
        | _ => 500
        end,
        (returnGen (MkLeafCtorColorCtorColorKVTreeCtorColorKVTree (LeafCtorColor_R ) (CtorColorKVTree_E ) (CtorColorKVTree_T )))); 
        (* 6 *) (match (size, stack1, stack2) with
        | (1, 4, 4) => 29
        | (1, 4, 6) => 39
        | (1, 6, 4) => 23
        | (1, 6, 6) => 26
        | (2, 0, 4) => 10
        | (2, 0, 6) => 10
        | (3, 0, 0) => 10
        | _ => 500
        end,
        (returnGen (MkLeafCtorColorCtorColorKVTreeCtorColorKVTree (LeafCtorColor_B ) (CtorColorKVTree_E ) (CtorColorKVTree_T )))); 
        (* 7 *) (match (size, stack1, stack2) with
        | (1, 4, 4) => 85
        | (1, 4, 6) => 84
        | (1, 6, 4) => 87
        | (1, 6, 6) => 82
        | (2, 0, 4) => 90
        | (2, 0, 6) => 90
        | (3, 0, 0) => 90
        | _ => 500
        end,
        (returnGen (MkLeafCtorColorCtorColorKVTreeCtorColorKVTree (LeafCtorColor_R ) (CtorColorKVTree_T ) (CtorColorKVTree_T )))); 
        (* 8 *) (match (size, stack1, stack2) with
        | (1, 4, 4) => 82
        | (1, 4, 6) => 83
        | (1, 6, 4) => 83
        | (1, 6, 6) => 83
        | (2, 0, 4) => 90
        | (2, 0, 6) => 90
        | (3, 0, 0) => 90
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
            | (1, 4, 4) => 47
            | (1, 4, 6) => 37
            | (1, 6, 4) => 49
            | (1, 6, 6) => 70
            | (2, 0, 4) => 52
            | (2, 0, 6) => 37
            | (3, 0, 0) => 35
            | _ => 500
            end
            in
            bindGen (freq [
              (_weight_1, returnGen 1%Z);
              (100-_weight_1, returnGen 0%Z)
            ]) (fun n1 =>
            (let _weight_2 := match (size, stack1, stack2) with
            | (1, 4, 4) => 69
            | (1, 4, 6) => 51
            | (1, 6, 4) => 58
            | (1, 6, 6) => 41
            | (2, 0, 4) => 61
            | (2, 0, 6) => 42
            | (3, 0, 0) => 60
            | _ => 500
            end
            in
            bindGen (freq [
              (_weight_2, returnGen 2%Z);
              (100-_weight_2, returnGen 0%Z)
            ]) (fun n2 =>
            (let _weight_4 := match (size, stack1, stack2) with
            | (1, 4, 4) => 51
            | (1, 4, 6) => 56
            | (1, 6, 4) => 54
            | (1, 6, 6) => 39
            | (2, 0, 4) => 58
            | (2, 0, 6) => 42
            | (3, 0, 0) => 49
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
              | (1, 4, 4) => 53
              | (1, 4, 6) => 50
              | (1, 6, 4) => 61
              | (1, 6, 6) => 40
              | (2, 0, 4) => 43
              | (2, 0, 6) => 55
              | (3, 0, 0) => 53
              | _ => 500
              end
              in
              bindGen (freq [
                (_weight_1, returnGen 1%Z);
                (100-_weight_1, returnGen 0%Z)
              ]) (fun n1 =>
              (let _weight_2 := match (size, stack1, stack2) with
              | (1, 4, 4) => 47
              | (1, 4, 6) => 56
              | (1, 6, 4) => 46
              | (1, 6, 6) => 33
              | (2, 0, 4) => 60
              | (2, 0, 6) => 57
              | (3, 0, 0) => 46
              | _ => 500
              end
              in
              bindGen (freq [
                (_weight_2, returnGen 2%Z);
                (100-_weight_2, returnGen 0%Z)
              ]) (fun n2 =>
              (let _weight_4 := match (size, stack1, stack2) with
              | (1, 4, 4) => 54
              | (1, 4, 6) => 63
              | (1, 6, 4) => 68
              | (1, 6, 6) => 41
              | (2, 0, 4) => 55
              | (2, 0, 6) => 45
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
    | tt => 10
    end,
    (returnGen (CtorColorKVTree_E ))); 
    (* 2 *) (match (tt) with
    | tt => 90
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
          
