Require Import ZArith.
From QuickChick Require Import QuickChick.
From ExtLib Require Import Monad.
From ExtLib.Data.Monads Require Import OptionMonad.
Import QcNotation.
Import MonadNotation.
From Coq Require Import List.
Import ListNotations.

From RBT Require Import Impl Spec.

Definition genColor (size : nat) (stack1 : nat) (stack2 : nat) : G (Color) :=

  (* Frequency1 *) (freq [
    (* R *) (match (size, stack1, stack2) with
    | (0, 0, 1) => 25
    | (0, 2, 1) => 59
    | (0, 3, 1) => 65
    | _ => 500
    end,
    (returnGen (R ))); 
    (* B *) (match (size, stack1, stack2) with
    | (0, 0, 1) => 69
    | (0, 2, 1) => 39
    | (0, 3, 1) => 31
    | _ => 500
    end,
    (returnGen (B )))]).

Fixpoint genTree (size : nat) (stack1 : nat) (stack2 : nat) : G (Tree) :=
  match size with
  | O  => 
    (* Frequency2 (single-branch) *) 
    (returnGen (E ))
  | S size1 => 
    (* Frequency3 *) (freq [
      (* E *) (match (size, stack1, stack2) with
      | (1, 0, 2) => 71
      | (1, 0, 3) => 63
      | (2, 0, 0) => 6
      | _ => 500
      end,
      (returnGen (E ))); 
      (* T *) (match (size, stack1, stack2) with
      | (1, 0, 2) => 20
      | (1, 0, 3) => 38
      | (2, 0, 0) => 79
      | _ => 500
      end,
      (bindGen (genColor 0 stack2 1) 
      (fun p1 => 
        (bindGen (genTree size1 stack2 2) 
        (fun p2 => 
          (bindGen 
          (* GenZ1 *)
          (let _weight_1 := match (size, stack1, stack2) with
          | (1, 0, 2) => 30
          | (1, 0, 3) => 47
          | (2, 0, 0) => 37
          | _ => 500
          end
          in
          bindGen (freq [
            (_weight_1, returnGen 1%Z);
            (100-_weight_1, returnGen 0%Z)
          ]) (fun n1 =>
          (let _weight_2 := match (size, stack1, stack2) with
          | (1, 0, 2) => 31
          | (1, 0, 3) => 63
          | (2, 0, 0) => 57
          | _ => 500
          end
          in
          bindGen (freq [
            (_weight_2, returnGen 2%Z);
            (100-_weight_2, returnGen 0%Z)
          ]) (fun n2 =>
          (let _weight_4 := match (size, stack1, stack2) with
          | (1, 0, 2) => 55
          | (1, 0, 3) => 64
          | (2, 0, 0) => 35
          | _ => 500
          end
          in
          bindGen (freq [
            (_weight_4, returnGen 4%Z);
            (100-_weight_4, returnGen 0%Z)
          ]) (fun n4 =>
          (let _weight_8 := match (size, stack1, stack2) with
          | (1, 0, 2) => 36
          | (1, 0, 3) => 73
          | (2, 0, 0) => 48
          | _ => 500
          end
          in
          bindGen (freq [
            (_weight_8, returnGen 8%Z);
            (100-_weight_8, returnGen 0%Z)
          ]) (fun n8 =>
          (let _weight_16 := match (size, stack1, stack2) with
          | (1, 0, 2) => 26
          | (1, 0, 3) => 73
          | (2, 0, 0) => 28
          | _ => 500
          end
          in
          bindGen (freq [
            (_weight_16, returnGen 16%Z);
            (100-_weight_16, returnGen 0%Z)
          ]) (fun n16 =>
          (let _weight_32 := match (size, stack1, stack2) with
          | (1, 0, 2) => 34
          | (1, 0, 3) => 72
          | (2, 0, 0) => 44
          | _ => 500
          end
          in
          bindGen (freq [
            (_weight_32, returnGen 32%Z);
            (100-_weight_32, returnGen 0%Z)
          ]) (fun n32 =>
            returnGen (n1 + n2 + n4 + n8 + n16 + n32)%Z
          )))))))))))) 
          (fun p3 => 
            (bindGen 
            (* GenZ2 *)
            (let _weight_1 := match (size, stack1, stack2) with
            | (1, 0, 2) => 46
            | (1, 0, 3) => 36
            | (2, 0, 0) => 49
            | _ => 500
            end
            in
            bindGen (freq [
              (_weight_1, returnGen 1%Z);
              (100-_weight_1, returnGen 0%Z)
            ]) (fun n1 =>
            (let _weight_2 := match (size, stack1, stack2) with
            | (1, 0, 2) => 43
            | (1, 0, 3) => 48
            | (2, 0, 0) => 42
            | _ => 500
            end
            in
            bindGen (freq [
              (_weight_2, returnGen 2%Z);
              (100-_weight_2, returnGen 0%Z)
            ]) (fun n2 =>
            (let _weight_4 := match (size, stack1, stack2) with
            | (1, 0, 2) => 48
            | (1, 0, 3) => 56
            | (2, 0, 0) => 54
            | _ => 500
            end
            in
            bindGen (freq [
              (_weight_4, returnGen 4%Z);
              (100-_weight_4, returnGen 0%Z)
            ]) (fun n4 =>
            (let _weight_8 := match (size, stack1, stack2) with
            | (1, 0, 2) => 50
            | (1, 0, 3) => 60
            | (2, 0, 0) => 64
            | _ => 500
            end
            in
            bindGen (freq [
              (_weight_8, returnGen 8%Z);
              (100-_weight_8, returnGen 0%Z)
            ]) (fun n8 =>
            (let _weight_16 := match (size, stack1, stack2) with
            | (1, 0, 2) => 38
            | (1, 0, 3) => 35
            | (2, 0, 0) => 51
            | _ => 500
            end
            in
            bindGen (freq [
              (_weight_16, returnGen 16%Z);
              (100-_weight_16, returnGen 0%Z)
            ]) (fun n16 =>
            (let _weight_32 := match (size, stack1, stack2) with
            | (1, 0, 2) => 55
            | (1, 0, 3) => 56
            | (2, 0, 0) => 56
            | _ => 500
            end
            in
            bindGen (freq [
              (_weight_32, returnGen 32%Z);
              (100-_weight_32, returnGen 0%Z)
            ]) (fun n32 =>
              returnGen (n1 + n2 + n4 + n8 + n16 + n32)%Z
            )))))))))))) 
            (fun p4 => 
              (bindGen (genTree size1 stack2 3) 
              (fun p5 => 
                (returnGen (T p1 p2 p3 p4 p5)))))))))))))])
  end.

Definition gSized :=
  (genTree 2 0 0).

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
          
