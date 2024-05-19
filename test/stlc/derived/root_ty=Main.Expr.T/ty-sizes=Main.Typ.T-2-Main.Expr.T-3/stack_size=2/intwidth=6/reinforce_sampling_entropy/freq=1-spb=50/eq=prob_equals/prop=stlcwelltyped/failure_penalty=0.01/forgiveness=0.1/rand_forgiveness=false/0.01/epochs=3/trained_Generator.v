From QuickChick Require Import QuickChick. Import QcNotation.
From Coq Require Import Bool ZArith List. Import ListNotations.
From ExtLib Require Import Monad.
From ExtLib.Data.Monads Require Import OptionMonad.
Import MonadNotation.

From STLC Require Import Impl Spec.
    
Fixpoint gen_Typ (size : nat) (stack1 : nat) (stack2 : nat) : G Typ :=
  match size with
  | 0 => 
    
        (* TBool *)

    
            returnGen (TBool )
    
        
    
  | S size' => 
    freq [
        (* TBool *)

    (
         match (size, ((stack1 : nat), (stack2 : nat))) with 
         | (1, (4, 1)) => 500
         | (2, (0, 4)) => 500
         | (2, (4, 4)) => 500
         | (2, (5, 4)) => 500
         | _ => 500
         end,
         
            returnGen (TBool )
    )
        ;
    (* TFun *)

    (
         match (size, ((stack1 : nat), (stack2 : nat))) with 
         | (1, (4, 1)) => 500
         | (2, (0, 4)) => 500
         | (2, (4, 4)) => 500
         | (2, (5, 4)) => 500
         | _ => 500
         end,
         
            bindGen (gen_Typ size' (stack2 : nat) 1) (fun p1 : Typ =>
bindGen (gen_Typ size' (stack2 : nat) 1) (fun p2 : Typ =>
returnGen (TFun p1 p2)
)
)
    )
        
    ]
    end.

Fixpoint gen_Expr (size : nat) (stack1 : nat) (stack2 : nat) : G Expr :=
  match size with
  | 0 => 
    freq [
        (* Var *)

    (
         match (size, ((stack1 : nat), (stack2 : nat))) with 
         | (0, (4, 4)) => 500
         | (0, (4, 5)) => 500
         | (0, (5, 4)) => 500
         | (0, (5, 5)) => 500
         | _ => 500
         end,
         
            let weight_1 := match (size, ((stack1 : nat), (stack2 : nat))) with 
         | (0, (4, 4)) => 500
         | (0, (4, 5)) => 500
         | (0, (5, 4)) => 500
         | (0, (5, 5)) => 500
         | _ => 500
         end in
                        bindGen (freq [
                            (weight_1, returnGen 1);
                            (1000-weight_1, returnGen 0)
                        ])
                        (fun n1 : nat => 
                        
let weight_2 := match (size, ((stack1 : nat), (stack2 : nat))) with 
         | (0, (4, 4)) => 500
         | (0, (4, 5)) => 500
         | (0, (5, 4)) => 500
         | (0, (5, 5)) => 500
         | _ => 500
         end in
                        bindGen (freq [
                            (weight_2, returnGen 2);
                            (1000-weight_2, returnGen 0)
                        ])
                        (fun n2 : nat => 
                        
let weight_4 := match (size, ((stack1 : nat), (stack2 : nat))) with 
         | (0, (4, 4)) => 500
         | (0, (4, 5)) => 500
         | (0, (5, 4)) => 500
         | (0, (5, 5)) => 500
         | _ => 500
         end in
                        bindGen (freq [
                            (weight_4, returnGen 4);
                            (1000-weight_4, returnGen 0)
                        ])
                        (fun n4 : nat => 
                        
let weight_8 := match (size, ((stack1 : nat), (stack2 : nat))) with 
         | (0, (4, 4)) => 500
         | (0, (4, 5)) => 500
         | (0, (5, 4)) => 500
         | (0, (5, 5)) => 500
         | _ => 500
         end in
                        bindGen (freq [
                            (weight_8, returnGen 8);
                            (1000-weight_8, returnGen 0)
                        ])
                        (fun n8 : nat => 
                        
let weight_16 := match (size, ((stack1 : nat), (stack2 : nat))) with 
         | (0, (4, 4)) => 500
         | (0, (4, 5)) => 500
         | (0, (5, 4)) => 500
         | (0, (5, 5)) => 500
         | _ => 500
         end in
                        bindGen (freq [
                            (weight_16, returnGen 16);
                            (1000-weight_16, returnGen 0)
                        ])
                        (fun n16 : nat => 
                        
let weight_32 := match (size, ((stack1 : nat), (stack2 : nat))) with 
         | (0, (4, 4)) => 500
         | (0, (4, 5)) => 500
         | (0, (5, 4)) => 500
         | (0, (5, 5)) => 500
         | _ => 500
         end in
                        bindGen (freq [
                            (weight_32, returnGen 32);
                            (1000-weight_32, returnGen 0)
                        ])
                        (fun n32 : nat => 
                        let p1 := n1+n2+n4+n8+n16+n32
                        
returnGen (Var p1)
)
)
)
)
)
)
    )
        ;
    (* Bool *)

    (
         match (size, ((stack1 : nat), (stack2 : nat))) with 
         | (0, (4, 4)) => 500
         | (0, (4, 5)) => 500
         | (0, (5, 4)) => 500
         | (0, (5, 5)) => 500
         | _ => 500
         end,
         
            let weight_true := match (size, ((stack1 : nat), (stack2 : nat))) with 
         | (0, (4, 4)) => 500
         | (0, (4, 5)) => 500
         | (0, (5, 4)) => 500
         | (0, (5, 5)) => 500
         | _ => 500
         end in
                    bindGen (freq [
                        (weight_true, true);
                        (1000-weight_true, false)
                    ]) (fun p1 : bool =>
returnGen (Bool p1)
)
    )
        
    ]
  | S size' => 
    freq [
        (* Var *)

    (
         match (size, ((stack1 : nat), (stack2 : nat))) with 
         | (1, (4, 4)) => 500
         | (1, (4, 5)) => 500
         | (1, (5, 4)) => 500
         | (1, (5, 5)) => 500
         | (2, (0, 4)) => 500
         | (2, (0, 5)) => 500
         | (3, (0, 0)) => 499
         | _ => 500
         end,
         
            let weight_1 := match (size, ((stack1 : nat), (stack2 : nat))) with 
         | (1, (4, 4)) => 500
         | (1, (4, 5)) => 500
         | (1, (5, 4)) => 500
         | (1, (5, 5)) => 500
         | (2, (0, 4)) => 500
         | (2, (0, 5)) => 500
         | (3, (0, 0)) => 500
         | _ => 500
         end in
                        bindGen (freq [
                            (weight_1, returnGen 1);
                            (1000-weight_1, returnGen 0)
                        ])
                        (fun n1 : nat => 
                        
let weight_2 := match (size, ((stack1 : nat), (stack2 : nat))) with 
         | (1, (4, 4)) => 500
         | (1, (4, 5)) => 500
         | (1, (5, 4)) => 500
         | (1, (5, 5)) => 500
         | (2, (0, 4)) => 500
         | (2, (0, 5)) => 500
         | (3, (0, 0)) => 500
         | _ => 500
         end in
                        bindGen (freq [
                            (weight_2, returnGen 2);
                            (1000-weight_2, returnGen 0)
                        ])
                        (fun n2 : nat => 
                        
let weight_4 := match (size, ((stack1 : nat), (stack2 : nat))) with 
         | (1, (4, 4)) => 500
         | (1, (4, 5)) => 500
         | (1, (5, 4)) => 500
         | (1, (5, 5)) => 500
         | (2, (0, 4)) => 500
         | (2, (0, 5)) => 500
         | (3, (0, 0)) => 500
         | _ => 500
         end in
                        bindGen (freq [
                            (weight_4, returnGen 4);
                            (1000-weight_4, returnGen 0)
                        ])
                        (fun n4 : nat => 
                        
let weight_8 := match (size, ((stack1 : nat), (stack2 : nat))) with 
         | (1, (4, 4)) => 500
         | (1, (4, 5)) => 500
         | (1, (5, 4)) => 500
         | (1, (5, 5)) => 500
         | (2, (0, 4)) => 500
         | (2, (0, 5)) => 500
         | (3, (0, 0)) => 500
         | _ => 500
         end in
                        bindGen (freq [
                            (weight_8, returnGen 8);
                            (1000-weight_8, returnGen 0)
                        ])
                        (fun n8 : nat => 
                        
let weight_16 := match (size, ((stack1 : nat), (stack2 : nat))) with 
         | (1, (4, 4)) => 500
         | (1, (4, 5)) => 500
         | (1, (5, 4)) => 500
         | (1, (5, 5)) => 500
         | (2, (0, 4)) => 500
         | (2, (0, 5)) => 500
         | (3, (0, 0)) => 500
         | _ => 500
         end in
                        bindGen (freq [
                            (weight_16, returnGen 16);
                            (1000-weight_16, returnGen 0)
                        ])
                        (fun n16 : nat => 
                        
let weight_32 := match (size, ((stack1 : nat), (stack2 : nat))) with 
         | (1, (4, 4)) => 500
         | (1, (4, 5)) => 500
         | (1, (5, 4)) => 500
         | (1, (5, 5)) => 500
         | (2, (0, 4)) => 500
         | (2, (0, 5)) => 500
         | (3, (0, 0)) => 500
         | _ => 500
         end in
                        bindGen (freq [
                            (weight_32, returnGen 32);
                            (1000-weight_32, returnGen 0)
                        ])
                        (fun n32 : nat => 
                        let p1 := n1+n2+n4+n8+n16+n32
                        
returnGen (Var p1)
)
)
)
)
)
)
    )
        ;
    (* Bool *)

    (
         match (size, ((stack1 : nat), (stack2 : nat))) with 
         | (1, (4, 4)) => 500
         | (1, (4, 5)) => 500
         | (1, (5, 4)) => 500
         | (1, (5, 5)) => 500
         | (2, (0, 4)) => 501
         | (2, (0, 5)) => 500
         | (3, (0, 0)) => 500
         | _ => 500
         end,
         
            let weight_true := match (size, ((stack1 : nat), (stack2 : nat))) with 
         | (1, (4, 4)) => 500
         | (1, (4, 5)) => 500
         | (1, (5, 4)) => 500
         | (1, (5, 5)) => 500
         | (2, (0, 4)) => 500
         | (2, (0, 5)) => 500
         | (3, (0, 0)) => 500
         | _ => 500
         end in
                    bindGen (freq [
                        (weight_true, true);
                        (1000-weight_true, false)
                    ]) (fun p1 : bool =>
returnGen (Bool p1)
)
    )
        ;
    (* Abs *)

    (
         match (size, ((stack1 : nat), (stack2 : nat))) with 
         | (1, (4, 4)) => 500
         | (1, (4, 5)) => 500
         | (1, (5, 4)) => 500
         | (1, (5, 5)) => 500
         | (2, (0, 4)) => 500
         | (2, (0, 5)) => 500
         | (3, (0, 0)) => 501
         | _ => 500
         end,
         
            bindGen (gen_Typ 2 (stack2 : nat) 4) (fun p1 : Typ =>
bindGen (gen_Expr size' (stack2 : nat) 4) (fun p2 : Expr =>
returnGen (Abs p1 p2)
)
)
    )
        ;
    (* App *)

    (
         match (size, ((stack1 : nat), (stack2 : nat))) with 
         | (1, (4, 4)) => 500
         | (1, (4, 5)) => 500
         | (1, (5, 4)) => 500
         | (1, (5, 5)) => 500
         | (2, (0, 4)) => 500
         | (2, (0, 5)) => 500
         | (3, (0, 0)) => 500
         | _ => 500
         end,
         
            bindGen (gen_Expr size' (stack2 : nat) 5) (fun p1 : Expr =>
bindGen (gen_Expr size' (stack2 : nat) 5) (fun p2 : Expr =>
returnGen (App p1 p2)
)
)
    )
        
    ]
    end.

Definition gSized :=
  gen_Expr 3 0 0.

    Definition test_prop_SinglePreserve :=
forAll gSized (fun (e: Expr) =>
  prop_SinglePreserve e).

(*! QuickChick test_prop_SinglePreserve. *)

Definition test_prop_MultiPreserve :=
forAll gSized (fun (e: Expr) =>
  prop_MultiPreserve e).

(*! QuickChick test_prop_MultiPreserve. *)
          
