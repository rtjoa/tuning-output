From QuickChick Require Import QuickChick. Import QcNotation.
From Coq Require Import Bool ZArith List. Import ListNotations.
From ExtLib Require Import Monad.
From ExtLib.Data.Monads Require Import OptionMonad.
Import MonadNotation.

From STLC Require Import Impl Spec.

Fixpoint manual_gen_typ (size : nat) (stack1 : nat) (stack2 : nat) : G Typ :=
  match size with
  | 0 => returnGen TBool
  | S size' =>
      let weight_tbool := match (size,(stack1, stack2)) with 
         | (1, (10, 14)) => 733
         | (1, (10, 15)) => 266
         | (2, (0, 10)) => 216
         | (2, (11, 10)) => 247
         | (2, (12, 10)) => 324
         | (2, (13, 10)) => 349
         | _ => 500
         end in
      freq [ (weight_tbool, returnGen TBool);
      (1000 - weight_tbool,
      bindGen (manual_gen_typ size' (stack2 : nat) 14)
        (fun p0 : Typ =>
         bindGen (manual_gen_typ size' (stack2 : nat) 15)
           (fun p1 : Typ => returnGen (TFun p0 p1))))]
  end.

Fixpoint manual_gen_expr (size : nat) (stack1 : nat) (stack2 : nat) : G Expr :=
  match size with
  | 0 =>
      let weight_var := match (size,(stack1, stack2)) with 
         | (0, (11, 11)) => 414
         | (0, (11, 12)) => 997
         | (0, (11, 13)) => 532
         | (0, (12, 11)) => 433
         | (0, (12, 12)) => 998
         | (0, (12, 13)) => 498
         | (0, (13, 11)) => 580
         | (0, (13, 12)) => 998
         | (0, (13, 13)) => 517
         | _ => 500
         end in
      freq [ (weight_var, bindGen arbitrary (fun p0 : nat => returnGen (Var p0)));
      (1000 - weight_var, bindGen arbitrary (fun p0 : bool => returnGen (Bool p0)))]
  | S size' =>
      let weight_var := match (size,(stack1, stack2)) with 
         | (1, (11, 11)) => 1
         | (1, (11, 12)) => 0
         | (1, (11, 13)) => 1
         | (1, (12, 11)) => 119
         | (1, (12, 12)) => 277
         | (1, (12, 13)) => 265
         | (1, (13, 11)) => 222
         | (1, (13, 12)) => 343
         | (1, (13, 13)) => 336
         | (2, (11, 11)) => 0
         | (2, (11, 12)) => 85
         | (2, (11, 13)) => 96
         | (2, (12, 11)) => 326
         | (2, (12, 12)) => 455
         | (2, (12, 13)) => 438
         | (2, (13, 11)) => 417
         | (2, (13, 12)) => 472
         | (2, (13, 13)) => 472
         | (3, (11, 11)) => 0
         | (3, (11, 12)) => 285
         | (3, (11, 13)) => 288
         | (3, (12, 11)) => 393
         | (3, (12, 12)) => 488
         | (3, (12, 13)) => 488
         | (3, (13, 11)) => 465
         | (3, (13, 12)) => 489
         | (3, (13, 13)) => 489
         | (4, (0, 11)) => 0
         | (4, (0, 12)) => 381
         | (4, (0, 13)) => 382
         | (5, (0, 0)) => 0
         | _ => 500
         end in
      let weight_bool := match (size,(stack1, stack2)) with 
         | (1, (11, 11)) => 244
         | (1, (11, 12)) => 0
         | (1, (11, 13)) => 294
         | (1, (12, 11)) => 524
         | (1, (12, 12)) => 255
         | (1, (12, 13)) => 563
         | (1, (13, 11)) => 545
         | (1, (13, 12)) => 334
         | (1, (13, 13)) => 541
         | (2, (11, 11)) => 10
         | (2, (11, 12)) => 76
         | (2, (11, 13)) => 746
         | (2, (12, 11)) => 593
         | (2, (12, 12)) => 438
         | (2, (12, 13)) => 537
         | (2, (13, 11)) => 554
         | (2, (13, 12)) => 472
         | (2, (13, 13)) => 504
         | (3, (11, 11)) => 3
         | (3, (11, 12)) => 285
         | (3, (11, 13)) => 672
         | (3, (12, 11)) => 531
         | (3, (12, 12)) => 488
         | (3, (12, 13)) => 519
         | (3, (13, 11)) => 535
         | (3, (13, 12)) => 489
         | (3, (13, 13)) => 504
         | (4, (0, 11)) => 1
         | (4, (0, 12)) => 381
         | (4, (0, 13)) => 635
         | (5, (0, 0)) => 1
         | _ => 500
         end in
      let weight_abs := match (size,(stack1, stack2)) with 
         | (1, (11, 11)) => 917
         | (1, (11, 12)) => 948
         | (1, (11, 13)) => 926
         | (1, (12, 11)) => 697
         | (1, (12, 12)) => 688
         | (1, (12, 13)) => 599
         | (1, (13, 11)) => 613
         | (1, (13, 12)) => 693
         | (1, (13, 13)) => 542
         | (2, (11, 11)) => 392
         | (2, (11, 12)) => 860
         | (2, (11, 13)) => 644
         | (2, (12, 11)) => 534
         | (2, (12, 12)) => 586
         | (2, (12, 13)) => 529
         | (2, (13, 11)) => 511
         | (2, (13, 12)) => 522
         | (2, (13, 13)) => 528
         | (3, (11, 11)) => 954
         | (3, (11, 12)) => 751
         | (3, (11, 13)) => 570
         | (3, (12, 11)) => 585
         | (3, (12, 12)) => 529
         | (3, (12, 13)) => 504
         | (3, (13, 11)) => 521
         | (3, (13, 12)) => 531
         | (3, (13, 13)) => 518
         | (4, (0, 11)) => 960
         | (4, (0, 12)) => 707
         | (4, (0, 13)) => 518
         | (5, (0, 0)) => 962
         | _ => 500
         end in
      let weight_app := match (size,(stack1, stack2)) with 
         | (1, (11, 11)) => 218
         | (1, (11, 12)) => 260
         | (1, (11, 13)) => 113
         | (1, (12, 11)) => 567
         | (1, (12, 12)) => 638
         | (1, (12, 13)) => 530
         | (1, (13, 11)) => 567
         | (1, (13, 12)) => 531
         | (1, (13, 13)) => 558
         | (2, (11, 11)) => 941
         | (2, (11, 12)) => 474
         | (2, (11, 13)) => 330
         | (2, (12, 11)) => 518
         | (2, (12, 12)) => 507
         | (2, (12, 13)) => 492
         | (2, (13, 11)) => 510
         | (2, (13, 12)) => 532
         | (2, (13, 13)) => 496
         | (3, (11, 11)) => 4
         | (3, (11, 12)) => 494
         | (3, (11, 13)) => 384
         | (3, (12, 11)) => 472
         | (3, (12, 12)) => 494
         | (3, (12, 13)) => 488
         | (3, (13, 11)) => 476
         | (3, (13, 12)) => 489
         | (3, (13, 13)) => 489
         | (4, (0, 11)) => 0
         | (4, (0, 12)) => 428
         | (4, (0, 13)) => 425
         | (5, (0, 0)) => 0
         | _ => 500
         end in
      freq [
      (weight_var,

         let weight_1 := match (size,(stack1, stack2)) with 
         | (1, (11, 11)) => 476
         | (1, (11, 12)) => 443
         | (1, (11, 13)) => 434
         | (1, (12, 11)) => 500
         | (1, (12, 12)) => 508
         | (1, (12, 13)) => 509
         | (1, (13, 11)) => 500
         | (1, (13, 12)) => 491
         | (1, (13, 13)) => 500
         | (2, (11, 11)) => 534
         | (2, (11, 12)) => 520
         | (2, (11, 13)) => 487
         | (2, (12, 11)) => 490
         | (2, (12, 12)) => 483
         | (2, (12, 13)) => 500
         | (2, (13, 11)) => 510
         | (2, (13, 12)) => 500
         | (2, (13, 13)) => 500
         | (3, (11, 11)) => 503
         | (3, (11, 12)) => 500
         | (3, (11, 13)) => 500
         | (3, (12, 11)) => 500
         | (3, (12, 12)) => 500
         | (3, (12, 13)) => 500
         | (3, (13, 11)) => 500
         | (3, (13, 12)) => 500
         | (3, (13, 13)) => 500
         | (4, (0, 11)) => 480
         | (4, (0, 12)) => 500
         | (4, (0, 13)) => 500
         | (5, (0, 0)) => 500
         | _ => 500
         end in
        bindGen (freq [ (weight_1, returnGen 1); (1000-weight_1, returnGen 0)])
        (fun n1 : nat =>  
         let weight_2 := match (size,(stack1, stack2)) with 
         | (1, (11, 11)) => 434
         | (1, (11, 12)) => 430
         | (1, (11, 13)) => 393
         | (1, (12, 11)) => 500
         | (1, (12, 12)) => 474
         | (1, (12, 13)) => 491
         | (1, (13, 11)) => 500
         | (1, (13, 12)) => 491
         | (1, (13, 13)) => 500
         | (2, (11, 11)) => 390
         | (2, (11, 12)) => 455
         | (2, (11, 13)) => 472
         | (2, (12, 11)) => 490
         | (2, (12, 12)) => 483
         | (2, (12, 13)) => 500
         | (2, (13, 11)) => 490
         | (2, (13, 12)) => 500
         | (2, (13, 13)) => 500
         | (3, (11, 11)) => 382
         | (3, (11, 12)) => 500
         | (3, (11, 13)) => 500
         | (3, (12, 11)) => 500
         | (3, (12, 12)) => 500
         | (3, (12, 13)) => 500
         | (3, (13, 11)) => 500
         | (3, (13, 12)) => 500
         | (3, (13, 13)) => 500
         | (4, (0, 11)) => 480
         | (4, (0, 12)) => 500
         | (4, (0, 13)) => 500
         | (5, (0, 0)) => 500
         | _ => 500
         end in
        bindGen (freq [ (weight_2, returnGen 2); (1000-weight_2, returnGen 0)])
        (fun n2 : nat =>  
         let weight_4 := match (size,(stack1, stack2)) with 
         | (1, (11, 11)) => 331
         | (1, (11, 12)) => 351
         | (1, (11, 13)) => 263
         | (1, (12, 11)) => 500
         | (1, (12, 12)) => 474
         | (1, (12, 13)) => 491
         | (1, (13, 11)) => 500
         | (1, (13, 12)) => 491
         | (1, (13, 13)) => 500
         | (2, (11, 11)) => 359
         | (2, (11, 12)) => 455
         | (2, (11, 13)) => 472
         | (2, (12, 11)) => 490
         | (2, (12, 12)) => 483
         | (2, (12, 13)) => 500
         | (2, (13, 11)) => 490
         | (2, (13, 12)) => 500
         | (2, (13, 13)) => 500
         | (3, (11, 11)) => 382
         | (3, (11, 12)) => 500
         | (3, (11, 13)) => 500
         | (3, (12, 11)) => 500
         | (3, (12, 12)) => 500
         | (3, (12, 13)) => 500
         | (3, (13, 11)) => 500
         | (3, (13, 12)) => 500
         | (3, (13, 13)) => 500
         | (4, (0, 11)) => 480
         | (4, (0, 12)) => 500
         | (4, (0, 13)) => 500
         | (5, (0, 0)) => 500
         | _ => 500
         end in
        bindGen (freq [ (weight_4, returnGen 4); (1000-weight_4, returnGen 0)])
        (fun n4 : nat =>  
         let weight_8 := match (size,(stack1, stack2)) with 
         | (1, (11, 11)) => 331
         | (1, (11, 12)) => 351
         | (1, (11, 13)) => 263
         | (1, (12, 11)) => 500
         | (1, (12, 12)) => 474
         | (1, (12, 13)) => 491
         | (1, (13, 11)) => 500
         | (1, (13, 12)) => 491
         | (1, (13, 13)) => 500
         | (2, (11, 11)) => 359
         | (2, (11, 12)) => 455
         | (2, (11, 13)) => 472
         | (2, (12, 11)) => 490
         | (2, (12, 12)) => 483
         | (2, (12, 13)) => 500
         | (2, (13, 11)) => 490
         | (2, (13, 12)) => 500
         | (2, (13, 13)) => 500
         | (3, (11, 11)) => 382
         | (3, (11, 12)) => 500
         | (3, (11, 13)) => 500
         | (3, (12, 11)) => 500
         | (3, (12, 12)) => 500
         | (3, (12, 13)) => 500
         | (3, (13, 11)) => 500
         | (3, (13, 12)) => 500
         | (3, (13, 13)) => 500
         | (4, (0, 11)) => 480
         | (4, (0, 12)) => 500
         | (4, (0, 13)) => 500
         | (5, (0, 0)) => 500
         | _ => 500
         end in
        bindGen (freq [ (weight_8, returnGen 8); (1000-weight_8, returnGen 0)])
        (fun n8 : nat =>  
         let weight_16 := match (size,(stack1, stack2)) with 
         | (1, (11, 11)) => 331
         | (1, (11, 12)) => 351
         | (1, (11, 13)) => 263
         | (1, (12, 11)) => 500
         | (1, (12, 12)) => 474
         | (1, (12, 13)) => 491
         | (1, (13, 11)) => 500
         | (1, (13, 12)) => 491
         | (1, (13, 13)) => 500
         | (2, (11, 11)) => 359
         | (2, (11, 12)) => 455
         | (2, (11, 13)) => 472
         | (2, (12, 11)) => 490
         | (2, (12, 12)) => 483
         | (2, (12, 13)) => 500
         | (2, (13, 11)) => 490
         | (2, (13, 12)) => 500
         | (2, (13, 13)) => 500
         | (3, (11, 11)) => 382
         | (3, (11, 12)) => 500
         | (3, (11, 13)) => 500
         | (3, (12, 11)) => 500
         | (3, (12, 12)) => 500
         | (3, (12, 13)) => 500
         | (3, (13, 11)) => 500
         | (3, (13, 12)) => 500
         | (3, (13, 13)) => 500
         | (4, (0, 11)) => 480
         | (4, (0, 12)) => 500
         | (4, (0, 13)) => 500
         | (5, (0, 0)) => 500
         | _ => 500
         end in
        bindGen (freq [ (weight_16, returnGen 16); (1000-weight_16, returnGen 0)])
        (fun n16 : nat =>  
         let weight_32 := match (size,(stack1, stack2)) with 
         | (1, (11, 11)) => 331
         | (1, (11, 12)) => 351
         | (1, (11, 13)) => 263
         | (1, (12, 11)) => 500
         | (1, (12, 12)) => 474
         | (1, (12, 13)) => 491
         | (1, (13, 11)) => 500
         | (1, (13, 12)) => 491
         | (1, (13, 13)) => 500
         | (2, (11, 11)) => 359
         | (2, (11, 12)) => 455
         | (2, (11, 13)) => 472
         | (2, (12, 11)) => 490
         | (2, (12, 12)) => 483
         | (2, (12, 13)) => 500
         | (2, (13, 11)) => 490
         | (2, (13, 12)) => 500
         | (2, (13, 13)) => 500
         | (3, (11, 11)) => 382
         | (3, (11, 12)) => 500
         | (3, (11, 13)) => 500
         | (3, (12, 11)) => 500
         | (3, (12, 12)) => 500
         | (3, (12, 13)) => 500
         | (3, (13, 11)) => 500
         | (3, (13, 12)) => 500
         | (3, (13, 13)) => 500
         | (4, (0, 11)) => 480
         | (4, (0, 12)) => 500
         | (4, (0, 13)) => 500
         | (5, (0, 0)) => 500
         | _ => 500
         end in
        bindGen (freq [ (weight_32, returnGen 32); (1000-weight_32, returnGen 0)])
        (fun n32 : nat =>  
        let p1 := n1+n2+n4+n8+n16+n32 in
        returnGen (Var p1))
      ))))));
      (weight_bool,
        let weight_true := match (size,(stack1, stack2)) with 
         | (1, (11, 11)) => 518
         | (1, (11, 12)) => 500
         | (1, (11, 13)) => 719
         | (1, (12, 11)) => 585
         | (1, (12, 12)) => 500
         | (1, (12, 13)) => 525
         | (1, (13, 11)) => 477
         | (1, (13, 12)) => 500
         | (1, (13, 13)) => 514
         | (2, (11, 11)) => 425
         | (2, (11, 12)) => 500
         | (2, (11, 13)) => 524
         | (2, (12, 11)) => 498
         | (2, (12, 12)) => 500
         | (2, (12, 13)) => 460
         | (2, (13, 11)) => 477
         | (2, (13, 12)) => 500
         | (2, (13, 13)) => 469
         | (3, (11, 11)) => 606
         | (3, (11, 12)) => 500
         | (3, (11, 13)) => 458
         | (3, (12, 11)) => 530
         | (3, (12, 12)) => 500
         | (3, (12, 13)) => 509
         | (3, (13, 11)) => 515
         | (3, (13, 12)) => 500
         | (3, (13, 13)) => 486
         | (4, (0, 11)) => 504
         | (4, (0, 12)) => 500
         | (4, (0, 13)) => 440
         | (5, (0, 0)) => 617
         | _ => 500
         end in
        freq [ (weight_true, returnGen (Bool true)); (1000 - weight_true, returnGen (Bool false))]
      );
      (weight_abs,
      bindGen (manual_gen_typ 2 (stack2 : nat) 10)
        (fun p0 : Typ =>
         bindGen (manual_gen_expr size' (stack2 : nat) 11)
           (fun p1 : Expr => returnGen (Abs p0 p1))));
      (weight_app,
      bindGen (manual_gen_expr size' (stack2 : nat) 12)
        (fun p0 : Expr =>
         bindGen (manual_gen_expr size' (stack2 : nat) 13)
           (fun p1 : Expr => returnGen (App p0 p1))))]
  end.

Definition gSized :=
  manual_gen_expr 5 0 0.
  
Definition test_prop_SinglePreserve :=
  forAll gSized (fun (e: Expr) =>
    prop_SinglePreserve e).

(*! QuickChick test_prop_SinglePreserve. *)
  
Definition test_prop_MultiPreserve :=
  forAll gSized (fun (e: Expr) =>
    prop_MultiPreserve e).
  
(*! QuickChick test_prop_MultiPreserve. *)


