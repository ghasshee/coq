Require Import Lia Arith ZArith.  


(* 7.6 Ltac *) 

(* 7.6.1 Arguments in Tactics *) 
Ltac autoClear h   := try (clear h; auto with arith; fail). 
Ltac autoAfter tac := try (tac; auto with arith; fail) . 

Goal 1 < 3 .          Proof. autoAfter ltac:(trivial).   Qed. 

Ltac le_S_star := apply le_n || (apply le_S; le_S_star). 

Goal 5 <= 100.        Proof. le_S_star. Qed.  




(* 7.6.2 Pattern Matching in Ltac *) 

(* 7.6.2.1 Pattern Matching in the Goal *) 
Open Scope nat. 
Definition divides (n m:nat) := exists p, p*n = m. 

(* ex. 7.1 *)
Lemma divides_0 : forall n, divides n 0. 
Proof. unfold divides. intros. now exists 0. Qed.       
Lemma divides_plus      : forall n m, divides n m -> divides n (n+m). 
Proof. intros n m [p H]; exists (S p); lia. Qed.   
Lemma not_divides_plus  : forall n m, ~divides n m -> ~divides n (n+m).
Proof. intros n m HN [p H]. apply HN. induction p; [exists 0 | exists p]; lia. Qed.  
Lemma not_divides_lt    : forall n m, O<m -> m<n -> ~divides n m. 
Proof. intros n m Hle0 Hle [x H]. rewrite <- H in Hle. induction x; lia. Qed.  
Lemma not_lt_2_divides  : forall n m, n <> 1 -> n<2 -> 0<m -> ~divides n m . 
Proof. intros n m Hn1 Hlt2 Hlt0 [x H]. subst. lia. Qed.  
Lemma le_plus_minus     : forall n m, le n m -> m = n+(m-n).  
Proof. lia.  Qed. 
Lemma lt_lt_or_eq       : forall n m, n < S m -> n < m \/ n = m .
Proof. lia. Qed.  
(* end ex. 7.1 *)       


Ltac check_not_divides := 
    match goal with 
    | [ |- (~divides ?X1 ?X2) ] =>  cut (X1<=X2) ; [ idtac | le_S_star ] ; intros Hle;
                                    rewrite (le_plus_minus _ _ Hle); apply not_divides_plus;
                                    simpl; clear Hle; check_not_divides
    | [ |- _                  ] =>  apply not_divides_lt; unfold lt; le_S_star
    end. 



(* 7.6.2.2 Finding the Names of Hypotheses *) 
Ltac contrapose H := 
    match goal with                       (* [ id:(~A)      |- (~B)  ] *)
    | [ id:(~_) |- (~_) ]   =>  intro H;  (* [ id:(~A), H:B |- False ] *) 
                                apply id  (* [ id:(~A), H:B |- A     ] *)  end. 

Theorem example_contrapose : forall x y:nat, x<>y -> x <= y -> ~y<=x .
Proof. 
    intros x y H H0 .  
    contrapose H'. 
    auto with arith. 
Qed. 



Ltac check_lt_not_divides := 
    match goal with 
    | [Hlt:(lt ?X1 2%nat) |- (~divides ?X1 ?X2) ] => apply not_lt_2_divides; auto
    | [Hlt:(lt ?X1 ?X2)   |- (~divides ?X1 ?X3) ] => 
                                    elim (lt_lt_or_eq _ _ Hlt);
                                    [clear Hlt; intros Hlt; check_lt_not_divides 
                                    | intros Heq; rewrite Heq; check_not_divides] end.

Definition is_prime : nat -> Prop :=
    fun p : nat => forall n : nat, n <> 1 -> lt n p -> ~ divides n p. 

Hint Resolve lt_O_Sn. 

Theorem prime7 : is_prime 7. 
Proof. 
    unfold is_prime; 
    intros n neq_1 lt_7. 
    Check lt_lt_or_eq. 
    elim (lt_lt_or_eq _ _ lt_7). 
        intros lt_6. 
        elim (lt_lt_or_eq _ _ lt_6). 
            intros lt_5. 
            elim (lt_lt_or_eq _ _ lt_5). 
                intros lt_4. 
                elim (lt_lt_or_eq _ _ lt_4). 
                    intros lt_3.
                    elim (lt_lt_or_eq _ _ lt_3). 
                        intros lt_2. 
                        apply not_lt_2_divides; auto. 

                        intros eq_2; rewrite eq_2.
                        (* check_not_divides *) 
                        cut (2<=7); [idtac | le_S_star].
                        intros lt_2_7; rewrite (le_plus_minus _ _ lt_2_7);
                        apply not_divides_plus; simpl;
                            cut (2<=5); [idtac | le_S_star]. 
                            intros lt_2_5; rewrite (le_plus_minus _ _ lt_2_5);
                            apply not_divides_plus; simpl;
                                    cut (2<=3); [idtac | le_S_star];
                                    intros lt_2_3; rewrite (le_plus_minus _ _ lt_2_3);
                                    apply not_divides_plus;
                                        try (
                                        cut(2<=1); [idtac | le_S_star] ).   
                                        apply not_divides_lt; unfold lt; le_S_star. 

                    intros eq_3; rewrite eq_3;

                    cut (3<=7); [idtac | le_S_star].
                    intros lt_3_7; rewrite (le_plus_minus _ _ lt_3_7);
                    apply not_divides_plus; simpl.  
                        cut(3<=4); [idtac | le_S_star].
                        intros lt_3_4; rewrite (le_plus_minus _ _ lt_3_4);
                        apply not_divides_plus; simpl;
                            try(
                            cut(3<=1); [idtac | le_S_star]). 
                            apply not_divides_lt; unfold lt; le_S_star. 

                intros eq_4; rewrite eq_4;

                cut (4<=7); [idtac | le_S_star]. 
                intros lt_4_7; rewrite (le_plus_minus _ _ lt_4_7);
                apply not_divides_plus; simpl;
                    try(
                    cut(4<=1); [idtac | le_S_star]).
                    apply not_divides_lt; unfold lt; le_S_star. 

            intros eq_5; rewrite eq_5;

            cut (5<=7); [idtac | le_S_star]. 
            intros lt_5_7; rewrite (le_plus_minus _ _ lt_5_7);
            apply not_divides_plus; simpl;
                try(
                cut(5<=2); [idtac | le_S_star]).
                apply not_divides_lt; unfold lt; le_S_star. 

        intros eq_6; rewrite eq_6;

        cut (6<=7); [idtac | le_S_star]. 
        intros lt_6_7; rewrite (le_plus_minus _ _ lt_6_7);
        apply not_divides_plus; simpl;
            try(
            cut(6<=1); [idtac | le_S_star]).
            apply not_divides_lt; unfold lt; le_S_star. 

Qed. 





Theorem prime37 : is_prime 37. 
Proof.
    Time(
        unfold is_prime;
        intros n H H1;
        check_lt_not_divides 
    ).
Qed. 

(*
Theorem prime127 : is_prime 127. 
Proof.
    Time(   unfold is_prime;
            intros n H H1;
            check_lt_not_divides    ).
Qed. 
(* Finished transaction in 9.57 secs (9.212u,0.121s) (successful) *)

Theorem prime257 : is_prime 257. 
Proof. 
    Time(   unfold is_prime;
            intros n H H1;
            check_lt_not_divides    ).
Qed. 
Finished transaction in 64.987 secs (62.402u,0.831s) (successful)
*)





(* 7.6.2.3 Pattern Matching and Backtracking *) 

Ltac clear_all := 
    match goal with 
    | [ a:_ |- _ ]  =>  clear a; clear_all
    | [     |- _ ]  =>  idtac
    end. 








(* 7.6.2.4 In-Depth Pattern Maching *)

Theorem ring_example5: 
    forall n m: nat, n*0 + (n+1)*m = n*n*0 + m*n + m. 
Proof. 
    intros; ring. 
Qed. 


Theorem ring_example6 : 
    forall n m: nat, n*0 + (S n)*m = n*n*0 + m*n + m. 
Proof. 
    intros; ring. 
Qed. 


Theorem S_to_plus_one : forall n:nat, S n = n+1. 
Proof. 
    intros; rewrite plus_comm; reflexivity. 
Qed. 

Ltac S_to_plus_simpl := 
    match goal with 
    | [ |- context [(S ?X1)] ]  =>  
            match X1 with 
            | O                         => fail 1
            | ?X2                       => rewrite (S_to_plus_one X2); S_to_plus_simpl
            end
    | [ |-  _                ]  =>  idtac
    end.


Theorem ring_example7 : 
    forall n m: nat, n*0 + (S n)*m = n*n*0 + m*n + m. 
Proof. 
    intros. 
    S_to_plus_simpl.
    ring. 
Qed. 





(* ex. 7.2 *) 

Open Scope Z. 

Check Zpos_xI. (* forall p : positive, Zpos(xI p) = 2 * Zpos p + 1 . *)
Check Zpos_xO. (* forall p : positive, Zpos(xO p) = 2 * Zpos p       *)

Ltac Zpos_to_simpl := 
    match goal with 
    | [ |- context [Zpos (xO ?P1)] ] => 
            match P1 with 
            (* | xO _   => fail 1  *) 
            | xH    => fail 1 
            | ?P2   => rewrite (Zpos_xO P2); Zpos_to_simpl
            end
    | [ |- context [Zpos (xI ?P3)] ] => 
            match P3 with 
            (* | xO _  => fail 1  *) 
            (* | xH    => fail 1  *)  
            | ?P4   => rewrite (Zpos_xI P4); Zpos_to_simpl
            end
    | [ |- _                      ] => idtac
    end. 


Lemma test : forall p: positive, Zpos(xO p) + 1 + 2 + Zpos(xI p) = 4 * Zpos p + 4 .    
Proof.   
    intros p . 
    Zpos_to_simpl. 
    ring. 
Qed. 


(* 7.6.3 Using Reduction in Defined Tactics *) 
Open Scope nat. 

Ltac simpl_on e := 
    let v := eval simpl in e in 
    match goal with 
    | [ |- context [e] ]    => replace e with v; [idtac | auto]
    end. 

Theorem simpl_on_example: 
    forall n : nat, exists m : nat, (1+n) + 4*(1+n) = 5 * (S m) .
Proof. 
    intros n.
    simpl_on (1+n). 
    now exists n. 
Qed. 


