(* Chapter 8.  Inductive Predicates *) 


(* 8.1 Inductive Properties *) 

(* 8.1.1 A Few Examples *) 
(* ==> see sort.v *) 

Require Import List Arith. 
Import ListNotations. 

(* ex 8.1 *) 
Inductive last {A} : A -> list A -> Prop  := 
    | singleton :  forall a, last a [a]  
    | cons_last :  forall a b l, last a l -> last a (b::l).  

Hint Constructors last : last. 

Fixpoint last_fun {A} (l:list A) := 
    match l with 
    | []        => None
    | [a]       => Some a 
    | a::rest   => last_fun rest  end .

Theorem last_fun_equiv_last : forall {A}(a:A)l, last_fun l=Some a <-> last a l.   
Proof. 
  split. 
  - induction l; intros; try now idtac. 
    + induction l; eauto with last.  
      * simpl in H. injection H. intros. subst. constructor.       
  - induction 1; eauto with last. 
    + rewrite <- IHlast. now induction l. 
Qed. 


(* ex 8.2 *) 
Inductive init {A} : list A -> list A -> Prop := 
    | init_singleton : forall a, init [] [a] 
    | init_cons      : forall a i l, init i l -> init (a::i)(a::l) . 

Inductive palindrome {A} : list A -> Prop := 
    | palindrome_nil  : palindrome []
    | palindrom_single: forall a, palindrome [a]   
    | palindrome_wrap : forall a i l, init i l->palindrome i->last a l->palindrome(a::l). 


(* ex 8.3 *) 
Require Import Relations Relations_2 Relations_2_facts.

Inductive clos_refl_trans {A}(R:relation A) : relation A :=
  | rt_step : forall x y, R x y-> clos_refl_trans R x y
  | rt_refl : forall x,           clos_refl_trans R x x 
  | rt_trans: forall x y z,       clos_refl_trans R x y -> clos_refl_trans R y z ->
                                  clos_refl_trans R x z.

Hint Resolve rt_trans rt_refl rt_step : sorted_base . 

Print Rstar. 
Hint Resolve Rstar_0 Rstar_n Rstar_contains_R Rstar_transitive : Rstar. 

Theorem CRT_correct : forall {A} R x (y:A), clos_refl_trans R x y <-> Rstar A R x y. 
Proof. 
    split.  
    - induction 1; eauto with Rstar. now apply Rstar_transitive with y. 
    - induction 1; eauto with sorted_base arith.  
Qed. 
(* end ex. 8.3 *) 




(* 8.1.2 Inductive Predicates and Logic Programming *) 

(* 8.1.3 Advice for Inductive Definitions *) 
(* + constructors are axioms *) 

(* 8.1.4 Examples of Sorted Lists *) 
(* ==> see sort.v *) 



(* ex. 8.4 *) 
(* ==> see perm.v *) 

(* ex. 8.5 *)
(* ==> see paren.v *)

(* ex. 8.6 *) 
(* ex. 8.7 *) 







(* 8.2 Inductive Properties and Logical Connectives *) 

Inductive True : Prop := I : True . 
(* Inductive False : Prop := . *)

Inductive and (A B:Prop) : Prop :=  conj : A -> B -> and A B . 

Inductive or  (A B:Prop) : Prop := 
    | or_introL : A -> or A B 
    | or_introR : B -> or A B . 

Print or_ind. 
(*
Inductive ex A (P:A->Prop) : Prop := ex_intro : forall x:A, P x -> ex A P.  
*)
Print ex. 
Print ex_intro.  
Print ex_ind. 


(*
Inductive eq A (x:A) : A -> Prop :=  refl_equal : eq A x x . 
*)

Print eq_ind . 



(* 8.2.7 *** JMeq Heterogeneous Equality *) 
(* ==> see JMeq.v *) 


(* ex. 8.8 *) 
(* ==> see JMeq.v *)


(* Structured intros *) 
Theorem structured_intro_example1 : forall A B C : Prop, A /\ B /\ C -> A . 
Proof. 
    intros A B C [Ha [Hb Hc]].   
    assumption . 
Qed. 

Theorem structured_intro_example2 : forall A B C : Prop,  A ->  A .  
Proof.  trivial .  Qed. 

Inductive even : nat -> Prop := 
    | O_even        : even O
    | plus_2_even   : forall n, even n -> even (S (S n)) . 

Theorem sum_even : forall n p : nat , even n -> even p -> even (n + p). 
Proof. 
    intros n p Heven_n.  
    elim Heven_n . 
    - trivial. 
    - intros x Heven_x Hrec Heven_p; simpl. 
      constructor. 
      now apply Hrec . 
Qed. 


(* ex 8.9 *) 
Theorem ex8_9 : forall n : nat , even n -> exists x, n = 2*x. 
Proof. 
    intros n even.  
    elim even. 
    - now exists 0. 
    - intros n0 Heven_n0 IH.   
      destruct IH .   
      exists (x+1). 
      rewrite  H. 
      ring.     
Qed. 



(* ex 8.10 *)
Require Import Arith. 

Lemma mult2_plus : forall n,  2 * n = n+ n. 
Proof.  intros; ring.  Qed. 

Theorem even_2n : forall n : nat, even (2*n) . 
Proof. 
    induction n; simpl; try constructor.  
    - SearchRewrite (_+0). 
      SearchRewrite (S (_ + _)) .   
      rewrite Nat.add_0_r, Nat.add_succ_r. 
      rewrite mult2_plus in IHn . 
      now constructor. 
Qed. 

Lemma mul_succ_r : forall n m, n * S m = n * m + n . 
Proof. intros; ring.  Qed.

Lemma even_plus_even : forall n m , even n -> even m -> even (m+n) . 
Proof. 
    intros; elim H.  
    - now rewrite Nat.add_0_r. 
    - intros. 
      rewrite Nat.add_succ_r, Nat.add_succ_r. 
      now repeat constructor. 
Qed. 

Theorem even_sqrt_even : forall n, even n -> even (n * n) . 
Proof. 
    intros n Heven_n .
    elim Heven_n; intros; simpl. 
    - constructor. 
    - constructor. 
      repeat rewrite <- plus_n_Sm. 
      constructor.
      repeat rewrite mult_succ_r. 
      now repeat apply even_plus_even. 
Qed. 


(* ex 8.11 *)
Theorem lt_le : forall n p : nat, n < p -> n <= p . 
Proof.  intros. apply (le_ind (S n)); now repeat constructor.  Qed. 


(* ex 8.12 *) 
Open Scope nat. 
Definition my_le n p := forall P: nat->Prop, P n -> (forall q:nat, P q -> P (S q)) -> P p. 

Theorem le_my_le : forall n p, n <= p -> my_le n p. 
Proof.  unfold my_le; intros; induction H; now try apply H1.  Qed. 


(* ex 8.13 *) 
Require Import Lia. 
Theorem le_trans' : forall n p q, n <= p -> p <= q -> n <= q . 
Proof.   
    intros n p q. apply (le_ind n (fun p => p <= q -> n <= q)); trivial. 
    - intros. apply H0. apply (le_ind (S m)); now repeat constructor. 
Qed. 


(* ex 8.14 *)
Inductive le_diff n m : Prop := 
    le_d : forall x, x+n = m -> le_diff n m . 

Lemma le_diff_succ : forall n m, le_diff n m -> le_diff n (S m). 
Proof. intros. destruct H. rewrite <- H. now apply (le_d _ _ (S x)). Qed. 

Theorem le_equiv_le_diff : forall n m , le n m <-> le_diff n m . 
Proof. 
    split; intros; elim H; try intros; 
    [ now apply (le_d _ _ 0) 
    | now apply le_diff_succ 
    | induction x; rewrite <- H0; apply le_plus_r] . 
Qed. 

(* ex 8.15 *) 
Inductive le' : nat -> nat -> Prop := 
    | le'_O_p   : forall p  , le' O p
    | le'_Sn_Sp : forall n p, le' n p -> le' (S n)(S p) .

Lemma le'_succ_r : forall n m, le' n m -> le' n (S m). 
Proof. intros; elim H; intros; now constructor. Qed. 

Hint Resolve le'_O_p le'_Sn_Sp le'_succ_r : arith'. 
Theorem le_equiv_le' : forall n m, le n m <-> le' n m. 
Proof. 
    split; intros. 
    - elim H; try induction n; eauto with arith' arith.  
    - elim H; lia.   
Qed. 

(* ex. 8.16 *)
(* ==> see sort.v *) 

(* ex. 8.17 *) 
Check True_ind. 
Definition my_true            := forall P: Prop, P -> P . 
Check False_ind. 
Definition my_false           := forall P: Prop, P.  
Check and_ind.
Definition my_and (P Q:Prop)  := forall R:Prop, (P->Q->R) -> R . 
Check or_ind. 
Definition my_or  (P Q:Prop)  := forall R:Prop, (P->R) -> (Q->R) -> R . 
Check ex_ind. 
Definition my_ex{A}(P:A->Prop):= forall R:Prop, (forall x,P x->R) -> R .  
Definition my_not (P:Prop)    := P -> my_false. 

Lemma my_true_eq_True : True <-> my_true. 
Proof.  intuition. now red.                         Qed. 
Lemma my_false_eq_False : my_false <-> False. 
Proof.  split; intros; [apply H |    ]; intuition.  Qed. 
Lemma my_and_eq_and     : forall A B, my_and A B <-> and A B. 
Proof.  split; intros; [apply H | red]; intuition.  Qed. 
Lemma my_or_eq_or       : forall A B, my_or A B <-> or A B. 
Proof.  split; intros; [apply H | red]; intuition.  Qed. 
Lemma my_ex_eq_ex       : forall A P, my_ex (A:=A) P<-> ex P. 
Proof.  
    split; intros. 
    - apply H. intros. now exists x.   
    - intros Q ex. destruct H. now apply ex with x.     
Qed. 


(* ex. 8.18 *) 
Section weird_induc_proof. 
    Variable   P : nat -> Prop. 
    Variable   f : nat -> nat .
    Hypothesis f_strict_mono : forall n p: nat, n < p -> f n < f p.  
    Hypothesis f_O : O < f O . 
    Hypothesis P0       : P 0 . 
    Hypothesis pred_P   : forall n, P (S n) -> P n.  
    Hypothesis f_P      : forall n, P n -> P (f n).     

    Lemma f_incr : forall n, n < f n.
    Proof. 
        unfold lt. 
        induction n. 
        - assumption . 
        - destruct (f_strict_mono n (S n)); try apply le_n_S; trivial.    
          + apply (le_trans (S n) (S(f n)) m)      ; try trivial. 
            apply (le_trans (S n) (S(S n))(S(f n))); try apply le_n_S; trivial. 
            * repeat constructor. 
    Qed. 

    Lemma p_pred' : forall n k,  P (n+k) -> P n . 
    Proof. 
        induction k. 
        - SearchRewrite ( _ + 0 ) . 
          rewrite <- plus_n_O.  
          now intros. 
        - intros.  
          apply IHk. 
          apply pred_P. 
          SearchRewrite (S _ + _ ).
          rewrite <- plus_Sn_m . 
          SearchRewrite ( _ + _ = _ + _) . 
          now rewrite plus_Snm_nSm.
    Qed. 
    Lemma P_pred : forall n p, n <= p -> P p -> P n. 
    Proof. 
        intros. 
        apply le_equiv_le_diff in H . 
        destruct H. subst p . 
        apply p_pred' with x.  
        Search ( _+_ = _+_). 
        now rewrite (Nat.add_comm). 
    Restart. 
        intros n p lt pp. 
        induction lt; try trivial.   
        - now apply IHlt, pred_P. 
    Qed.

    Theorem weird_induc : forall n, P n. 
    Proof. 
        induction n; try trivial. 
        - apply (P_pred (S n) (f n)).  
          apply f_incr. 
          now apply f_P. 
    Qed. 

End weird_induc_proof. 



(* ex. 8.19 - ex. 8.23 *)
(* ==> see paren.v *) 


(* 8.4 * Inductive Relations and Functions *) 

(* 8.4.1 Factorial Function *)
Require Import ZArith. 
Open Scope Z_scope.
Inductive Pfact : Z -> Z -> Prop := 
    | Pfact0 : Pfact 0 1 
    | Pfact1 : forall n v:Z, n <> 0 -> Pfact (n-1) v -> Pfact n (n*v) . 

Theorem pfact3 : Pfact 3 6 . 
Proof. 
    apply Pfact1 with (n:=3) (v:=2) . 
    discriminate. 
    apply (Pfact1 2 1) . 
    discriminate. 
    apply (Pfact1 1 1). 
    discriminate . 
    apply (Pfact0). 
Qed. 

Theorem fact_def_pos : forall x y:Z, Pfact x y -> 0 <= x. 
Proof. intros x y H. elim H; lia.  Qed. 



Require Import Zwf Wf.
Check Zwf. 
Check well_founded. 
Print well_founded_ind. 


(* ex. 8.24 *)
(* ==> see paren.v *) 



(* 8.4.2  ** Representing the Semantics of a Language *) 
(* ==> see hoare.v *) 

(* ex. 8.25 *)
(* ==> see hoare.v *) 

(* ex. 8.26 *)
(* ==> see hoare.v *) 

(* ex. 8.27 *)
(* ==> see hoare.v *) 



(* 8.5 * Elaborate Behavior of "elim" tactic *) 

(* 8.5.1 Instantiating the Argument *) 

Open Scope nat_scope. 

Inductive is_0_1 : nat -> Prop := 
    | is_0 : is_0_1 0 
    | is_1 : is_0_1 1 . 

Hint Resolve is_0 is_1 . 

Lemma sqr_01 : forall x, is_0_1 x -> is_0_1 (mult x x) . 
Proof. induction 1; simpl; auto. Qed. 

Theorem elim_example : forall n, n<=1 -> n*n <= 1. 
Proof. intros n H. elim sqr_01 . (* == elim (sqr_01 n) *) 
Abort. 


(* 8.5.2 "inversion" tactiv *) 

Print even. 
Theorem not_1_even : ~ even 1. 
Proof. 
    red. (* reduction *) 
    intros H. 
    elim H. (* == apply even_ind with P := fun x:nat => False *)
    Print even_ind. 
Restart. 
    unfold not. 
    intros H. 
    inversion H. 
Restart.
    red. 
    intros H. 
    generalize (refl_equal 1). 
    pattern 1 at -2.        (* == pattern 1 except 2 *) 
    induction H; discriminate. 
Qed. 


Theorem plus_2_even_inv : forall n, even (S (S n)) -> even n . 
Proof. 
    intros n H. 
    now inversion H. 
Restart.   (* without inversion *)  
    intros n H.
    generalize (refl_equal (S (S n))). 
    pattern n at -2.   (* == pattern 1 except at 2 *)
    induction H.  
    - discriminate .   
    - intros.  
      injection H0; intros. 
      now rewrite H1. 
Qed. 


Inductive odd : nat -> Prop := 
    | I_odd : odd 1 
    | plus_2_odd : forall n, odd n -> odd (S(S n)) . 

Theorem even_not_odd : forall n, even n -> ~ odd n . 
Proof. red. intros. induction H; inversion H0; subst; now apply IHeven.  Qed. 



(* ex 8.28 *) 
(* ==> see sort.v *) 

(* ex 8.29 *) 
Section stamp . 
  Inductive stamp : nat -> Prop := 
      | stamp5cents : stamp 5 
      | stamp3cents : stamp 3 
      | add_stamps : forall n m, stamp n -> stamp m -> stamp (n+m). 
  
  Hint Resolve stamp5cents stamp3cents add_stamps. 
  
  Check nat_ind. 
  Lemma nat_3_ind : forall (P:nat->Prop), 
    P 0 -> P 1 -> P 2 -> (forall n, P n -> P(S(S(S n)))) -> forall n, P n. 
  Proof. intros; cut (P n /\ P (S n) /\ P(S (S n))); elim n; intuition. Qed. 
  
  Ltac stamp_6 := simpl; apply (add_stamps 3 3); constructor. 
  Ltac stamp_8 := simpl; apply (add_stamps 3 5); constructor. 
  Ltac stamp_9 := simpl; apply (add_stamps 6 3); try stamp_6; try constructor. 
  Ltac stamp_10:= simpl; apply (add_stamps 5 5); constructor. 
  
  Lemma Frobenius_aux : forall k, stamp (8+k).
  Proof. 
    induction k using nat_3_ind; [ stamp_8 | stamp_9 | stamp_10 |]. 
    - cut (3 + (8 + k) = 8 + S(S(S k))); auto with arith.   
      intros. rewrite <- H; auto.  
  Qed. 
  
  Theorem Frobenius : forall n, n>=8 -> stamp n. 
  Proof. 
    intros. cut (exists k, n = 8 + k). 
    - intros [k Heq]; subst. apply Frobenius_aux. 
    - induction H; [exists 0 | destruct IHle as [x Heq]; exists (S x)]; lia.  
  Qed. 
End stamp. 
(* end ex. 8.29 *) 

