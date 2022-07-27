Require Import Arith ZArith . 

Check Z.le. 
Check le .

(* Minimal Polymorphic Propositional Logic *) 
(* == Minimal Logic + ∀ + ∃ *) 

Theorem  imp_trans : forall P Q R : Prop , (P -> Q) -> (Q -> R) -> P -> R .
Proof . intros P Q R H H' p. apply H', H. assumption. Qed.   

Theorem resolution : forall A, forall P Q R S : A -> Prop, 
  (forall a:A, Q a -> R a -> S a) -> 
  (forall b: A , P b -> Q b) -> 
  forall c : A , P c -> R c -> S c . 
Proof. 
  intros A P Q R S H H' c p r . 
  apply H; try (apply H'); assumption . 
Qed. 




(* 5.1.3.1 Helping "apply" *) 
Check mult_le_compat_l. 
Check mult_le_compat_r. 

Theorem le_mult_mult : forall a b c d : nat , (le a c) -> (le b d) -> (le (a*b) (c*d)) . 
Proof. 
  intros a b c d H H0 .
  apply le_trans with (m := c*b). 
  apply mult_le_compat_r ; assumption. 
  apply mult_le_compat_l ; assumption.  
Qed.



Definition opaque_f : nat -> nat -> nat . 
Proof. intros; assumption. Qed. 

Lemma bad_proof_example_for_opaque : forall x y: nat , opaque_f x y = y. 
Proof . 
  intros.
  (* unfold opaque_f. *)
Abort. 



(* 5.2 Logical Connectives *) 

(* 5.2.2  *)
Section ex_falso_quedlibet. 
  
  Hypothesis ff : False . 

  Lemma exi : 220 = 284 . 
  Proof. apply False_ind. exact ff. Qed. 

  Lemma ex2 : 220 = 284 . 
  Proof. elim ff.  Qed. 

End ex_falso_quedlibet. 

  

(* ex. 5.3 *)
Lemma contrap : forall P Q : Prop , ( P -> Q ) -> not Q -> not P . 
Proof. intros P Q pq nq p. elim nq. apply pq. assumption.  Qed. 
Lemma false_ind_1 : forall P Q R : Prop , (P->Q) -> (P->~Q) -> P -> R . 
Proof. intros P Q R pq p_q p. elim(p_q p). apply pq. assumption. Qed. 

(* ex. 5.4 *)
Definition dyslexic_imp     := forall P Q, (P->Q)->(Q->P).
Definition dyslexic_contrap := forall P Q:Prop, (P->Q)->((~P)->~Q). 
Theorem dyslexic_imp_False : dyslexic_imp -> False.  
Proof. intros. elim(X False True); tauto. Qed.   
Theorem dyslexic_contrap_False : dyslexic_contrap -> False. 
Proof. intros. elim(H False True); tauto. Qed.  
(* end ex. 5.4 *) 













(* 5.2.4 Conjunction and Disjunction *) 
Theorem conj3' : forall P Q R : Prop , P -> Q -> R -> P /\ Q /\ R . 
Proof. repeat split ; assumption.  Qed. 


Theorem or_commutes : forall A B : Prop , A \/ B -> B \/ A . 
Proof . 
  intros A B H . elim H .
  right. assumption. 
  left.  assumption. 
Qed. 


(* ex. 5.5 *)
Example ex5_5 : forall A:Set, forall a b c d: A, a=c \/ b=c \/ c=c \/ d=c.
Proof . tauto. (* 
  intros A a b c d . 
  right; right; left.
  trivial .  *)
Qed. 


(* ex. 5.6 *) 
Lemma or_assoc : forall A B C:Prop, A \/ (B\/C) -> (A\/B)\/C . Proof. tauto. Qed.  
Lemma NNLEM : forall A:Prop , ~~ (A \/ ~A) .                   Proof. tauto. Qed.  
Lemma or_imp : forall A B: Prop, (A \/ B) /\ ~A -> B .         Proof . tauto. Qed. 


(* ex. 5.7 *) 
Definition classic        := forall P  :Prop, ~~P -> P.
Definition peirce         := forall P Q:Prop, ((P->Q)->P)->P. 
Definition LEM            := forall P  :Prop, P \/ ~P .
Definition DeMorganNAN    := forall P Q:Prop, ~(~P/\~Q) -> P\/Q. 
Definition implies_to_or  := forall P Q:Prop, (P->Q) -> (~P\/Q). 

Lemma ex_5_7_1 : classic -> peirce . 
Proof.  
    unfold classic, peirce. 
    intros classic P Q pqp. 
    apply classic.
    intros nP .
    elim nP. 
    apply pqp. 
    intro p . 
    elim nP . 
    assumption . 
Qed. 

Lemma ex_5_7_2 : peirce -> LEM . 
  Proof. 
    unfold peirce, LEM.
    intros peirce P. 
    apply (peirce (P\/~P) False). 
    intros H . 
    left. 
    apply (peirce P False). 
    intros np. 
    elim H.  
    right. 
    assumption . 
  Qed. 

Lemma ex_5_7_3 : LEM -> DeMorganNAN . 
  Proof. 
    unfold LEM, DeMorganNAN. 
    intros LEM P Q H.  
    elim (LEM P) .
    intros p . 
    left. 
    assumption . 
    intros np . 
    elim (LEM Q) .
    intros q. 
    right. 
    assumption . 
    intros nq . 
    elim H. 
    split; assumption .
  Qed. 

Lemma ex_5_7_4 : DeMorganNAN -> implies_to_or . 
  Proof. 
    unfold DeMorganNAN, implies_to_or . 
    intros de_morgan_not_and_not P Q pq . 
    apply (de_morgan_not_and_not (~P) Q). 
    intros H. 
    elim H. 
    intros nnp nq . 
    apply nnp . 
    intros p . 
    apply nq .
    apply pq. 
    assumption . 
  Qed. 

Lemma ex_5_7_5 : implies_to_or -> classic. 
  Proof. 
    unfold implies_to_or, classic. 
    intros implies_to_or P nnp. 
    elim (implies_to_or P P). 
    intros np . 
    elim nnp. 
    assumption . 
    trivial.     
    trivial. 
  Qed. 
(* End ex. 5.7 *)



(* 5.2.5 "repeat" tactic *) 

(* ex. 5.8 *) 





(* 5.2.6 Existential Quantification *) 

Theorem ex_imp_ex : forall (A:Type) (P Q:A -> Prop), (ex P) -> (forall x:A, P x -> Q x) -> (ex Q) . 
Proof . 
  intros A P Q H H0 . 
  elim H.
  intros a Ha.
  exists a. 
  apply H0. 
  assumption. 
Qed. 


(* ex. 5.9 *) 
Section ex_5_9.  
  Hypothesis A:Set  .
  Hypothesis P Q:A -> Prop . 

  Lemma ex_5_9_3 : (exists x:A, (forall R:A->Prop, R x)) -> 2 = 3 . 
  Proof . 
    intros H. 
    elim H. 
    intros a H0.
    exact (H0 (fun _ => 2 = 3)) .
  Qed. 
  Lemma ex_5_9_4 : (forall x:A, P x) -> ~ (exists y : A, ~ P y) . 
  Proof . 
    intros PTruth .  
    intros H . 
    elim H .
    intros x nPx . 
    elim nPx. 
    apply PTruth . 
  Qed. 
End ex_5_9. 


Lemma L36 : 6*6 = 9*4.  Proof. reflexivity. Qed. 
Print L36. 




(* 5.3 Equality and Rewriting *) 

(* 5.3.1 Proving Equalities *) 

Open Scope Z_scope.

Definition Zsquare_diff x y := x*x - y*y . 

Theorem unfold_example: forall x y, 
  x*x = y*y -> Zsquare_diff x y * Zsquare_diff (x+y)(x-y) = 0 .
Proof . 
  intros x y Heq . 
  unfold Zsquare_diff at 1. 
  unfold Zsquare_diff at 1. 
Abort . 



(* 5.3.2 Using Equality: Rewriting tactics *) 
(* p 126 *) 

Require Import ZArith . 
Open Scope Z. 

Theorem Zmult_distr_1 : forall n x: Z, n*x+x = (n+1) * x . 
Proof. 
  intros. 
  rewrite Zmult_plus_distr_l . 
  rewrite Zmult_1_l .  
  reflexivity. 
Qed. 


(* 5.3.3 "pattern" tactic *) 

Theorem regroup : forall x:Z, x+x+x+x+x = 5*x.
Proof. 
  intros x. 
  pattern x at 1. 
  Check Zmult_1_l. 
  rewrite <- (Zmult_1_l x).
  (*
  rewrite (Zmult_distr_1 1 x). 
  rewrite (Zmult_distr_1 (1+1) x). 
  rewrite (Zmult_distr_1 (1+1+1) x). 
  rewrite (Zmult_distr_1 (1+1+1+1) x).  
  *) 
    repeat rewrite Zmult_distr_1 . 
  simpl. (* ?? explain the Goal here  *)  
  reflexivity .  
Qed. 


(* Ex 5.10 *) 
Require Import Arith. 
Open Scope nat. 

Theorem plus_permute2 : forall n m p : nat, n + m + p = n + p + m .
Proof. 
  intros n m p. 
  rewrite <- plus_assoc. 
  rewrite <- plus_assoc.  
  pattern (m+p) . 
  rewrite <- plus_comm. 
  reflexivity. 
Qed. 




(* 5.3.4 Contidinal Rewriting *) 

Lemma le_lt_S_eq : forall n p:nat, n<=p -> p<S n -> n = p.    Proof. intros. omega. Qed. 
Lemma plus_lt_reg_l : forall n m p: nat, p+n < p+m -> n<m .   Proof. intros. omega. Qed. 
Lemma plus_le_reg_l : forall n m p: nat, p+n <= p+m -> n<=m . Proof. intros. omega. Qed. 

Theorem cond_rewrite_example : forall n : nat, 8 <= n+6 -> 3+n<6 -> n*n=n+n. 
Proof. 
  intros n H H0. 
  Check le_lt_S_eq 2 n . 
  rewrite <- (le_lt_S_eq 2 n) . 
  - reflexivity.   
  - rewrite plus_comm in H. apply (plus_le_reg_l 2 n 6) . assumption .    
  - apply (plus_lt_reg_l  n 3 3) . assumption .
Qed. 



(* Ex 5.11 *)
Theorem eq_trans : forall(A:Type)(x y z:A), x=y -> y=z -> x=z. 
Proof. 
  intros A x y z eq_xy eq_yz . 
  rewrite eq_xy . 
  rewrite eq_yz . 
  reflexivity . 
Qed. 



(* 5.3.5 Searching Theorems for Rewriting *) 

Open Scope Z. 

SearchRewrite (_ * _) .  
Check Zmult_1_l . 

SearchRewrite (_ * 1)%Z . 
SearchRewrite (1 * _)%Z . 

(* 5.3.6 Other Tactics *) 

(* 
  replace 
  cutrewrite 
  symmetry
  transitivity
*) 
Lemma symmetry_example : forall(A:Type)(x y:A), x = y . 
Proof . symmetry. Abort.   


(* 5.4 Tactic Summary Table *) 



(* 5.5  *** Impredicative Definitions *) 

Definition my_true   : Prop := forall P: Prop, P -> P . 
Definition my_false  : Prop := forall P: Prop, P.  

Theorem my_I : my_true. 
Proof. 
  exact (fun P p => p).  (* intros. assumption. *)
Qed. 

Theorem my_false_ind : forall P: Prop, my_false -> P. 
Proof. 
  exact (fun P F => F P). (* intros P F.  apply F . *)
Qed. 

Definition my_not (P:Prop) : Prop := P -> my_false. 


(* ex 5.13 *) 
Lemma ex5_13_1 : my_not my_false . 
Proof. 
  unfold my_not, my_false.
  exact (fun F P => F P). 
Qed. 

Lemma ex5_13_2 : forall P:Prop, my_not (my_not (my_not P)) -> my_not P . 
Proof.
  intros P nnnP p. 
  exact (nnnP (fun nP => nP p)).  
Qed. 

Lemma ex5_13_3 : forall P Q:Prop, my_not(my_not(my_not P)) -> P -> Q .
Proof. 
  intros P Q nnnP p. 
  unfold my_not, my_false in nnnP. 
  exact (nnnP (fun nP => nP p) Q). 
Qed. 

Lemma ex5_13_4 : forall P Q: Prop, (P -> Q) -> my_not Q -> my_not P . 
Proof. 
  intros P Q pq nQ p. 
  exact (nQ (pq p)) . 
Qed. 

Lemma ex5_13_5 : forall P Q R: Prop, (P->Q) -> (P->my_not Q) -> P -> R. 
Proof. 
  unfold my_not, my_false. 
  intros P Q R pq pqAny p. 
  exact (pqAny p (pq p) R). 
Qed. 



(* 5.5.3 Leibniz Equality *) 

Print eq_rec. 

(* ex. 5.14 *) 
Section leibniz. 
  Set Implicit Arguments. 
  Unset Strict Implicit. 
  Variable A : Set.    (* Variable A : Type *) 

  Definition leibniz (a b:A) : Prop := forall P : A -> Prop, P a -> P b. 

  Require Import Relations. 
  Print reflexive . 
  Print symmetric .  (* forall A : Type, relation A -> Prop *)    
  Print transitive . 
  Print equiv . 
  Print relation . 

  Theorem leibniz_sym : symmetric A leibniz. 
  Proof.  
    unfold symmetric, leibniz. intros x y Leib Q . 
    apply Leib .             (*  Gamma  |-?  (Q x -> Q y) =: P(y) *) 
    trivial.                 (*  Gamma  |-?  (Q x -> Q x) =: P(x) *) 
  Qed. 

  Theorem leibniz_refl : reflexive A leibniz.  Proof.  red. now intros.  Qed. 
  Theorem leibniz_trans : transitive A leibniz. Proof. red. intros. now apply H0. Qed. 
  Theorem leibniz_equiv : equiv A leibniz. 
  Proof. repeat split; [apply leibniz_refl|apply leibniz_trans|apply leibniz_sym]. Qed. 
  Theorem leibniz_least_reflexive : forall R, reflexive A R -> inclusion A leibniz R. 
  Proof. compute. intros. now apply H0, H.                  Qed. 
  Theorem leibniz_eq : forall a b:A, leibniz a b -> a = b. 
  Proof. intros a b leib. now apply leib. (* exact(leib(eq a)(eq_refl a)).*) Qed. 
  Theorem eq_leibniz : forall a b:A, a = b -> leibniz a b. 
  Proof. unfold leibniz; intros a b Heq P. now rewrite Heq. Qed. 
  Theorem leibniz_ind : forall(x:A)(P:A->Prop), P x -> forall y:A, leibniz x y -> P y.
  Proof. unfold leibniz; intros. now apply H0.              Qed. 

  Check eq_rec.  (* forall (A:Type) (x : A *)  
  Check eq_ind.
  Check eq_rect. (* Type *)  

  Unset Implicit Arguments. 
End leibniz. 


(* 5.5.4 Some Other Connectives and Quantifiesrs *) 

Definition my_and (P Q: Prop)        := forall R:Prop, (P->Q->R) -> R . 
Definition my_or  (P Q: Prop)        := forall R:Prop, (P->R) -> (Q->R) -> R . 
Definition my_ex  {A} (P:A->Prop)    := forall R:Prop, (forall x:A, P x->R) -> R .  




(* Ex 5.15 *) 
Lemma ex5_15_1 : forall P Q:Prop, my_and P Q -> P . 
Proof. intros P Q pANDq. exact ( pANDq P (fun x y => x)). Qed. 

Lemma ex5_15_2 : forall P Q:Prop, my_and P Q -> Q . 
Proof. intros P Q pANDq. exact ( pANDq Q (fun x y => y)). Qed. 

Lemma ex5_15_3 : forall P Q R:Prop, (P->Q->R) -> my_and P Q -> R. 
Proof. intros P Q R pqr pANDq. exact (pANDq R pqr).       Qed. 

Lemma ex5_15_4 : forall P Q:Prop, P -> my_or P Q .  
Proof. exact ( fun P Q p R pr qr => pr p ) .              Qed. 

Lemma ex5_15_5 : forall P Q:Prop, Q -> my_or P Q .  
Proof. exact ( fun P Q q R pr qr => qr q ) .              Qed. 

Lemma ex5_15_6 : forall P Q R:Prop, (P->R) -> (Q->R) -> my_or P Q -> R. 
Proof. intros P Q R pr qr pORq . exact (pORq R pr qr).          Qed. 

Lemma ex5_15_7 : forall P:Prop, my_or P my_false -> P . 
Proof. intros P pOR_ . exact (pOR_ P(my_I P)(my_false_ind P)).  Qed. 

Lemma ex5_15_8 : forall P Q:Prop, my_or P Q -> my_or Q P. 
Proof. exact (fun P Q pORq R qr pr => pORq R pr qr) .           Qed. 

Lemma ex5_15_9 : forall A (P:A->Prop)(a:A), P a -> my_ex P. 
Proof. exact (fun A P a pa R pxr => pxr a pa). 
(*intros A P a pa R pxr. 
  unfold my_ex . 
  intros R pxr . 
  apply (pxr a). 
  assumption .  *)  
Qed. 

Lemma ex5_15_10 : forall A (P:A->Prop), my_not(my_ex P) -> forall a:A, my_not(P a) . 
Proof. exact (fun A P nExP a pa => nExP (fun R pxr => pxr a pa)). 
(*intros A P nExP a pa . 
  apply nExP. 
  unfold my_ex . 
  intros R pxr . 
  exact (pxr a pa ). *) 
Qed. 





(* 5.5.4.1 Impredicative le <= *)  

Open Scope nat. 

Definition my_le (n p:nat) := 
  forall P: nat->Prop, P n -> (forall q:nat, P q -> P (S q)) -> P p. 

(* Ex 5.16 *)

Lemma my_le_n : forall n: nat, my_le n n . 
Proof. intros n P pn sucP. exact pn . Qed. 

Lemma my_le_S : forall n p: nat, my_le n p -> my_le n (S p) . 
Proof. intros n p le_n_p P pn sucP. exact (sucP p (le_n_p P pn sucP)). Qed. 

Lemma my_le_le : forall n p: nat, my_le n p -> le n p . 
Proof. intros n p my_le_n_p. apply (my_le_n_p (le n)); now constructor. Qed. 


