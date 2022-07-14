From mathcomp Require Import ssreflect. 
Require Import Reals.
Require Import Fourier. 
Require Import Coq.Sets.Ensembles. 
Require Export QArith_base. 

Local Open Scope R_scope. 
Require Export Rdefinitions. 
Require Import Classical. 
Require Import Coq.Sets.Finite_sets.
Require Import Coq.Sets.Finite_sets_facts.
Require Import Coq.Sets.Image. 
Require Import Coq.Logic.Description. 
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevanceFacts.
Require Import Coq.Logic.ClassicalDescription. 
Require Import Coq.Arith.Even.
Require Import Coq.Arith.Div2.

Hint Resolve Rplus_0_l Rplus_0_r Rplus_opp_r Rplus_opp_l Rplus_comm Rplus_assoc : R.

Lemma sig_map : forall {T} (P : T -> Prop) ( x y : { x : T | P x } ), 
  proj1_sig x = proj1_sig y -> x = y. 
Proof. 
  intros A P x y. 
  case x. 
  intros xv Pxv.  
  case y. 
  intros yv Pyv.
  simpl. 
  intros. subst. 
  Print proof_irrelevance. 
  now rewrite (proof_irrelevance (P yv) Pyv Pxv). 
Qed. 


Lemma ex_1_1_1_1 : forall e, (forall r, e + r = r) -> e = 0. 
Proof. intros.   
  intros. 
  set (H 0).  
  now rewrite <- (Rplus_0_r e). 
Qed.  

Lemma ex_1_1_1_2 : forall r r', r + r' = 0 -> r' = -r. Proof.  intros. fourier. Qed.  
     
Lemma ex_1_1_1_3 : forall r , - (-r) = r.    Proof. intros. fourier. Qed. 

Lemma ex_1_1_1_4 : forall r , 0 * r = 0 .    Proof. intros. fourier . Qed. 

Lemma ex_1_1_1_5 : forall r, (-1) * r = -r.  Proof. intros. fourier. Qed. 

Lemma ex_1_1_1_6 : (-1) * (-1)= 1.           Proof. fourier. Qed. 

Lemma ex_1_1_1_7_l : forall r r', r * (-r')  = - (r * r'). Proof. intros. fourier. Qed. 
Lemma ex_1_1_1_7_r : forall r r', (- r) * r' = - (r * r'). Proof. intros. fourier. Qed. 

Lemma ex_1_1_1_8 : forall r r', (-r) * (-r') = r * r' . Proof. intros. fourier. Qed. 

Lemma ex_1_1_1_9 : forall r r', r * r' = 0 -> { r = 0 } + { r' = 0 }. 
Proof. 
  intros; elim (total_order_T r 0); intros.
  - destruct a.  
    + right. 
      cut (r <> 0); intros; try fourier. 
      * rewrite <- (Rmult_1_l r'),<- (Rinv_l _ H0), Rmult_assoc, H.
        fourier. 
    + now left.  
  - right. 
    cut (r <> 0); intros; try fourier. 
    + rewrite <- (Rmult_1_l r'),<- (Rinv_l _ H0), Rmult_assoc, H.
      fourier. 
Qed. 

Lemma ex_1_1_1_sub : forall r r', r * r' = 1 -> r' = (/ r). 
Proof. 
  intros. 
  rewrite <- (Rmult_1_l (/r)), <- H, Rmult_comm, <- Rmult_assoc. 
  cut (r <> 0); intros.   
  - rewrite (Rinv_l _ H0); fourier.  
  - intros n. subst. generalize H. fourier .       
Qed. 

Lemma ex_1_1_1_10 : forall r, r <> 0 -> /(-r) = - /r. 
Proof. 
  intros. symmetry. 
  apply (ex_1_1_1_sub (-r) (-/r)). 
  rewrite ex_1_1_1_8; rewrite Rmult_comm; rewrite Rinv_l; fourier. 
Qed. 

Lemma ex_1_1_1_11 : forall r r', r <> 0 /\ r' <> 0 -> /(r*r') = /r' * /r. 
Proof. 
  intros 
  destruct H.     
  rewrite <-  (ex_1_1_1_sub (r*r') (/r' */r)). 
  - trivial. 
  - rewrite <- Rmult_assoc. rewrite (Rmult_assoc r). rewrite Rinv_r. 
    rewrite (Rmult_comm r); rewrite Rmult_assoc; rewrite Rinv_r; fourier. trivial. 
Qed. 

Lemma Formula_1_2 : forall r, r>0 \/ r=0 <-> -r<0 \/ r=0. 
Proof. 
  intros; split; intros. 
  - elim H; intros.  
    + left; rewrite <- (Rplus_0_r (-r)), <- (Rplus_opp_l r); fourier. 
    + now right. 
  - elim H; intros. 
    + left; rewrite <- (Rplus_0_r r), <- (Rplus_opp_l (-r)); fourier. 
    + now right.   
Qed.  


    


