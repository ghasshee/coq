(* Chapter 03 *) 

(* 3. Propositions and Proofs *) 


(* 3.1 Minimal Propositional Logic *) 
Section Minimal_propositional_Logic.

  Variables P Q R S T : Prop.

  Theorem imp_trans : (P->Q) -> (Q->R) -> (P->R) . 
  Proof. intros H H' p. apply H', H. assumption. Qed. 
  
  Theorem imp_dist : (P->Q->R) -> (P->Q) -> (P->R). 
  Proof. 
    intros Hpqr Hpq p. apply Hpqr. 
    2: apply Hpq; assumption.  (* 2:tactic := apply tactic in Goal 2 *) 
    1: assumption. 
  Qed.  


  Definition f : (nat->bool) -> (nat->bool) -> nat -> bool. 
    intros f1 f2. assumption. Defined . 
  Print f . 
  
  Eval compute in f ( fun n => true ) ( fun n => false) 45 .
  Opaque f .
  Eval compute in f ( fun n => true ) ( fun n => false) 45 .  (* This does not compute *) 
  Compute         f ( fun n => true ) ( fun n => false) 45 .  (* This DOES compute *) 
  
  (* ex. 3.2 *)
  Lemma id_P  : P -> P .                                    Proof. tauto. Qed.  
  Lemma id_PP : (P->P) -> (P->P).                           Proof. tauto. Qed.  
  Lemma imp_perm : (P->Q->R) -> (Q->P->R).                  Proof. tauto. Qed. 
  Lemma ignore_Q : (P->R) -> P -> Q -> R .                  Proof. tauto. Qed. 
  Lemma delta_imp : (P->P->Q) -> P -> Q.                    Proof. tauto. Qed.  
  Lemma delta_impR : (P->Q) -> (P->P->Q).                   Proof. tauto. Qed. 
  Lemma diamond : (P->Q) -> (P->R) -> (Q->R->T) -> P -> T.  Proof. tauto. Qed. 
  Lemma weak_pierce : ((((P->Q)->P)->P)->Q)->Q .            Proof. tauto. Qed.  
    
  
  (* 3.3 Structure of an Interactive Proof *) 
  Section proof_of_triple_impl. 
    Hypothesis H : ((P -> Q) -> Q) -> Q.
    Hypothesis p : P. 
  
    Lemma Rem : (P -> Q) -> Q.  Proof fun H': P->Q => H' p.    
    Lemma foo:Q. Abort. 
    Theorem triple_impl: Q .    Proof H Rem. 
    Lemma foo:Q. Abort. 
  End proof_of_triple_impl. 
  Print triple_impl. 
  Print Rem.              (* Be careful to the type of Rem *)  
  
  
  Theorem then_example : P -> Q -> (P -> Q -> R) -> R. 
  Proof. 
      intros p q H; apply H ; assumption .  (* assumption is called twice *) 
  Qed. 
  
  
  Theorem triple_impl_one_shot : (((P->Q)->Q)->Q)->P->Q . 
  Proof. 
      intros H p ; apply H; intro H0; apply H0; assumption . 
  Qed. 
  
  
  Theorem compose_example : (P->Q->R) -> (P->Q) -> (P->R) . 
  Proof. 
      intros H H' p . 
      (* apply H ; [assumption | apply H' ; assumption ] . *) 
      (* apply H; [ | apply H' ] ; assumption . *)
      apply H; [ idtac | apply H' ] ; assumption . 
  Qed. 
  
  
  Theorem orelse_example : (P -> Q) -> R -> (( P->Q) -> R -> (T -> Q) -> T) -> T. 
  Proof. 
      intros H r H0 . 
      apply H0; ( assumption || intros H1) . 
  Abort.
  
  
  Lemma L3 : (P->Q) -> (P->R) -> (P->Q->R->T) -> P -> T .
  Proof. 
      intros H H0 H1 p. 
      apply H1; [idtac | apply H | apply H0 ] ; assumption . 
  Qed. 
  
  

  (* 3.6.1.5   "fail" tactic *) 
  
  Theorem then_fail_example1 : (P->Q) -> (P->Q) . 
  Proof. 
      intros f; apply f; fail.
  Qed.
  
  Theorem then_fail_example2 : ( ( P->P ) -> ( Q->Q ) -> R ) -> R .
  Proof. 
    (* intro X; apply X; fail. *)
  Abort. 
   
  
  
  
  (* 3.6.1.6    "try" tactic *) 
  
  Theorem try_example : (P->Q->R->T) -> (P->Q) -> (P->R->T) . 
  Proof. 
      intros H H' p r. 
      apply H; try (apply H'); assumption . 
  Qed. 


  (* 3.7 On Completeness for Propositional Logic *) 

  (* 3.7.1 A Complete Set of Tactics *) 

  (* "apply" *)
  (* "intro" *)
  (* "assumption" *)

  (* 3.7.2 Unprovable Propositions in Minimal Prop Logic *) 
  Goal ~ (forall P:Prop, exists p:P, True). 
  Proof.
  Abort. 
  
  (* 3.8  Some More Tactics *) 

  (* 3.8.1.1 "cut" *)
  (* 3.8.1.2 "assert" *) 
  (* 3.8.2.1 "auto" *)
  (* 3.8.2.2 "trivial" *) 
  Section section_cut_examples. 
    Hypotheses  (H  : P->Q)
                (H0 : Q->R)
                (H1 : (P->R)->T->Q)
                (H2 : (P->R)->T) . 
  
    Theorem cut_example : Q . 
    Proof. 
      cut (P->R). intro H3. 
      apply H1; try (apply H2); assumption .
      intro p; apply H0; apply H; assumption .  
    Qed. 
    Print cut_example.
  End section_cut_examples. 

  Theorem triple_impl2 : (((P->Q)->Q)->Q)->P -> Q .
  Proof. auto 3. Qed. 

  (* ex. 3.6 *) 
  Theorem auto_ex : (((((P->Q)->Q)->Q)->Q)->Q)->P->Q  .
  Proof.  auto 3. auto 4.  Qed.
  

End Minimal_propositional_Logic . 


(* 3.9 A New Kind of Abstraction *) 


Goal (((True /\ True) /\ True) /\ True) /\ True. 
Proof. 
  split.   
  - split.  
    + split. 
      * { split . 
          - exact I.  
          - exact I. }
      * trivial . 
    + trivial. 
  - assert True. 
    + reflexivity.     
    + assumption . 
Qed. 


Goal True \/ True . 
Proof . 
    left . 
    trivial .
Qed . 
     
Require Import Bool .
Lemma abdb_comm : forall b1 b2 , b1 && b2 = b2 && b1 .
Proof . 
    intros b1 b2 . 
    destruct b1 .
    - destruct b2 . 
        + simpl. reflexivity .  
        + simpl. reflexivity .   (* here - is closed auto matically *) 
    - destruct b2 . 
        + simpl. reflexivity .  
        + simpl. reflexivity . 
Qed. 




(* 3.8 some more tactics *)

Compute 1 < 2.  
Print Lt . 
Print le_S.  
Print le . 
Print gt. 

Theorem _100_gt_10 : 100 > 10 . 
Proof.  
    unfold gt. 
    unfold lt. 
    apply le_S . 
    auto 92. 
Qed. 




