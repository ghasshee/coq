Set Implicit Arguments. 

Section SEQUENCES. 
  Variable A : Type. 
  
  Definition Rel := A -> A -> Prop. 


  (* zero or more transitions *) 
  Inductive star (R: Rel) : Rel :=
    | star_refl : forall a, star R a a 
    | star_step : forall a b c, R a b -> star R b c -> star R a c. 

  Hint Resolve star_refl star_step : seq . 

  Lemma star_one : forall (R:Rel) a b, R a b -> star R a b. 
  Proof.  eauto with seq. Qed.  


  Hint Resolve star_one : seq. 

  Lemma star_trans : forall (R:Rel) a b, star R a b -> 
                      forall c, star R b c -> star R a c. 
  Proof.  induction 1; eauto with seq. Qed. 


  (* one or several transitions *) 
  Inductive plus (R: Rel) : Rel := 
    | plus_left : forall a b c, R a b -> star R b c -> plus R a c. 

  Hint Resolve star_trans plus_left : seq. 

  Lemma plus_one : forall (R:Rel) a b, R a b -> plus R a b. 
  Proof.  eauto with seq.  Qed.  

  Lemma plus_star : forall (R:Rel) a b, plus R a b -> star R a b. 
  Proof. intros; inversion H; eauto with seq. Qed. 

  Lemma plus_star_trans : forall (R:Rel) a b c, plus R a b -> star R b c -> plus R a c. 
  Proof. induction 1; eauto with seq. Qed.     

  Lemma star_plus_trans : forall (R:Rel) a b c, star R a b -> plus R b c -> plus R a c. 
  Proof. inversion 2; inversion H; subst; eauto with seq. Qed.   

  Lemma plus_trans : forall (R:Rel) a b c, plus R a b -> plus R b c -> plus R a c. 
  Proof. intros. apply plus_star_trans with b; auto. now apply plus_star. Qed. 

  Lemma plus_right : forall (R:Rel) a b c, star R a b -> R b c -> plus R a c.
  Proof. induction 1; eauto with seq. Qed.    

  Hint Resolve plus_one plus_star plus_star_trans plus_trans plus_right : seq. 



  (* Absense of transitions *) 
  Definition irred (R : Rel) a : Prop := forall b, ~(R a b). 


  CoInductive infseq (R:Rel) : A -> Prop :=
    | infseq_step : forall a b, 
        R a b -> infseq R b -> infseq R a . 

  Lemma infseq_coinduction_principle : 
    forall (R:Rel) (X: A->Prop), 
    (* if forall a, there is a next step, *) 
    (forall a, X a -> exists b, R a b /\ X b) -> 
    (* it's infinite sequence *) 
    forall a, X a -> infseq R a. 
  Proof. 
    intros R X P. cofix H. intros. 
    destruct (P a H0) as [b [U V]]. apply infseq_step with b; auto.    
  Qed. 
 
  Lemma infseq_coinduction_principle_2 :
    forall (R:Rel) (X: A->Prop),
    (forall a, X a -> exists b, plus R a b /\ X b) -> 
    forall a, X a -> infseq R a. 
  Proof. 
    intros.      
    apply infseq_coinduction_principle with 
      (X := fun a => exists b, star R a b /\ X b). 
    - intros. destruct H1 as [b [STAR Xb]].  
      inversion STAR; subst.  
      + destruct (H b Xb) as [c [PLUS Xc]]. inversion PLUS; subst.  
        exists b0. split; auto. 
        exists c. auto. 
      + exists b0. split; auto.  
        exists b; auto. 
    - destruct (H a H0) as [b [PLUS Xb]].    
      exists b. split; auto with seq. 
  Qed. 



  (* example of infseq_coinduction_principle *)

  Lemma infseq_alternate_characterization : 
    forall (R : Rel) a, (forall b, star R a b -> exists c, R b c) ->
    infseq R a. 
  Proof. 
    intros R. apply infseq_coinduction_principle.  
    intros. destruct (H a) as [b Hb]. 
    - constructor. 
    - exists b.  
      split.
      + assumption. Guarded. 
      + intros. apply H.      
        econstructor.   
        * apply Hb.  
        * assumption.  
    Guarded. 
  Qed.




  Require Import Classical. 

  Lemma infseq_or_finseq: 
    forall (R : Rel) a, infseq R a \/ exists b, star R a b /\ irred R b. 
  Proof. 
    intros R a.  
    Check classic. 
    destruct (classic (forall b, star R a b -> exists c, R b c)). 
    - left. now apply infseq_alternate_characterization.    
    - right.
      Check not_all_ex_not. 
      apply not_all_ex_not in H as [b P]. 
      Check imply_to_and. 
      apply imply_to_and in P as [STAR not_next]. 
      exists b. split. 
      + auto. 
      + unfold irred. 
        intros. red. intros.    
        apply not_next. 
        now exists b0. 
  Qed. 



  Section DETERMINISM. 
    Variable R : A -> A -> Prop. 
    Hypothesis R_determ : forall a b c, R a b -> R a c -> b = c. 


    (* uniqueness of transition sequences *)
    Lemma star_star_inv : 
      forall a b, star R a b -> forall c, star R a c -> star R b c \/ star R c b.
    Proof. 
      intros a b H. 
      induction H; intros.
      - now left.   
      - inversion H1; subst.   
        + right. econstructor; eauto.   
        + assert (b=b0).  
          * apply R_determ with a; auto. 
          * apply IHstar; subst; auto.      
    Qed. 


    Lemma finseq_unique : 
      forall a b b', 
      star R a b  -> irred R b  -> 
      star R a b' -> irred R b' ->
      b = b'. 
    Proof. 
      intros. 
      destruct (star_star_inv H H1). 
      - inversion H3; subst. auto. elim (H0 _ H4).      
      - inversion H3; subst. auto. elim (H2 _ H4). 
    Qed. 


    Lemma infseq_star_inv : 
      forall a b, star R a b -> infseq R a -> infseq R b. 
    Proof. 
      intros a b H. 
      induction H; auto. 
      intros. inversion H1; subst.       
      assert (b = b0). 
      + eapply R_determ; eauto.    
      + apply IHstar. now subst.  
    Qed. 

    Lemma infseq_finseq_excl : 
      forall a b,  star R a b -> irred R b -> infseq R a -> False. 
    Proof. 
      intros. 
      unfold irred in H0.   
      assert (infseq R b). 
      - eapply infseq_star_inv; eauto. 
      - inversion H2; subst. now apply (H0 b0).    
    Qed. 


    End DETERMINISM. 

  End SEQUENCES. 


  Hint Resolve 
    star_refl star_step star_one star_trans plus_left plus_one
    plus_star plus_star_trans star_plus_trans plus_right : sequences. 


    
