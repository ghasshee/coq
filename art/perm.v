
(* ex. 8.4 *) 
Require Import Arith. 
Require Import Relations. 
Require Import List. 
Import ListNotations. 
Print equivalence. 

(*
Section flip. 
  Variable A : Type. 
  Inductive flip : list A -> list A -> Prop := 
    | flip_two  : forall x y,    flip [x;y] [y;x] 
    | flip_cons : forall l l' x, flip l l' -> flip (x::l)(x::l') 
    | flip_last : forall l l' x, flip l l' -> flip (l++[x])(l'++[x]) . 
  
  Inductive flip_many : list A -> list A -> Prop := 
    | flip_step  : forall l l',     flip l l' -> flip_many l l'
    | flip_refl  : forall l,        flip_many l l 
    | flip_trans : forall l l' l'', flip_many l l'-> flip_many l' l''-> flip_many l l''.  
  
  Lemma flip_sym : forall l l', flip l l' -> flip l' l .  
  Proof. induction 1; now constructor.   Qed. 
  
  Hint Resolve  flip_two  flip_cons flip_last flip_sym
                flip_step flip_refl flip_trans        : flip. 
  
  Lemma flip_many_sym : forall l l', flip_many l l' -> flip_many l' l. 
  Proof. induction 1; eauto with flip. Qed.  
  
  Hint Resolve  flip_many_sym : flip . 
  
  Theorem filp_equiv : equivalence (list A) flip_many . 
  Proof.  split; red; eauto with flip.  Qed. 

End flip. 
 *)

Section perm. 
  Variable A : Type. 
  Inductive flip : list A -> list A -> Prop := 
    | flip_hd : forall a b l , flip (a::b::l) (b::a::l)
    | flip_tl : forall a l l', flip l l' -> flip (a::l) (a::l').  

  Inductive perm : list A -> list A -> Prop := 
    | perm_refl  : forall l, perm l l
    | perm_tr    : forall l l' l'', perm l l' -> flip l' l'' -> perm l l''. 

  Lemma flip_sym : forall l l', flip l l' -> flip l' l. 
  Proof. induction 1; now constructor. Qed.  

  Hint Resolve flip_hd flip_tl perm_refl perm_tr flip_sym : perm.  

  Lemma perm_trans_r : forall l' l'', perm l' l'' -> forall l, flip l l' -> perm l l''. 
  Proof. induction 1; eauto with perm. Qed.    

  Hint Resolve perm_trans_r : perm. 

  Lemma perm_sym : forall l l', perm l l' -> perm l' l. 
  Proof. induction 1; eauto with perm. Qed. 

  Lemma perm_trans : forall l l' l'', perm l l' -> perm l' l'' -> perm l l''. 
  Proof. induction 1; eauto with perm. Qed.  

  Hint Resolve perm_sym perm_trans : perm. 

  Theorem perm_equiv : equivalence _ perm. 
  Proof. split; red; eauto with perm. Qed.  

  Theorem perm_tail : forall a l l', perm l l' -> perm (a::l) (a::l'). 
  Proof. induction 1; eauto with perm. Qed.  

  Theorem flip_head : forall a l l', flip l l' -> flip (l++[a])(l'++[a]). 
  Proof. 
    induction 1.  
    + repeat rewrite <- app_comm_cons.  
      constructor. 
    + eauto with perm.  
      repeat rewrite <- app_comm_cons. 
      constructor. assumption.  
  Qed. 

  Theorem perm_head : forall a l l', perm l l' -> perm (l++[a])(l'++[a]). 
  Proof. 
    induction 1; eauto with perm. 
    inversion H0; subst. 
    + econstructor; eauto with perm. constructor.     
    + econstructor; eauto with perm. 
      repeat rewrite <- app_comm_cons. 
      constructor. apply flip_head. assumption.   
  Qed. 

  Hint Resolve perm_tail perm_head flip_head : perm. 
    
End perm. 




Search ( { _ = _ } + { _ <> _ } ). 

(* ex 9.5 *) 
Fixpoint occ l n := 
  match l with 
  | []      => 0 
  | x::xs   => match Nat.eq_dec n x with 
               | left _   => 1 + occ xs n 
               | right _  => occ xs n end end.  



(* ex. 16.7 *) 
Lemma flip_occ_eq : forall l l', flip nat l l' -> forall n, occ l n = occ l' n. 
Proof. 
  induction 1; intro n; simpl; 
  [ case(Nat.eq_dec n a);case(Nat.eq_dec n b) | rewrite IHflip ]; reflexivity.    
Qed. 

Theorem perm_occ_eq : forall l l', perm nat l l' -> forall n, occ l n = occ l' n. 
Proof. 
  induction 1; intro n.
  - reflexivity.  
  - destruct H0; rewrite IHperm; simpl;  
    [ case(Nat.eq_dec n a);case(Nat.eq_dec n b) | rewrite<-(flip_occ_eq l0 l') ]; trivial. 
Qed. 



Fixpoint check_all_occs l l' k := 
  match k with 
  | []        => true
  | x::xs     => match Nat.eq_dec (occ l x) (occ l' x) with 
                 | left _   => check_all_occs l l' xs 
                 | right _  => false end end.  

Theorem check_all_occs_false : forall l l' k, check_all_occs l l' k = false -> 
  exists a, occ l a <> occ l' a. 
Proof.  
  simple induction k; simpl; intros. 
  - inversion H.  
  - destruct (Nat.eq_dec (occ l a)(occ l' a)); 
    [destruct (H H0) | ];[ exists x | exists a ] ; assumption. 
Qed. 

Theorem check_all_occs_not_perm : forall l l', 
  check_all_occs l l' l = false   ->  ~ perm nat l l'. 
Proof. 
  red; intros. 
  destruct (check_all_occs_false _ _ _ H).  
  now apply perm_occ_eq with (n:= x) in H0.  
Qed. 

Ltac noperm := 
  match goal with 
  | |- ~ perm nat ?l ?l'  => 
      apply (check_all_occs_not_perm l l'); 
      reflexivity 
  end. 


Theorem not_perm_eg : ~ perm nat [1;3;2] [3;1;1;4;2]. 
Proof.  noperm. Qed.  





Fixpoint nat_le_bool n m :=
  match n, m with 
  | O, _      => true
  | _, O      => false 
  | S p, S q  => nat_le_bool p q end.  

Fixpoint insert n l := 
  match l with 
  | []      => [n] 
  | m::l'   => match nat_le_bool n m with 
               | true   => n :: l
               | false  => m :: insert n l' end end. 

Fixpoint sort l := 
  match l with 
  | n :: l' => insert n (sort l')
  | []      => []                 end. 

Theorem insert_perm_aux : forall n l, perm nat (n::l) (insert n l). 
Proof. Admitted. 


Theorem insert_perm : forall l l', perm nat l l' -> forall n, perm nat (n::l) (insert n l'). 
Proof. Admitted. 

Theorem sort_perm : forall l, perm nat l (sort l). 
Proof. 
  induction l; simpl. 
  - constructor.  
  - apply insert_perm. assumption.  
Qed. 






      

