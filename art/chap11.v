
Require Import ZArith Arith. 
Open Scope Z_scope. 

Inductive Z_btree : Set := 
    | Z_leaf    : Z_btree
    | Z_bnode   : Z -> Z_btree -> Z_btree -> Z_btree . 


Definition Figure_11_1 := 
  Z_bnode 10 
    (Z_bnode 8 
      (Z_bnode 7 Z_leaf Z_leaf)
      (Z_bnode 9 Z_leaf Z_leaf))
    (Z_bnode 15
      (Z_bnode 13 Z_leaf Z_leaf)
      (Z_bnode 19 
        Z_leaf
        (Z_bnode 27 Z_leaf Z_leaf))) . 

Inductive occ (n:Z) : Z_btree -> Prop := 
    | occ_root  : forall t1 t2,   occ n (Z_bnode n t1 t2)
    | occ_l     : forall p t1 t2, occ n t1 -> occ n (Z_bnode p t1 t2)
    | occ_r     : forall p t1 t2, occ n t2 -> occ n (Z_bnode p t1 t2) . 


Require Import Lia. 

Definition naive_occ_dec : forall n t, {occ n t} + {~ occ n t} . 
    induction t. 
      - (* t == Z_leaf *) right; red; intros; inversion H.   
      - (* t == Z_bnode z t1 t2 *) case (Z.eq_dec n z). 
          + (* n == z *) induction 1; left. constructor.  
          + (* n <> z *) case IHt1. 
              * (* t1 == Z_bnode n _ _ *) intro occ1. left. now constructor.  
              * (* t1 <> Z_bnode n _ _ *) intros nocc1 neq. { case IHt2. 
                -  (* t2 == Z_bnode n _ _ *) intro occ2. left. now constructor.   
                -  (* No n occurs in next level *) intro nocc2. right. inversion 1; auto. }
Defined. 
     
Require Import Extraction. 

Extraction naive_occ_dec. 


Inductive min (n:Z) (t:Z_btree) : Prop := 
    | min_intro : (forall p, occ p t -> n < p) -> min n t.

Inductive maj (n:Z) (t:Z_btree) : Prop :=
    | maj_intro : (forall p, occ p t -> p < n) -> maj n t. 

Inductive search_tree : Z_btree -> Prop :=
    | leaf_search_tree : search_tree Z_leaf 
    | bnode_search_tree : forall n t1 t2, 
            search_tree t1 -> search_tree t2 -> maj n t1 -> min n t2 -> search_tree (Z_bnode n t1 t2) . 




(* ex 11.1 *) 
Inductive min' n : Z_btree -> Prop := 
    | min_intro_leaf : min' n Z_leaf 
    | min_intro_node : forall z t1 t2, min' n t1 -> n < z ->  min' n (Z_bnode z t1 t2) .  

Inductive maj' n : Z_btree -> Prop := 
    | max_intro_leaf : maj' n Z_leaf 
    | max_intro_node : forall z t1 t2, maj' n t2 -> z < n -> maj' n (Z_bnode z t1 t2). 

Inductive search_tree' : Z_btree -> Prop := 
    | leaf_search_tree' : search_tree' Z_leaf 
    | bnode_search_tree' : forall n t1 t2, 
            search_tree' t1 -> search_tree t2 -> maj' n t1 -> min' n t2 -> 
            search_tree' (Z_bnode n t1 t2) . 

Lemma min_eq_min' : forall n t, search_tree t -> min n t <-> min' n t. 
Proof. 
    intros t n st. 
    induction st.   
    - split; constructor. intros p occ. 
      + inversion occ.   
    - split. 
      + inversion 1. constructor.   
        * rewrite <- IHst1. 
          constructor. intros.   
          apply H2. now constructor.  
        * apply H2. now constructor.    
      + inversion 1. constructor. intros p occp. 
        inversion occp.  
        * now idtac. 
        * rewrite <- IHst1 in H4. destruct H4. now apply H4.   
        * subst. apply Z.lt_trans with n; trivial. 
          destruct H0. now apply H0.    
Qed. 

Lemma maj_eq_maj' : forall n t, search_tree t -> maj n t <-> maj' n t.  
Proof. 
    intros n t Hst; induction Hst.
    - split; constructor. Print occ. inversion 1. 
    - split.   
      + Print maj'. inversion 1. constructor. 
        * rewrite <- IHHst2. constructor. intros.     
          apply H2. now constructor.  
        * apply H2. now constructor.  
      + Print maj. inversion 1. subst. constructor.
        intros p occ. inversion occ; subst.  
        * (* occ_root*) assumption. 
        * (* occ_l   *) apply Z.lt_trans with n0; trivial. destruct H. now apply H.  
        * (* occ_r   *) rewrite <- IHHst2 in H4. destruct H4. now apply H2.   
Qed. 

Theorem search_tree'_correct : forall t, search_tree t <-> search_tree' t.  
Proof. 
    split. 
    - intros; induction H; constructor; auto.       
        * now rewrite <- maj_eq_maj'. 
        * now rewrite <- min_eq_min'. 
    - intros. induction H; constructor; auto. 
        * now rewrite maj_eq_maj'. 
        * now rewrite min_eq_min'. 
Qed. 
(* end ex 11.1 *) 

Definition occ_dec_spec p t : Set := 
    search_tree t -> {occ p t} + { ~ occ p t} . 

Inductive INSERT n t t' : Prop := 
    insert_intro : (forall p, occ p t  -> occ p t'      ) -> occ n t' -> 
                   (forall p, occ p t' -> occ p t \/ n=p) -> search_tree t' -> INSERT n t t'. 

Definition insert_spec n t : Set := search_tree t -> { t' : Z_btree | INSERT n t t' } . 

Inductive RM n t t' : Prop := 
    rm_intro : 
        ~ occ n t' -> 
        (forall p, occ p t' -> occ p t) -> 
        (forall p, occ p t -> occ p t' \/ n = p) -> 
        search_tree t' -> RM n t t'. 

Definition rm_spec n t : Set := search_tree t -> { t' : Z_btree | RM n t t' } . 






