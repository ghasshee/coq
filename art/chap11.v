(* Chapter 11 * A Case Study *) 





(* 11.1 Binary Search Tree *) 


(* 11.1.1 The Data Structure *) 

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

(* Values tccuring in a Tree *) 

Inductive occ (n:Z) : Z_btree -> Prop := 
    | occ_root  : forall t1 t2,   occ n (Z_bnode n t1 t2)
    | occ_l     : forall p t1 t2, occ n t1 -> occ n (Z_bnode p t1 t2)
    | occ_r     : forall p t1 t2, occ n t2 -> occ n (Z_bnode p t1 t2) . 


(* 11.1.2 A Naive Approach to Deciding Occurrence *) 
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

(* 11.1.3 Describing Search Trees *) 

Inductive min (n:Z) (t:Z_btree) : Prop := 
    | min_intro : (forall p, occ p t -> n < p) -> min n t.

Inductive maj (n:Z) (t:Z_btree) : Prop :=
    | maj_intro : (forall p, occ p t -> p < n) -> maj n t. 

Inductive search_tree : Z_btree -> Prop :=
    | leaf_search_tree : search_tree Z_leaf 
    | bnode_search_tree : forall n t1 t2, 
            search_tree t1 -> search_tree t2 -> maj n t1 -> min n t2 -> 
            search_tree (Z_bnode n t1 t2) . 




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






(* 11.2 Specifying Programs *) 


(* 11.2.1 Finding an Occurence *) 
Definition occ_dec_spec p t : Set := 
    search_tree t -> {occ p t} + { ~ occ p t} . 


(* 11.2.2 Inserting a Number *) 

(* A Predicate for Insertion *) 
Inductive INSERT n t t' : Prop := 
    insert_intro : 
      (forall p, occ p t  -> occ p t'      ) -> occ n t' -> 
      (forall p, occ p t' -> occ p t \/ n=p) -> search_tree t' -> INSERT n t t'. 

(* 11.2.2.1 The Specification for Insertion *) 
Definition insert_spec n t : Set := search_tree t -> { t' : Z_btree | INSERT n t t' } . 



(* 11.2.3 Removing a Number *) 
Inductive RM n t t' : Prop := 
    rm_intro : 
        ~ occ n t' -> 
        (forall p, occ p t' -> occ p t) -> 
        (forall p, occ p t -> occ p t' \/ n = p) -> 
        search_tree t' -> RM n t t'. 

Definition rm_spec n t : Set := search_tree t -> { t' : Z_btree | RM n t t' } . 





(* ex.11.2 *) 
Definition bin_search_tree  := sig search_tree. 

Definition bin_search_occ   n (t:bin_search_tree) := 
    match t with 
    | exist _ t _ => occ n t end. 

Definition bin_search_occ_dec n t := 
      {bin_search_occ n t} + { ~ bin_search_occ n t }. 

Inductive bin_search_INSERT n t t' : Prop :=
    bs_insert_intro : 
      (forall p, bin_search_occ p t -> bin_search_occ p t')  -> 
      bin_search_occ n t' -> 
      (forall p, bin_search_occ p t'-> bin_search_occ p t\/n=p) -> 
      bin_search_INSERT n t t'. 

Definition bin_search_insert_spec n t := { t' | bin_search_INSERT n t t' }. 

Inductive bin_search_RM n t t': Prop := 
    bs_rm_intro :
      ~ bin_search_occ n t' -> 
      (forall p, bin_search_occ p t' -> bin_search_occ p t) -> 
      (forall p, bin_search_occ p t  -> bin_search_occ p t \/ n=p) -> 
      bin_search_RM n t t'. 

Definition bin_search_rm_spec n t := { t' | bin_search_RM n t t' }. 
(* end 11.2 *) 








(* 11.3 Auxiliary Lemmas *) 

Lemma not_left : 
  forall n l r , search_tree (Z_bnode n l r) -> forall p, p>=n -> ~ occ p l. 
Proof. 
  red. intros. inversion H.  
  subst. inversion H7.  
  now set (H2 p H1). 
Qed. 
Reset not_left. 

(* 11.4 Realizing Specifications *) 

(* 11.4.1 Realizing the Occurence Test *) 

Definition occ_dec := forall p t, occ_dec_spec p t.
Reset occ_dec. 

Lemma min_leaf : forall z, min z Z_leaf. 
Proof. intros. constructor. inversion 1. Qed.    

Lemma maj_leaf : forall z, maj z Z_leaf. 
Proof. intros. constructor. inversion 1. Qed.    

Lemma maj_not_occ : forall z t, maj z t -> ~ occ z t. 
Proof. red. intros. inversion H. set (H1 z H0). lia. Qed.  

Lemma min_not_occ : forall z t, min z t -> ~ occ z t. 
Proof. red. intros. inversion H. set (H1 z H0). lia. Qed.  

Hint Resolve 
  insert_intro
  occ_root occ_l occ_r 
  min_leaf maj_leaf maj_not_occ min_not_occ : searchtrees. 

Section search_tree_basic_properties. 
  Variable n:Z.
  Variable l r : Z_btree. 
  Hypothesis se : search_tree (Z_bnode n l r). 

  Lemma search_tree_l : search_tree l. 
  Proof. inversion se. assumption. Qed.   
  Lemma search_tree_r : search_tree r. 
  Proof. inversion se. assumption. Qed.   
  Lemma maj_l : maj n l. 
  Proof. inversion se. assumption. Qed. 
  Lemma min_r : min n r. 
  Proof. inversion se. assumption. Qed. 
  Lemma not_right : forall p, p<=n -> ~ occ p r. 
  Proof. inversion se. inversion H5. red. intros. set (H6 p H8). lia. Qed.      
  Lemma not_left  : forall p, p>=n -> ~ occ p l. 
  Proof. inversion se. inversion H4. red. intros. set (H6 p H8). lia. Qed.   
  Lemma go_left : forall p, occ p(Z_bnode n l r) -> p < n -> occ p l. 
  Proof. intros. inversion se. inversion H; subst; 
         [ | | inversion H7; set (H1 p H9) ]; auto; lia. Qed. 
  Lemma go_right : forall p, occ p(Z_bnode n l r) -> p > n -> occ p r.   
  Proof. intros. inversion se. inversion H; subst; 
         [ | inversion H6; set(H1 p H9) | ]; auto; lia.  Qed. 
End search_tree_basic_properties. 
         
Hint Resolve go_left go_right not_left not_right
    search_tree_l search_tree_r maj_l min_r : searchtrees. 


Check Z_le_gt_dec. 
Check Z_le_lt_eq_dec. 

Definition occ_dec : forall p t, occ_dec_spec p t. 
Proof. 
  refine 
  (fix occ_dec p t {struct t} := 
    match t with 
    | Z_leaf        => fun h => right _ _ 
    | Z_bnode n l r => fun h => match Z_le_gt_dec p n with 
                                | left  h1 => match Z_le_lt_eq_dec p n h1 with 
                                              | left h'1 => match occ_dec p l _ with 
                                                            | left  h''1 => left  _ _ 
                                                            | right h''2 => right _ _ end
                                              | right h'2=> left _ _  end 
                                | right h2 => match occ_dec p r _ with 
                                              | left  h''1  => left  _ _ 
                                              | right h''2  => right _ _  end end end); 
                                              subst; eauto with searchtrees. 
Defined. 
  
Extraction occ_dec. 




(* 11.4.2 Insertion *) 

Lemma insert_leaf : forall n, INSERT n Z_leaf (Z_bnode n Z_leaf Z_leaf). 
Proof. intros. constructor.    
  - inversion 1. 
  - constructor.  
  - inversion 1; tauto.  
  - repeat constructor; inversion 1. 
Qed. 

Lemma insert_l : forall n p l l' r, n < p -> search_tree (Z_bnode p l r) -> 
    INSERT n l l' -> 
    INSERT n (Z_bnode p l r) (Z_bnode p l' r). 
Proof. 
  inversion 3; constructor; intros.  
  - inversion H6; subst; eauto with searchtrees. 
  -                      eauto with searchtrees.  
  - inversion H6; subst; eauto with searchtrees. 
    + destruct (H4 p0);  eauto with searchtrees. 
  - inversion H0; subst; constructor; eauto with searchtrees. 
    + constructor; inversion H11; intros; destruct(H4 p0 H7); 
      subst; eauto with searchtrees.
Qed. 

Lemma insert_r : forall n p l r r', n > p -> search_tree (Z_bnode p l r) -> 
    INSERT n r r' -> 
    INSERT n (Z_bnode p l r) (Z_bnode p l r') . 
Proof. 
  inversion 3; constructor; intros. 
  - inversion H6; subst; eauto with searchtrees. 
  - eauto with searchtrees. 
  - inversion H6; subst; eauto with searchtrees. 
    + destruct (H4 p0); eauto with searchtrees. 
  - inversion H0; subst; constructor; eauto with searchtrees. 
    + constructor; inversion H12; intros; destruct(H4 p0 H7);
      subst; eauto with searchtrees; lia.  
Qed. 

Lemma insert_eq : forall n l r, search_tree (Z_bnode n l r) -> 
      INSERT n (Z_bnode n l r) (Z_bnode n l r). 
Proof. constructor; eauto with searchtrees. Qed.  

Hint Resolve insert_leaf insert_l insert_r insert_eq : searchtrees. 



(* Should There be a Test function for search_tree ? *)

Definition insert : forall n t, insert_spec n t. 
Proof. 
  refine 
  (fix insert n t :=
    match t with 
    | Z_leaf        => fun s => exist _ (Z_bnode n Z_leaf Z_leaf) _ 
    | Z_bnode p l r => fun s => 
        match Z_le_gt_dec n p with 
        | left  Hle => match Z_le_lt_eq_dec n p Hle with 
                       | left  Heq => match insert n l _ with 
                                      | exist _ l' _ => exist _ (Z_bnode p l' r) _ end 
                       | right Hlt => exist _ (Z_bnode n l r) _ end 
        | right Hgt => match insert n r _ with
                       | exist _ r' _ => exist _ (Z_bnode p l r') _ end end end ); 
                       subst; eauto with searchtrees.  
Defined.  




Require Import List. 
Import ListNotations. 

Definition list2tree_spec l := 
  { t | search_tree t /\ (forall p, In p l <-> occ p t)}. 


Definition list2tree_aux_spec l t := 
  search_tree t -> 
  { t' | search_tree t' /\ (forall p, In p l \/ occ p t <-> occ p t') }.  

Definition list2tree_aux : forall l t, list2tree_aux_spec l t. 
Proof.   
  refine
    (fix list2tree_aux l t := 
         match l with 
         | []     => fun s => exist _ t _
         | p::l'  => fun s => 
             match insert p t s with
             | exist _ t' _ => match list2tree_aux l' t' _ with
                               | exist _ t'' _ => exist _ t'' _ end end end).
  - split; auto.
    + split; auto.
      * intuition. inversion H0. 
  - case i; auto.
  - case a; auto.
    intros; split; auto.
    intros; case a; intros; split; auto.
    + destruct 1 as [H3 | H3].
      * { destruct H3; intros; subst. 
        - destruct (H2 p0). apply H3. right. case i; auto.          
        - destruct (H2 p0). auto. }   
      * { destruct (H2 p0). apply H4. right. case i; auto. }  
    + intros. 
      destruct a       as [H4 H5]. 
      destruct (H5 p0) as [H6 H7]. 
      destruct (H7 H3).
      * left. cbn. right. assumption.     
      * destruct i.    
        destruct (H11 p0 H8); auto.  
        cbn. left. left. assumption.     
Defined. 

Definition list2tree : forall l, list2tree_spec l. 
Proof. 
  refine ( fun l => 
    match list2tree_aux l Z_leaf _ with 
    | exist _ t _ => exist _ t _  end ). 
  - constructor.  
  - destruct a as [H1 H2].  
    split; auto. 
    + intros p. destruct (H2 p); split. 
      * intros. apply H. left. assumption.    
      * intros. 
        { destruct (H0 H3). 
        - auto. 
        - inversion H4. } 
Defined. 


(* Extracted Programs *) 

Extraction insert .
Extraction list2tree_aux . 
Extraction list2tree . 






(* 11.4.3 Removing Elements *) 

Inductive RMAX t t' n : Prop :=
  rmax_intro : occ n t -> 
               (forall p, occ p t -> p<=n) -> 
               (forall q, occ q t' -> occ q t) -> 
               (forall q, occ q t -> occ q t' \/ q = n) -> 
               ~ occ n t' -> search_tree t' -> RMAX t t' n. 

Definition rmax_sig t q := {t' | RMAX t t' q}. 
(*
Definition is_bnode t := match t with 
                         | Z_leaf => False
   | _      => True end . *)
Inductive is_bnode : Z_btree -> Prop := 
  is_bnode_intro : forall n l r, is_bnode (Z_bnode n l r). 

Definition rmax_spec t  := search_tree t -> is_bnode t -> {q & rmax_sig t q} . 



(* 11.5 Possible Improvements *) 

(* 11.6 Another Example *)

(* ==> see Monin's book[66] chapter 12 *) 
(*     "Undeerstanding Formal Methods" 2002 *) 

