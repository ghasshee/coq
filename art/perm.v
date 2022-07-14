
(* ex. 8.4 *) 
Require Import Arith. 
Require Import Relations. 
Require Import List. 
Import ListNotations. 
Print equivalence. 


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

Section perm. 
  Variable A : Type. 
  Inductive transpose : list A -> list A -> Prop := 
    | transpose_hd : forall a b l , transpose (a::b::l) (b::a::l)
    | transpose_tl : forall a l l', transpose l l' -> transpose (a::l) (a::l').  

  Inductive perm : list A -> list A -> Prop := 
    | perm_refl  : forall l, perm l l
    | perm_tr    : forall l l' l'', perm l l' -> transpose l' l'' -> perm l l''. 

  Lemma transpose_sym : forall l l', transpose l l' -> transpose l' l. 
  Proof. induction 1; now constructor. Qed.  

  Hint Resolve transpose_hd transpose_tl perm_refl perm_tr transpose_sym : perm.  

  Lemma perm_trans' : forall l' l'', perm l' l'' -> forall l, transpose l l' -> perm l l''. 
  Proof. induction 1; eauto with perm. Qed.    
        
  Hint Resolve perm_trans' : perm. 

  Lemma perm_sym : forall l l', perm l l' -> perm l' l. 
  Proof. induction 1; eauto with perm. Qed. 

  Lemma perm_trans : forall l l' l'', perm l l' -> perm l' l'' -> perm l l''. 
  Proof. induction 1; eauto with perm. Qed.  

  Hint Resolve perm_sym perm_trans : perm. 

  Theorem perm_equiv : equivalence _ perm. 
  Proof. split; red; eauto with perm. Qed.  

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

Theorem perm_occ_eq : forall l l' n, perm nat l l' -> occ l n = occ l' n. 
Proof. 
  (* Do this proof on paper first !! *)
Admitted. 

