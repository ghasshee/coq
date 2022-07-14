
Section JMeq . 
    Inductive JMeq {A} (x:A) : forall {B}, B -> Prop := 
        JMeq_refl : JMeq x x . 

    Check (JMeq_refl 1) .  
    Check JMeq. 
    Reset JMeq. 

    Require Import JMeq. 
    Check JMeq_eq. 

    Inductive htree (A:Set) : nat -> Set := 
        | hleaf : A -> htree A O
        | hnode : forall n:nat, A -> htree A n -> htree A n -> htree A (S n). 

    Inductive ahtree : Set := 
        | any_height : forall n:nat, htree nat n -> ahtree . 
    Check any_height. 

    Theorem any_height_inj2 : 
        forall (n1 n2:nat) (t1:htree nat n1) (t2:htree nat n2), 
        any_height n1 t1 = any_height n2 t2 -> JMeq t1 t2 . 
    Proof. 
        intros. 
        (* 
        injection H. 
        intros. 
        dependent rewrite <- H0. 
        constructor. 
        Undo 4. 
        *) 
        change (match any_height n2 t2 with 
                | any_height n t => JMeq t1 t end ). 
        now rewrite <- H.  
    Qed. 

End JMeq. 


Check existT. 
Check projT2. 


Require Import Vector. 
Require Import List. 

Set Implicit Arguments .

Inductive vector (A:Type) : nat -> Type := 
    | Vnil  : vector A O 
    | Vcons : A -> forall n, vector A n -> vector A (S n).  

Arguments Vnil  {A} . 
Arguments Vcons {A} . 

Unset Implicit Arguments. 

Section vectors_and_lists. 
    Variable A : Set . 
    Fixpoint vector_to_list (n:nat)(v:vector A n){struct v} : list A := 
        match v with 
        | Vnil          => nil 
        | Vcons a p t1  => cons a (vector_to_list p t1) end . 

    Fixpoint list_to_vector (l:list A) : vector A (length l) := 
        match l as x return vector A (length x) with 
        | nil       => Vnil 
        | cons a tl => Vcons a (length tl) (list_to_vector tl)  end. 

    Theorem keep_length : forall n (v:vector A n), length (vector_to_list n v) = n . 
    Proof. intros; elim v; simpl; auto.  Qed. 

    Theorem Vconseq : 
        forall(a:A)(n m:nat), n = m -> forall (v:vector A n)(w: vector A m), 
        JMeq v w -> JMeq (Vcons a n v)(Vcons a m w). 
    Proof. 
        intros. subst n.  
        Print JMeq_ind. 
        now elim H0. 
    Qed. 

    Theorem vect_to_list_to_vect_id : 
        forall n (v:vector A n), 
        JMeq v (list_to_vector (vector_to_list n v)) . 
    Proof. 
        intros.
        elim v; simpl; auto.  
        intros.   
        apply Vconseq;  
        [ symmetry; apply keep_length | trivial ] . 
    Qed. 

End vectors_and_lists. 

(* ex. 8.8 *) 
Lemma JMeq_plus_assoc : forall x y z:nat, JMeq (x+(y+z)) ((x+y)+z) . 
Proof. 
    intros x y z. 
    induction x; simpl; auto.  
    now elim IHx. 
Qed. 
