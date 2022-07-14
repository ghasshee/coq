(* Add LoadPath "../" as pp.  *)
(* Require Import chap08.  *)
Require Import List. 
Import ListNotations. 

Record group : Type := 
  { A   : Type;
    op  : A -> A -> A ;
    sym : A -> A ;
    e   : A ;
    e_neutral_left : forall x : A , op e x = x ;
    sym_op : forall x:A, op (sym x) x = e;
    op_assoc : forall x y z : A, op (op x y) z = op x (op y z); 
    op_comm : forall x y : A, op x y = op y x }. 


Check Build_group. 

Check list. 
Check list_ind. 

(* Variably Dependent Inductive Type *)
Inductive htree (A:Set) : nat -> Set := 
    | hleaf : A -> htree A O
    | hnode : forall n:nat, A -> htree A n -> htree A n -> htree A (S n). 

Check htree_ind. 

Print list. 


Print nat_rec. 

Check le_ind. 




(* ex. 14.1 *)
Locate "+". 

Check nat_rec. 

Definition add m := 
    nat_rec (fun _ => nat) m (fun n n_plus_m => S n_plus_m) .  

Compute add 3 4 . 



(* ex. 14.3 *) 

Require Import List. 
Import ListNotations. 

Inductive sorted {A:Set} (R:A->A->Prop) : list A -> Prop := 
    | sorted0 : sorted R  [] 
    | sorted1 : forall x, sorted R [x] 
    | sorted2 : forall x y (l:list A), R x y -> sorted R(y::l)-> sorted R (x::y::l).

Check sorted_ind. 
Print sorted_ind. 

Fixpoint sorted_ind_max {A:Set} (R:A->A->Prop) 
      (P : forall l:list A, sorted R l -> Prop)  
      (p0 : P [] (sorted0 R)) 
      (p1 : forall x, P [x] (sorted1 R x)) 
      (p2 : forall x y l (r:R x y) (s:sorted R(y::l)), P(y::l)s -> 
            P (x::y::l) (sorted2 R x y l r s)) 
      (l: list A) (s : sorted R l) { struct s } : P l s := 
      match s as x0 in (sorted _ l0) return P l0 x0 with 
      | sorted0 _ => p0
      | sorted1 _ x => p1 x
      | sorted2 _ x y l0 r s0 => p2 x y l0 r s0 (sorted_ind_max R P p0 p1 p2(y::l0)s0)    
      end.   

Check sorted_ind_max. 
Check sorted_ind. 

(* end ex. 14.3 *) 



Definition rich_minus (n m:nat) := { x : nat | x + m = n }. 
Definition le_rich_minus : forall m n : nat , n <= m -> rich_minus m n. 
Proof. 
  induction m.
  - intros n Hle. 
    exists n. 
    now inversion Hle.
  - intros n. case n. 
    + intros Hle; now exists (S m).  
    + intros n' Hle. elim (IHm n') .   
      * intros r Heq. 
        exists r. 
        now rewrite <- Heq. 
      * inversion Hle; auto with arith.   
Qed. 


(* ex. 14.4 *) 

Definition pred_partial : forall n:nat, n<>O -> nat. 
    induction n; intros h; 
    [ now elim h | exact n ] .  
Defined. 

(* 9.2.4 Proving Preconditions *) 
Open Scope nat. 
Require Import Lia.

Theorem le_2_n_not_O : forall n:nat, 2 <= n -> n <> 0 . 
Proof. intuition . rewrite H0 in H. inversion H. Qed. 

Scheme le_ind_max := Induction for le Sort Prop. 
Check le_ind_max. 
Theorem le_2_n_pred : forall n (h:2<=n), pred_partial n (le_2_n_not_O n h) <> 0 .   
    (* cannot solve 2nd order unification *) 
Proof. 
  intros. 
  apply (le_ind_max 2 (fun n' h => pred_partial n' (le_2_n_not_O n' h) <> 0 )); 
  intros; simpl; lia. 
  (* Qed. *) 
Restart. (* without Lia *) 
  intros. 
  apply (le_ind_max 2 (fun n' h => pred_partial n' (le_2_n_not_O n' h) <> 0 )). 
  - now simpl. 
  -  intros. simpl. inversion l. 
    + subst. now simpl in H.   
    + subst. now idtac.   
Qed. 
(* end 14.4 *) 

(* ex. 14.5 *) 
Set Implicit Arguments. 

Inductive lfactor (A:Set) : list A -> list A -> Prop :=
  | lf1 : forall u, lfactor [] u
  | lf2 : forall a u v, lfactor u v -> lfactor (a::u)(a::v) . 

Definition list_minus : forall (A:Set) u v, lfactor u v -> {w : list A | v = u ++ w}. 
Proof. 
  simple induction u; simple induction v; intros.
  - now exists []. 
  - now exists (a::l).  
  - destruct (H []). 
    + inversion H0.  
    + exists []. inversion H0.   
  - destruct (H l0).  
    + now inversion H1.  
    + subst. exists x.     
      now inversion H1.  
Qed. 

Unset Implicit Arguments. 
(* end *)





Print eq.  
Print eq_rec. 

(*
Definition eq_rect (A:Type) (x:A) (P: A -> Type)(f : P x)(y:A)(e : x = y) : P y
  := match e in (_ = x) return P x with 
     | refl_equal => f 
     end. 

Definition eq_rec {A} x (P:A -> Set) := eq_rect A x P. 
 *)

Section update_def. 
  Variables (A : Set)(A_eq_dec : forall x y:A, {x = y}+{x <> y}). 
  Variables (B : A -> Set) (a:A) (v:B a) (f : forall x, B x). 

  Definition update (x:A) : B x := 
    match A_eq_dec a x with 
    | left h    => eq_rec a B v x h
    | right h'  => f x end . 
End update_def.  

Require Import Eqdep .
Print eq_rec_eq. 

Check update. 

(* ex. 14.6 *) 
Theorem update_eq : forall A eq_dec B a v f , update A eq_dec B a v f a = v . 
Proof. 
  intros A eq_dec B a v f. 
  unfold update. destruct (eq_dec a a). 
  - now rewrite <- eq_rec_eq. 
  - now idtac.    
Qed.


    



(* 14.3 Mutually Inductive Type *) 


Inductive ntree (A:Set) : Set := 
  | nnode : A -> nforest A -> ntree A 
with nforest (A:Set) : Set := 
  | nnil  : nforest A 
  | ncons : ntree A -> nforest A -> nforest A . 

Require Import ZArith Arith . 
Open Scope Z_scope. 

Fixpoint count A (t:ntree A) := 
  match t with 
  | nnode _ a l => 1 + count_list A l end 
with count_list A l := 
  match l with 
  | nnil  _     => 0 
  | ncons _ t l => count A t + count_list A l end .  



Check ntree_ind. 

Scheme ntree_ind2 := 
  Induction for ntree Sort Prop
with nforest_ind2 := 
  Induction for nforest Sort Prop . 

Inductive occurs (A:Set) (a:A) : ntree A -> Prop := 
  | occurs_root     : forall l,   occurs A a (nnode A a l)
  | occurs_branches : forall b l, occurs_forest A a l -> occurs A a (nnode A b l)
with occurs_forest (A:Set) (a:A) : nforest A -> Prop := 
  | occurs_head : forall t tl, occurs A a t -> occurs_forest A a (ncons A t tl)
  | occurs_tail : forall t tl, occurs_forest A a tl -> occurs_forest A a (ncons A t tl). 



Fixpoint n_sum_values t := 
  match t with 
  | nnode _ z l   => z + n_sum_values_l l end 
  with n_sum_values_l l := 
  match l with 
  | nnil _      => 0
  | ncons _ t tl  => n_sum_values t + n_sum_values_l tl end . 

Check n_sum_values. 


Theorem greater_values_sum : 
  forall t, (forall x, occurs Z x t -> 1 <= x) -> count Z t <= n_sum_values t. 
Proof. 
  induction t using ntree_ind2 with 
    ( P0 := fun l => (forall x, occurs_forest Z x l -> 1 <= x) -> 
                      count_list Z l <= n_sum_values_l l). 
  - intros Hocc; lazy beta iota delta - [Zplus Z.le].  
    fold count_list n_sum_values_l. 
    SearchPattern (_ + _ <= _ + _ ). 
    apply Z.add_le_mono. 
    + apply Hocc. constructor.  
    + apply IHt. intros. apply Hocc. now constructor.     
  - auto with zarith. 
  - intros Hocc; lazy beta iota delta - [Zplus Z.le];
    fold count count_list n_sum_values n_sum_values_l. 
    apply Z.add_le_mono. 
    + apply IHt. intros. apply Hocc. now constructor. 
    + apply IHt0. intros. apply Hocc. now constructor.   
Qed. 



Inductive ltree A := 
  | lnode : A -> list (ltree A) -> ltree A. 

Check ltree_ind. 

Section correct_ltree_ind. 
  Variables (A:Type) (P:ltree A -> Prop) (Q:list (ltree A) -> Prop). 

  Hypotheses
    (H : forall a l, Q l -> P (lnode A a l))
    (H0: Q []) 
    (H1: forall t, P t -> forall l, Q l -> Q (t::l)). 

  Fixpoint ltree_ind2 t : P t := 
    match t as x return P x with 
    | lnode _ a l => 
        H a l ((fix l_ind l' : Q l' :=
                match l' as x return Q x with 
                | nil   => H0 
                | x::xs => H1 x (ltree_ind2 x) xs (l_ind xs) end ) l) end .  

  (* ex. 14.7 *) 
  Fixpoint list_ltree_ind2 l : Q l := 
    match l as x return Q x with 
    | nil     => H0 
    | x :: xs => H1 x (ltree_ind2 x) xs (list_ltree_ind2 xs) end . 

End correct_ltree_ind. 
    
Check list_ltree_ind2 . 
Check ltree_ind2 . 

Section correct_ltree_rec. 
  Variables (A:Type) (P:ltree A -> Set) (Q:list (ltree A) -> Set). 

  Hypotheses
    (H : forall a l, Q l -> P (lnode A a l))
    (H0: Q []) 
    (H1: forall t, P t -> forall l, Q l -> Q (t::l)). 

  Fixpoint ltree_rec2 t : P t := 
    match t as x return P x with 
    | lnode _ a l => 
        H a l ((fix l_rec l' : Q l' :=
                match l' as x return Q x with 
                | nil   => H0 
                | x::xs => H1 x (ltree_rec2 x) xs (l_rec xs) end ) l) end .  

  (* ex. 14.7 *) 
  Fixpoint list_ltree_rec2 l : Q l := 
    match l as x return Q x with 
    | nil     => H0 
    | x :: xs => H1 x (ltree_rec2 x) xs (list_ltree_rec2 xs) end . 

End correct_ltree_rec. 
    
Check list_ltree_rec2 . 
Check ltree_rec2 . 
Check list_rec. 


(* ex. 14.8 *)
Definition lcount := ltree_rec2 Z _ _ (fun _ _ l => l + 1) 0 (fun _ x _ xs => x + xs). 

Compute lcount (lnode Z 3 [lnode _ 1 [];lnode _ 2 [];lnode _ 3[]]). 


Scheme ntree_rec2 := 
  Induction for ntree Sort Set
with nforest_rec2 :=
  Induction for nforest Sort Set. 

Check ltree_rec2. 
Check ntree_rec2. 

Definition ltree_to_ntree (A:Set) := 
  ltree_rec2 A _ _ 
    (fun a _ l    => nnode A a l) (nnil A) 
    (fun _ t _ l  => ncons A t l) .  

Compute ltree_to_ntree _ (lnode Z 3 [lnode _ 1 [];lnode _ 2 [];lnode _ 3[]]). 

Definition ntree_to_ltree (A:Set) := 
  ntree_rec2 A _ _
    (fun a _ l    => lnode _ a l)  []
    (fun _ t _ l  => t::l) . 

Check list_ltree_rec2. 
Definition list_ltree_to_nforest (A:Set) := 
  list_ltree_rec2 A _ _ 
    (fun a _ l    => nnode _ a l) (nnil A)
    (fun _ t _ l  => ncons A t l) . 
    
Definition nforest_to_list_ltree (A:Set) := 
  nforest_rec2 A _ _ 
    (fun a _ l    => lnode _ a l)  []
    (fun _ t _ l  => t::l) . 
    
Theorem ntree_ltree_equiv : forall (A:Set) (t:ltree A), 
    ntree_to_ltree _ (ltree_to_ntree A t) = t. 
Proof. 
  intros A.
  induction t using ltree_ind2 with 
   (Q := fun l => nforest_to_list_ltree _ (list_ltree_to_nforest A l) = l); 
  try rewrite <- IHt at -1; try rewrite <- IHt0 at -1; now compute. 
  (*
  - rewrite <- IHt at -1. 
    now compute. 
  - now compute.   
  - rewrite <- IHt , <- IHt0 at -1. 
    now compute.  
  *)
Qed. 

Theorem ltree_ntree_equiv : forall (A:Set) (t:ntree A),
    ltree_to_ntree _ (ntree_to_ltree A t) = t. 
Proof. 
  intros A. 
  induction t using ntree_ind2 with 
    (P0 := fun l => list_ltree_to_nforest _ (nforest_to_list_ltree A l) = l);
  try rewrite <- IHt at -1; try rewrite <- IHt0 at -1; now compute. 
Qed. 


