
CoInductive Stream (A:Type) : Type := 
    | Cons : A -> Stream A -> Stream A. 


Set Implicit Arguments. 

(* Lazy List *) 
CoInductive LList (A:Type) : Type := 
    | LNil  : LList A 
    | LCons : A -> LList A -> LList A. 

Arguments LNil {A} . 

Definition isEmpty (A:Type) (l:LList A) : Prop := 
    match l with 
    | LNil          => True
    | LCons a l'    => False end. 

Definition LHead (A:Type) (l:LList A) : option A :=
    match l with 
    | LNil          => None
    | LCons a _     => Some a end.  

Definition LTail (A:Type) (l:LList A) : LList A :=
    match l with
    | LNil          => LNil 
    | LCons _ x     => x     end.

Fixpoint LNth (A:Type) (n:nat) (l:LList A){struct n} : option A := 
    match l with 
    | LNil          => None
    | LCons a l'    => match n with 
                       | O      => Some a 
                       | S p    => LNth p l' end end. 




Check (LCons 1 (LCons 2 (LCons 3 LNil))). 


(* ex. 13.1 *) 
Fixpoint list2LList {A:Type} (l:list A) : LList A := 
    match l with 
    | nil           => LNil
    | cons a x      => LCons a (list2LList x) end. 

Inductive injective (A B:Type) (f:A->B) : Prop := 
    injective_def: (forall a a' , f a = f a' -> a = a') -> injective f .  

Lemma list2LList_injective : forall A:Type, injective (list2LList (A:=A)) .  
Proof. 
    intros. 
    constructor.  
    intros l k. 
    generalize k. 
    induction l. 
    - intros.  
      induction k0.  
      + trivial . 
      + discriminate H.
    - intros.   
      induction k0. 
      + discriminate H. 
      + intros.  
        inversion H. 
        subst a0. 
        set (IHl k0 H2).  
        now rewrite e. 
Qed. 
(* end ex 13.1 *) 


Eval compute in (LNth 2 (LCons 4 (LCons 3 (LCons 90 LNil)))). 


(* ex. 13.2 *)

(* Lazy Binary Tree *) 
CoInductive LTree (A:Type) : Type := 
    | LLeaf : LTree A
    | LBin  : A -> LTree A -> LTree A -> LTree A. 

Arguments LLeaf {A} .  

Definition is_LLeaf (A:Type) (t:LTree A) : Prop := 
    match t with 
    | LLeaf         => True
    | LBin _ _ _    => False end. 

Definition L_root (A:Type) (t:LTree A) : option A := 
    match t with 
    | LLeaf         => None 
    | LBin a _ _    => Some a end. 

Definition L_left_son (A:Type) (t:LTree A) : LTree A := 
    match t with 
    | LLeaf         => LLeaf
    | LBin _ l _    => l end . 

Definition L_right_son (A:Type) (t:LTree A) : LTree A := 
    match t with 
    | LLeaf         => LLeaf 
    | LBin _ _ r    => r end. 

Inductive OnePath := Left : OnePath | Right : OnePath . 
Definition Path := list OnePath. 

Fixpoint L_subtree (A:Type) (t:LTree A) (p:Path) {struct p} :=
    match t with 
    | LLeaf         => None  
    | LBin a l r    => match p with 
                       | nil            => Some t 
                       | cons Left  ps  => L_subtree l ps 
                       | cons Right ps  => L_subtree r ps end end. 

Fixpoint Ltree_label (A:Type) (t:LTree A) (p:Path) {struct p} :=
    match t with 
    | LLeaf         => None 
    | LBin a l r    => match p with 
                       | nil            => Some a 
                       | cons Left ps   => Ltree_label l ps 
                       | cons Right ps  => Ltree_label r ps end end. 
(* End ex.13.2 *)











(* 13.3 Building Infinite Object *) 

CoFixpoint from n : LList nat := LCons n (from (S n)).

Definition Nats : LList nat := from 0. 

Compute Nats. 

Compute LNth 10000 Nats. 

Definition Squares_from := 
    let sqr := fun n => n*n in 
    cofix F := fun n => LCons (sqr n) (F(S n)) . 




(* Guarded Condition *) 

Eval simpl in (isEmpty Nats) . 
Eval compute in (isEmpty Nats). 

Eval simpl in (from 3). 
Eval compute in (from 3). 

Eval compute in (LHead (LTail (from 3))). 
Eval compute in (LNth 19 (from 17)). 



(* Few Corecursive Functions *) 

CoFixpoint repeat (A:Type) (a:A) : LList A := LCons a (repeat a). 

CoFixpoint LAppend (A:Type) (u v: LList A) : LList A := 
    match u with 
    | LNil          => v 
    | LCons a u'    => LCons a (LAppend u' v) end . 

Eval compute in (LNth 123 (LAppend (repeat 33) Nats)). 

Eval compute in (LNth 123 (LAppend (LCons 0 (LCons 1 (LCons 2 LNil))) Nats)). 




CoFixpoint general_omega (A:Type) (u v: LList A) : LList A := 
    match v with 
    | LNil          => u 
    | LCons b v'    => match u with 
                       | LNil       => LCons b (general_omega v' v)
                       | LCons a u' => LCons a (general_omega u' v) end end . 

Definition omega (A:Type) (u:LList A) : LList A := 
    general_omega u u . 


Compute (LNth 123 (omega (LCons 0 (LCons 1 (LCons 3 (LCons 4 LNil)))))). 


(* ex. 13.3 *) 
CoFixpoint T_R_from n : LTree nat := LBin n LLeaf (T_R_from (S n)). 

Definition all_positive_bin_tree_R := T_R_from 1. 

CoFixpoint T_from n : LTree nat := LBin n (T_from (n+n))(T_from(n+n+1)). 

Definition all_positive_bin_tree := T_from 1. 
(* end *) 

(* ex. 13.4 *) 
CoFixpoint graft (A:Type) (t t':LTree A) := 
    match t with 
    | LLeaf         => t'
    | LBin  a l r   => LBin a (graft l t')(graft r t') end . 
(* end *) 

CoInductive graft_coind (A:Type) (t t' u:LTree A) : Prop := 
    graft_def : graft t t' = u -> graft_coind t t' u. 

CoInductive cograft (A:Type) : LTree A -> LTree A -> LTree A ->  Prop := 
    | graft_lleaf : forall t, cograft LLeaf t t  
    | graft_lbin  : forall a l r l' r' t , 
            cograft l t l' -> cograft r t r' -> cograft (LBin a l r) t (LBin a l' r') .  


(* 13.3.4 Badly Formed Definitions *) 

(*
CoFixpoint filter (A:Type) (p: A -> bool) (l: LList A) : LList A :=
    match l with 
    | LNil          => LNil
    | LCons a l'    => if p a then LCons a (filter p l') else (filter p l') end. 
*)
(*
CoFixpoint F u := 
  match u with 
  | LNil => LNil
  | LCons a v => match a with 
                 | O => LNil
                 | S b => LCons b ( F (F v))  end end. 
*)

(* e.x. 13.5 *)
CoFixpoint LMap (A B:Type) (f:A->B) (l:LList A) := 
    match l with 
    | LNil          => LNil
    | LCons a l'    => LCons (f a) (LMap f l') end. 

(* we cannot define following type, 
   since when f a is LNil we cannot use decomposition lemma to wrap corecursive function .  
CoFixpoint LMapcan (A B:Type) (f:A -> LList B) (l:LList A) := 
    match l with 
    | LNil          => LNil
    | LCons a l'    => LAppend (f a) (LMapcan f l') end. 
 *)


Definition LList_decompose (A:Type) (l:LList A) : LList A := 
    match l with 
    | LNil          => LNil 
    | LCons a l'    => LCons a l' end . 


Theorem LList_decomposition_lemma : 
    forall (A:Type) (l:LList A) , l = LList_decompose l. 
Proof. 
    intros A l. case l; trivial. 
Qed.

Hint Rewrite LList_decomposition_lemma : llist.  



(* ex. 13.6 *) 

Definition LTree_decompose (A:Type) (t:LTree A) : LTree A := 
    match t with 
    | LLeaf             => LLeaf 
    | LBin a l r        => LBin a l r end .


Theorem LTree_decomposition_lemma : 
    forall (A:Type) (t:LTree A), t = LTree_decompose t  . 
Proof. 
    intros A t. case t; trivial. 
Qed. 

Hint Rewrite LTree_decomposition_lemma : ltree . 
(* end *) 

(* ex 13.7 *) 

Fixpoint LList_decomp_n (A:Type) n (l:LList A) : LList A :=  
    match n with 
    | O         => l 
    | S p       => match l with 
                   | LNil           => LNil 
                   | LCons a l'     => LCons a (LList_decomp_n p l') end end.  

Eval simpl in (LList_decomp_n 0 (LAppend (LCons 1 (LCons 2 LNil)) (LCons 3 (LCons 4 LNil)))) . 
Eval simpl in (LList_decomp_n 1 (LAppend (LCons 1 (LCons 2 LNil)) (LCons 3 (LCons 4 LNil)))) . 
Eval simpl in (LList_decomp_n 2 (LAppend (LCons 1 (LCons 2 LNil)) (LCons 3 (LCons 4 LNil)))) . 
Eval simpl in (LList_decomp_n 3 (LAppend (LCons 1 (LCons 2 LNil)) (LCons 3 (LCons 4 LNil)))) . 

Eval simpl in LList_decomp_n 6 Nats . 
Eval simpl in LList_decomp_n 5 (omega (LCons 1 (LCons 2 LNil))) .  

Theorem LList_decomp_n_lemma : forall n l, LList_decomp_n (A:=nat) n l = l . 
Proof. 
  simple induction n; auto.  
  intros. simpl.  
  case l; auto.  
  intros. now rewrite H.  
Qed. 
(* end *) 

Check trans_equal. 

Ltac LList_unfold term := 
    apply trans_equal with (1 := LList_decomposition_lemma term) . 

Lemma LAppend_LNil : forall (A:Type) (v:LList A), LAppend LNil v = v . 
Proof. 
    intros.   
    rewrite (LList_decomposition_lemma (LAppend LNil v)) . 
    now case v. 
Restart. 
    intros. 
    LList_unfold (LAppend LNil v).
    now case v. 
Qed.  

Lemma LAppend_LCons : forall (A:Type) (a:A) u v, LAppend(LCons a u) v = LCons a (LAppend u v). 
Proof. 
    intros. 
    LList_unfold (LAppend (LCons a u) v) . 
    now case v. 
Qed. 

Hint Rewrite LAppend_LNil LAppend_LCons : llists. 


(* ex 13.8 *) 

Lemma from_unfold :  forall n:nat, from n = LCons n (from (S n)) . 
Proof.  intros n.   now LList_unfold (from n) .  Qed. 

Lemma repeat_unfold : forall (A:Type) (a:A) , repeat a = LCons a (repeat a) . 
Proof.  intros .    now LList_unfold (repeat a).  Qed. 

Lemma omega_LNil : forall A:Type, omega LNil = LNil (A := A). 
Proof.  intros.     now LList_unfold (omega (A:=A) LNil).   Qed. 

Lemma general_omega_LNil : forall (A:Type) (u:LList A), general_omega u LNil = u . 
Proof. 
    intros. 
    LList_unfold (general_omega u LNil) .     
    now case u.  
Qed. 


Lemma general_omega_LCons : forall (A:Type) (a:A) u v, 
    general_omega (LCons a u) v = LCons a (general_omega u v) . 
Proof. 
    intros. 
    LList_unfold (general_omega(LCons a u)v). 
    case v.   
    - rewrite (LList_decomposition_lemma (general_omega u LNil)). now case u. 
    - trivial. 
Qed. 

Lemma general_omega_LNil_LCons : forall (A:Type) (a:A) (u:LList A), 
    general_omega LNil (LCons a u) = LCons a (general_omega u (LCons a u)).  
Proof. intros.  now LList_unfold (general_omega LNil (LCons a u)).  Qed. 

Theorem general_omega_shoots_again : forall (A:Type) (v:LList A), 
    general_omega LNil v = general_omega v v . 
Proof. 
    intros. 
    case v. 
    - trivial. 
    - intros. 
      rewrite general_omega_LNil_LCons. 
      now rewrite (LList_decomposition_lemma (general_omega (LCons a l) (LCons a l)) ). 
Qed. 

Hint Rewrite 
    from_unfold repeat_unfold 
    omega_LNil 
    general_omega_LNil general_omega_LCons 
    general_omega_LNil_LCons 
    general_omega_shoots_again                  : llists. 
(* end *) 



(* ex. 13.9 *) 
Lemma graft_LLeaf : forall (A:Type) (u:LTree A),  graft LLeaf u = u . 
Proof. intros. rewrite (LTree_decomposition_lemma (graft LLeaf u)). now case u. Qed.   

Lemma graft_LCons : forall (A:Type) (a:A) (l r t:LTree A), 
        graft (LBin a l r) t = LBin a (graft l t) (graft r t) . 
Proof. 
    intros. 
    now rewrite (LTree_decomposition_lemma (graft (LBin a l r) t)) . 
Qed. 

Hint Rewrite graft_LLeaf graft_LCons : grafts . 

Lemma graft_t_LLeaf : forall (A:Type) (t:LTree A),  cograft t LLeaf t . 
Proof. 
    cofix H. 
    intros. 
    case t.  
    - constructor. 
    - intros.  
      constructor. 
      + apply H. 
      + apply H. 
Qed. 

Hint Rewrite graft_t_LLeaf : cografts . 

(* end *) 



(* 13. 5 Inductive Predicate over Coinductive Types *) 

Inductive Finite (A:Type) : LList A -> Prop := 
    | Finite_LNil  : Finite LNil 
    | Finite_LCons : forall a l, Finite l -> Finite (LCons a l) .  

Hint Resolve Finite_LNil Finite_LCons : llists. 


Lemma one_two_three : Finite (LCons 1 (LCons 2 (LCons 3 LNil))) . 
Proof.   now repeat constructor.  
Restart. auto with llists.         Qed.  

Theorem Finite_of_LCons : forall (A:Type)(a:A) l, Finite (LCons a l) -> Finite l. 
Proof.  intros. now inversion H.  Qed. 

Theorem LAppend_of_Finite : forall (A:Type)(l l':LList A), Finite l -> Finite l' -> Finite(LAppend l l') .  
Proof. induction 1; autorewrite with llists using auto with llists. Qed. 

(* ex 13.10 *)
Theorem general_omega_of_Finite : forall (A:Type)(u v:LList A), Finite u -> Finite v -> 
        general_omega u v = LAppend u (general_omega v v). 
Proof. 
    simple induction 1. 
    - intros; autorewrite with llists using auto with llists. 
    - intros; autorewrite with llists using auto with llists. 
      rewrite H1; auto .   
Qed.  

Theorem omega_of_Finite : forall (A:Type)(u:LList A), Finite u -> omega u = LAppend u (omega u). 
Proof. 
    unfold omega. 
    intros. 
    now apply (general_omega_of_Finite H ). 
Qed. 

(* ex 13.11 *) 
Inductive FiniteTree (A:Type) : LTree A -> Prop := 
    | Finite_LLeaf  : FiniteTree LLeaf 
    | Finite_LBin   : forall a l r, FiniteTree l -> FiniteTree r -> FiniteTree (LBin a l r). 

Theorem graft_t_LLeaf_of_Finite : forall (A:Type) (t:LTree A), FiniteTree t -> graft t LLeaf = t  .
Proof. 
    intros. 
    induction H.  
    - now autorewrite with grafts. 
    - autorewrite with grafts. 
      rewrite IHFiniteTree1. 
      rewrite IHFiniteTree2. 
      reflexivity. 
Qed. 
















(* 13.6 Coinductive Predicates *) 

CoInductive Infinite (A:Type) : LList A -> Prop := 
    Infinite_LCons : forall (a:A) l , Infinite l -> Infinite (LCons a l). 

Hint Resolve Infinite_LCons : llists. 


Definition F_from : (forall n, Infinite (from n)) -> forall n , Infinite (from n). 
    intros H n; rewrite (from_unfold n). 
    constructor.  
    trivial.  
Defined.  


Theorem from_Infinite_VO : forall n, Infinite (from n). 
Proof  cofix H : forall n, Infinite (from n) := F_from H . 

Theorem from_Infinite    : forall n, Infinite (from n) . 
Proof. 
    cofix H. 
    intros n; rewrite (from_unfold n). 
    now constructor.   
    Guarded. 
Qed. 

Print from_Infinite. 




(* ex. 13.12 *)
Print repeat . 

Lemma repeat_infinite : forall A (a:A), Infinite (repeat a) . 
Proof. 
  cofix H. 
  intros. rewrite (repeat_unfold a). 
  constructor. 
  auto.
  Guarded. 
Qed. 
   

Lemma general_omega_infinite : 
  forall A (a:A) (u v:LList A), Infinite (general_omega v (LCons a u)). 
Proof. 
  cofix H. 
  intros. case u; case v; intros; 
    try rewrite general_omega_LNil_LCons; 
    try rewrite general_omega_LCons; now constructor. 
  Guarded. 
Qed. 

Theorem omega_infinite : forall A (a:A) (l:LList A), Infinite (omega (LCons a l)). 
Proof. intros. unfold omega. apply general_omega_infinite. Qed. 
(* end *)


(* ex. 13.13 *) 
Inductive BugInfinite A : LList A -> Prop :=
  | BugInfinite_intro : forall (a:A) l, BugInfinite l -> BugInfinite (LCons a l). 

Lemma BugIninite_is_bug : forall A (l:LList A), ~ BugInfinite l . 
Proof. 
  red. intros.    
  now induction H. 
Qed. 
(* end *)

(* ex. 13.14 *)
CoInductive at_least_one_branch_infinite A : LTree A -> Prop :=
  | left_infinite : forall a l r, 
      at_least_one_branch_infinite l -> at_least_one_branch_infinite(LBin a l r) 
  | right_infinite : forall a l r, 
      at_least_one_branch_infinite r -> at_least_one_branch_infinite(LBin a l r) . 

CoInductive all_branches_infinite A : LTree A -> Prop :=
  | both_infinite : forall a l r,
      all_branches_infinite l -> all_branches_infinite r -> all_branches_infinite(LBin a l r). 

CoFixpoint uniform_tree A (a:A) := LBin a (uniform_tree a)(uniform_tree a).   
CoFixpoint repeat_right A (a:A) := LBin a LLeaf (repeat_right a).  
Require Import Setoid. 

Lemma uniform_tree_unfold : forall A (a:A), 
    uniform_tree a = LBin a (uniform_tree a)(uniform_tree a). 
Proof. intros. now rewrite (LTree_decomposition_lemma (uniform_tree a)) at 1. Qed.

Lemma repeat_right_unfold : forall A (a:A),  repeat_right a = LBin a LLeaf (repeat_right a). 
Proof. intros. now rewrite (LTree_decomposition_lemma (repeat_right a)) at 1. Qed.

Lemma uniform_tree_all_infinite : forall A (a:A), all_branches_infinite (uniform_tree a) . 
Proof. 
  cofix H. 
  intros. rewrite (uniform_tree_unfold a).
  now constructor. Guarded. 
Qed.      

Lemma repeat_right_at_least_one_infinite : forall A (a:A),
    at_least_one_branch_infinite (repeat_right a). 
Proof.  cofix H. intros. rewrite (repeat_right_unfold a). now constructor. Qed.


Theorem all_infinite_at_least_one_infinite : forall A (l:LTree A), 
  all_branches_infinite l -> at_least_one_branch_infinite l. 
Proof. 
  cofix H. 
  intros. 
  inversion H0. 
  apply left_infinite. 
  now apply H. Guarded.  
Qed. 

Inductive at_least_one_branch_finite A : LTree A -> Prop :=
  | LLeaf_has_finite : at_least_one_branch_finite LLeaf
  | left_has_finite : forall a l r, 
      at_least_one_branch_finite l -> at_least_one_branch_finite (LBin a l r)
  | right_has_finite : forall a l r, 
      at_least_one_branch_finite r -> at_least_one_branch_finite (LBin a l r).  

Theorem If_no_finite_branches_then_at_least_one_infinite : forall A (t:LTree A),
  ~ at_least_one_branch_finite t -> at_least_one_branch_infinite t.  
Proof. 
  cofix H. 
  simple destruct t; intros.  
  - destruct H0. constructor.      
  - constructor. 
    apply H. red. intros. apply H0. 
    now apply left_has_finite. 
Qed. 

Theorem If_no_finite_branches_then_all_infinite : forall A (t:LTree A), 
  ~ at_least_one_branch_finite t -> all_branches_infinite t. 
Proof. 
  cofix H. 
  simple destruct t; intros. 
  - destruct H0. constructor. 
  - constructor; 
      apply H; red; intros; apply H0; 
      [apply left_has_finite | apply right_has_finite ]; auto.
Qed. 

Section ClassicalLogic. 
End ClassicalLogic. 
(* end ex. 13.14*)



(* 13.6.4 Elimination Techinique *) 

Theorem LNil_not_Infinite :  forall A, ~ Infinite (LNil (A:=A)). 
Proof.  intros A H. inversion H. Qed. 

(* ex. 13.15 *)
Theorem Infinite_of_LCons : forall A (a:A) u, Infinite (LCons a u) -> Infinite u. 
Proof. intros. now inversion H.  Qed. 

Lemma LAppend_of_Infinite : 
    forall A (u:LList A), Infinite u -> forall v, Infinite (LAppend u v). 
Proof. cofix H. intros. inversion H0. rewrite LAppend_LCons. constructor. auto. Qed.     

Lemma Finite_not_Infinite : forall A (l:LList A), Finite l -> ~ Infinite l. 
Proof. 
    intros. induction H. 
    - intros H'. inversion H'.  
    - intros H'. inversion H'.   
      now apply IHFinite. 
Qed. 

Lemma Not_Finite_Infinite : forall A (l:LList A), ~ Finite l -> Infinite l. 
Proof. 
  cofix H. 
  simple destruct l. 
  - intros. destruct H0. constructor.   
  - intros. constructor. apply H.
    red. intros. apply H0. now constructor. 
Qed. 
(* end *)


(* ex. 13.16 *)
Section Classical. 
  Axiom DoubleNegElim : forall P, ~~P -> P. 

  Lemma Not_Infinite_Finite : forall A (l:LList A), ~ Infinite l -> Finite l. 
  Proof.  
    intros.    apply DoubleNegElim.  
    intros H'. apply H. now apply Not_Finite_Infinite.  
  Qed. 

  Require Import Classical. 
  Lemma Finite_or_Infinite : forall A (l:LList A), Finite l \/ Infinite l.  
  Proof.
    intros.    apply DoubleNegElim. 
    intros H.  apply H. left.  apply Not_Infinite_Finite.  
    intros H'. apply H. right. auto. 
  Qed. 

  Reset Finite_or_Infinite. 
  Require Import Classical. 
  Lemma Finite_or_Infinite : forall A (l:LList A), Finite l \/ Infinite l.  
  Proof. 
    intros; case (classic (Finite l)). 
    - intros. now left.  
    - intros. right. now apply Not_Finite_Infinite.     
  Qed. 
End Classical. 
(* end *) 



(* ex. 13.17 *)
Definition Infinite_ok A (X:LList A -> Prop) :=
  forall l, X l -> exists a, (exists l', l = LCons a l' /\ X l'). 

Definition Infinite1 A (l:LList A) := exists X, Infinite_ok X /\ X l. 

Lemma Not_Infinite_LNil : forall A,  ~ Infinite (A:=A) LNil. 
Proof. 
  red. intros. inversion H.  
Qed. 
Lemma Not_Infinite1_LNil : forall A, ~ Infinite1 (A:=A) LNil.
Proof. 
  red. intros. inversion H. inversion H0. destruct H1 with (l:=LNil (A:=A)).         
  * trivial.
  * destruct H3. destruct H3. discriminate H3.    
Qed. 
Lemma LCons_Infinite1 : forall A (a:A) l, Infinite1 (LCons a l) -> Infinite1 l. 
Proof. 
  simple destruct l; unfold Infinite1; intros; destruct H; destruct H; exists x; split; auto.  
  - destruct H with (LCons a LNil); auto.    
    destruct H1. destruct H1. injection H1. intros. subst. assumption.     
  - destruct H with (LCons a (LCons a0 l0)); auto. 
    destruct H1. destruct H1. injection H1. intros. subst. assumption.  
Qed. 
  
Theorem Infinite_equiv_Infinite1 : forall A (l:LList A), Infinite l <-> Infinite1 l. 
Proof. 
  intros. split. 
  - intros. unfold Infinite1.   
    exists (Infinite (A:=A)). split. 
    + unfold Infinite_ok. 
      intros. inversion H0. exists a. exists l1. now split.  
    + trivial.   Guarded. 
  - intros. apply Not_Finite_Infinite.   
    red. intros HF. induction HF. Guarded. 
    + now apply (Not_Infinite1_LNil (A:=A)).   
    + apply IHHF.  
      now apply LCons_Infinite1 with a.  
Qed. 
(* end ex. 13.17 *) 







(* 13.7 Bisimilarity *) 



(* ex. 13.18 *) 
Lemma LAppend_of_Infnite_0 : 
    forall (A:Type)(l:LList A), Infinite l -> forall l', l = LAppend l l'. 
Proof. 
    intros.  
    destruct H. 
    rewrite LAppend_LCons .   
    cut (l = LAppend l l'). 
    - intros. now rewrite <- H0.     
    - 
Abort.  





(* 13.7.1 bisimilar predicate *) 

CoInductive bisimilar (A:Type) : LList A -> LList A -> Prop :=
    | bisim0 : bisimilar LNil LNil 
    | bisim1 : forall (a:A) l l', bisimilar l l' -> bisimilar (LCons a l)(LCons a l') . 

Hint Resolve bisim0 bisim1 : llists. 

(* ex. 13.19 *) 
Check bisimilar. 
Require Import Relations. 

Print Relations. 
Print equivalence. 
Print relation. 

Lemma bisimilar_refl : forall A,  reflexive _ (bisimilar (A:=A)) .  
Proof. 
    - unfold reflexive. 
      cofix H. 
      intros. 
      case x.
      + constructor.  
      + intros. constructor. 
        now apply H. 
Qed.
Lemma bisimilar_trans : forall A, transitive _ (bisimilar (A:=A)). 
    - unfold transitive . 
      cofix H. 
      intros A x.   
      case x. 
      + intros .    
        inversion H0. now subst.  
      + intros a l y. 
        intros z Hb0.  generalize z. clear z. 
        inversion Hb0. subst.  
        intros.    
        inversion H0. subst. 
        constructor. 
        now apply (H A l l' l'0).  
Qed. 
Lemma bisimilar_sym : forall A, symmetric _ (bisimilar (A:=A)). 
    - unfold symmetric.  
      cofix H. 
      intros A x. 
      case x. 
      + intros.  
        inversion H0. now subst.   
      + intros.   
        inversion H0. subst. 
        constructor.  
        now apply H. 
Qed. 

Theorem bisimilar_equivalence : forall A, equivalence _ (bisimilar (A:=A)). 
Proof. 
    intros. 
    split; [ apply bisimilar_refl | apply bisimilar_trans | apply bisimilar_sym ].  
Qed. 
(* end 13.19 *) 



(*
Require Import Coq.Setoids.Setoid. 

Add Parametric Relation (A:Type) : (@LList A) (@bisimilar A)
    reflexivity  proved by (@bisimilar_refl A)
    symmetry     proved by (@bisimilar_sym A)
    transitivity proved by (@bisimilar_trans A)
    as bisim_rel. 
 *)



Lemma bisimilar_inv_1 : forall A (a a':A) (u u':LList A), bisimilar (LCons a u) (LCons a' u') -> a = a'.   
Proof. intros. now inversion H.  Qed. 

Lemma bisimilar_inv_2 : forall A (a a':A) (u u':LList A), bisimilar (LCons a u)(LCons a' u') -> bisimilar u u'. 
Proof. intros. now inversion H.  Qed. 


(* ex. 13.20 *) 
Lemma bisimilar_LNth : forall A(n:nat)(u v:LList A), bisimilar u v -> LNth n u = LNth n v . 
Proof. 
    simple induction n. 
    simple destruct u; simple destruct v. 
    - now intros. 
    - intros; inversion H. 
    - intros; inversion H. 
    - intros; inversion H. now simpl. 
    - simple destruct u; simple destruct v. 
      + trivial.  
      + intros. inversion H0. 
      + intros. inversion H0. 
      + intros. inversion_clear H0. simpl. now apply H.   
Qed. 


Lemma LNth_bisimilar : 
    forall A (u v:LList A), (forall n, LNth n u = LNth n v) -> bisimilar u v. 
Proof. 
    cofix H. 
    simple destruct u; simple destruct v.   
    - intros. constructor. 
    - intros. discriminate (H0 0).    
    - intros. discriminate (H0 0).    
    - intros. injection (H0 0). intros. subst.    
      constructor. apply H.  
      intros. 
      set (H0 (S n)). 
      assumption . 
Qed. 


       

         
(*
Add Parametric Morphism A : (@LNth A) 
    with signature 
      (@Logic.eq nat) ==> (@bisimilar A) ==> (@Logic.eq (option A)) as LNth_m . 
    apply bisimilar_LNth. 
Qed. 
          
Print LNth_m_Proper . 
 *)
Theorem bisimilar_of_Finite_is_Finite : 
    forall A (l:LList A), Finite l -> forall l', bisimilar l l' -> Finite l' . 
Proof. 
    simple induction 1; simple destruct l'. 
    - auto with llists. 
    - intros. inversion H0.  
    - auto with llists.  
    - intros. inversion H2; subst. 
      constructor.  
      now apply H1. 
Qed. 
     

Theorem bisimilar_of_Infinite_is_Infinite : 
    forall A (l:LList A), Infinite l -> forall l', bisimilar l l' -> Infinite l'. 
Proof. 
    cofix H. 
    intros A l H0. inversion H0; simple destruct l'. 
    - intros. inversion H3.  
    - intros. constructor. apply (H A l0) . 
      + auto with llists.  
      + now apply bisimilar_inv_2 in H3.  
Qed. 


Theorem bisimilar_of_Finite_is_eq : 
    forall A (l:LList A), Finite l -> forall l' , bisimilar l l' -> l = l'. 
Proof. 
    simple induction 1; simple destruct l'.  
    - intros. reflexivity.  
    - intros. inversion H0.   
    - intros. inversion H2. 
    - intros. 
      set (H1 l1). inversion H2.   
      set (e H4). now rewrite e0.    
Qed. 





(* ex. 13.23 *) 
(* redo bisimilarity with LTree ! *)

(* end *) 
(* ex. 13.26 *) 
(* show left-absrobing of graft *) 










(* 13.7.2 Using Bisimilarity *) 

Theorem LAppend_assoc : 
    forall A (u v w:LList A), bisimilar (LAppend u (LAppend v w)) (LAppend (LAppend u v) w) . 
Proof. 
    intro A; cofix H. 
    destruct u; intros; autorewrite with llists using auto with llists. 
    apply bisimilar_refl. 
Qed. 



(* 13.24 *) 

Lemma LAppend_of_Infinite_bisim : 
    forall A (u:LList A), Infinite u -> forall v, bisimilar u (LAppend u v). 
Proof. 
    intros A; cofix H.  
    simple destruct u; simple destruct v.   
    - intros. rewrite LAppend_LNil. apply bisimilar_refl.    
    - intros. inversion H0.  
    - inversion H0. rewrite LAppend_LCons. constructor. auto .
    - intros. inversion H0; subst. rewrite LAppend_LCons. constructor.  auto. 
Qed.



(* 13.25 *) 
Lemma general_omega_LAppend : 
    forall A (u v:LList A), bisimilar (general_omega u v) (LAppend u (general_omega v v)). 
Proof. 
    intros A; cofix H.
    simple destruct u; simple destruct v. 
    - rewrite LAppend_LNil. apply bisimilar_refl.    
    - intros. rewrite LAppend_LNil. autorewrite with llists using auto with llists.  
      apply bisimilar_refl. 
    - rewrite LAppend_LCons.  
      rewrite general_omega_LCons. 
      constructor. apply H.  
    - intros. autorewrite with llists using auto with llists.   
      constructor. autorewrite with llists using auto with llists.  
      rewrite <- general_omega_LCons. 
      apply H. 
Qed. 


Theorem omega_LAppend : 
    forall A (u:LList A), bisimilar (omega u) (LAppend u (omega u)). 
Proof. 
    unfold omega. 
    intros. apply (general_omega_LAppend). 
Qed. 
















(* 13.8 Park Principle *) 


Print relation. 

Definition bisimulation A (R:relation(LList A)) := 
    forall l1 l2: LList A , 
    R l1 l2 ->  match l1 with 
                | LNil          => l2 = LNil
                | LCons a l     => 
                    match l2 with 
                    | LNil      => False 
                    | LCons b k => a=b /\ R l k     end end. 


Lemma R_LCons : forall A (R:relation (LList A)) (l1 l2:LList A) a1 a2,  
    R (LCons a1 l1) (LCons a2 l2) -> R l1 l2.  
Proof. 
    intros. 
Abort. 

(* ex. 13.27 *) 
Theorem park_principle : 
    forall A (R: relation(LList A)), bisimulation R -> forall l1 l2, R l1 l2 -> bisimilar l1 l2. 
Proof. 
    cofix H. 
    simple destruct l1; simple destruct l2.   
    - intros. constructor.   
    - intros. set(H0 LNil(LCons a l)). simpl in y. apply y in H1. discriminate.          
    - intros. set(H0(LCons a l)LNil) . simpl in y. apply y in H1. now apply False_ind.  
    - intros. set(H0(LCons a l)(LCons a0 l0)). simpl in y. destruct y. 
      + assumption. 
      + subst. constructor. now apply (H A R).   
Qed. 


(* ex. 13.28 *) 
CoFixpoint alter : LList bool := LCons true (LCons false alter). 

Definition alter2 : LList bool := omega (LCons true (LCons false LNil)). 

Definition R l1 l2 : Prop := 
    l1=alter             /\ l2=alter2 \/ 
    l1=LCons false alter /\ l2=LCons false alter2. 

Lemma R_bisimilar : bisimulation R . 
Proof. 
    unfold bisimulation, R. 
    repeat simple induction 1; subst; simpl.  
    - split; auto.  
      right. split; autorewrite with llists using auto with llists. trivial. 
    - split; auto.  
Qed. 

Lemma alter_alter2_bisim : bisimilar alter alter2. 
Proof. 
    apply (park_principle (R:=R)). 
    - exact R_bisimilar.  
    - unfold R. auto.   
Qed. 
















(* 13.9 LTL *) 



Section LTL. 

  Variables (A:Type) (a b c:A) .

  Definition satisfies (l:LList A) (P: LList A -> Prop) : Prop := P l . 

  Hint Unfold satisfies : llists. 


  Inductive Atomic (P: A -> Prop) : LList A -> Prop := 
    | Atomic_intro : forall (a:A) l, P a -> Atomic P (LCons a l). 

  Inductive Next (P: LList A -> Prop) : LList A -> Prop := 
    | Next_intro : forall (a:A) l,  P l -> Next P (LCons a l). 

  Hint Resolve Atomic_intro Next_intro : llists. 

  Theorem Next_example : satisfies (LCons a (repeat b)) (Next (Atomic (eq b))). 
  Proof. rewrite (repeat_unfold b); auto with llists.  Qed. 


  Inductive Eventually P : LList A -> Prop := 
    | Eventually_here    : forall (a:A) l,  P (LCons a l) -> Eventually P (LCons a l) 
        (*| Eventually_here    : forall (l:LList A),  P l -> Eventually P l *)
    | Eventually_further : forall (a:A) l, Eventually P l -> Eventually P (LCons a l).

  CoInductive Always P : LList A -> Prop :=
    | Always_LCons : forall (a:A) l, P (LCons a l) -> Always P l -> Always P (LCons a l). 

  Hint Resolve Always_LCons Eventually_here Eventually_further : llists. 

  Definition F_Infinite P := Always (Eventually P). 
  Definition G_Infinite P := Eventually (Always P). 



  (* ex 13.29 *) 
  Theorem Eventually_of_LAppend : forall P(u v:LList A), 
    Finite u -> satisfies v (Eventually P) -> satisfies (LAppend u v) (Eventually P). 
  Proof. 
    unfold satisfies; induction 1; intros; 
    autorewrite with llists using auto with llists. 
  Qed. 
  (* ex 13.29 is solved at the next section *) 


  (* ex 13.30 *) 
  Theorem Always_Infinite : forall P (l:LList A) , Always P l -> Infinite l.  
  Proof. cofix H. intros. inversion H0. constructor. now apply (H P).  Qed. 

  (* ex 13.31 *) 
  Lemma always_a : satisfies (repeat a) (Always (Atomic (eq a))) . 
  Proof. 
    unfold satisfies. cofix H.  
    rewrite (repeat_unfold a) . 
    constructor.
    - now constructor.  
    - apply H.  
  Qed. 

  (* ex. 13.33 *)
  Lemma LAppend_G_Infinite : forall P (u v:LList A), 
    Finite u -> satisfies v (G_Infinite P) -> satisfies (LAppend u v) (G_Infinite P). 
  Proof. 
    unfold satisfies, G_Infinite. intros. 
    induction H. 
    - now rewrite LAppend_LNil.  
    - rewrite LAppend_LCons . 
      now apply Eventually_further. 
  Qed.  

  Lemma LAppend_G_Infinite_R : forall P (u v:LList A), 
    Finite u -> satisfies (LAppend u v) (G_Infinite P) -> satisfies v (G_Infinite P) . 
  Proof.
    unfold satisfies, G_Infinite. 
    simple destruct v; intros; induction H. 
    - now rewrite LAppend_LNil in H0.  
    - inversion H0.     
      + rewrite LAppend_LCons in H1.
        injection H1; intros; subst; clear H1. apply IHFinite.    
        inversion H2; subst. 
        destruct l; inversion H3. 
        * rewrite LAppend_LNil in H1; discriminate H1. 
        * rewrite LAppend_LCons in H1; injection H1; intros; subst; clear H1.     
          constructor. now rewrite <- LAppend_LCons.  
      + rewrite LAppend_LCons in H1; injection H1; intros; subst; clear H1.  
        auto. 
    - now rewrite <- LAppend_LNil.  
    - rewrite LAppend_LCons in H0.  
      inversion H0;subst. 
      + inversion H2; subst.   
        destruct l0; inversion H3. 
        * rewrite LAppend_LNil in H1; injection H1; intros; subst; clear H1.   
          rewrite LAppend_LNil in H3. now apply Eventually_here in H3.  
        * rewrite LAppend_LCons in H1; injection H1; intros; subst; clear H1.   
          apply IHFinite . 
          rewrite LAppend_LCons in H3. apply Eventually_here in H3.  
          now rewrite LAppend_LCons. 
      + now apply IHFinite.  
  Qed. 

End LTL. 


(* ex. 13.29 *)

Section ex_13_29 . 
  Definition P := Atomic (eq 1). 
  Definition v := LCons 1 LNil. 
  Definition u := repeat 0. 

  Theorem ex_13_29_counterexample : forall ns, ns = LAppend u v -> 
      ~ satisfies ns (Eventually P). 
  Proof. 
    unfold P, v, u, satisfies. 
    intros Heq H H' .   
    rewrite repeat_unfold, LAppend_LCons in H.     
    induction H' as [n ns ato|]. 
    - inversion ato. subst. 
      discriminate H. 
    - injection H; intros; subst; clear H.      
      apply IHH'. rewrite repeat_unfold at 1. now rewrite LAppend_LCons. 
  Qed. 
End ex_13_29. 



(* 13.10 Automaton *)

Require Import List. 
Import ListNotations. 

Record automaton : Type :=
    mk_auto {
      state       : Set;
      action      : Set;
      initial     : state;
      transition  : state -> action -> list state }. 

Definition deadlock A q := 
  forall a, @transition A q a = nil. 

CoInductive Trace A : state A -> LList(action A) -> Prop :=
  | empty_trace : forall q, deadlock A q -> Trace A q LNil 
  | lcons_trace : forall q q' a l, In q' (transition A q a) -> Trace A q' l -> Trace A q (LCons a l).

Theorem Trace_inv A : forall q a l, Trace A q (LCons a l) -> exists q', Trace A q' l . 
Proof. intros. inversion H. subst. now exists q'. Qed. 

Theorem Trace_cons A : forall q a q' l, 
  Trace A q (LCons a l) -> @transition A q a = [q'] -> Trace A q' l. 
Proof. intros. inversion H. subst. rewrite H0 in H4. destruct H4; subst; now idtac. Qed.   

(* ex. 13.34 *)

Inductive st    := q0 | q1 | q2. 

Inductive act  := a | b . 

Definition trans q x : list st :=
  match q , x with 
  | q0, a => [q1] 
  | q0, b => [q1]
  | q1, a => [q2]
  | q2, b => [q2;q1]
  | _ , _ => [] 
  end. 

Definition A1 := mk_auto q0 trans . 


Lemma A1_no_deadlock : forall q, ~ deadlock A1 q. 
Proof. 
  unfold deadlock; simple destruct q; intros dl.
  - set (dl a). discriminate e.    
  - set (dl a). discriminate e. 
  - set (dl b). discriminate e. 
Qed. 


Lemma A1_trace : forall q t, Trace A1 q t -> 
  exists q' act t',   t = LCons act t' 
                  /\  Trace A1 q' t' 
                  /\  (   (q,act,q') = (q0,a,q1)
                      \/  (q,act,q') = (q0,b,q1)
                      \/  (q,act,q') = (q1,a,q2)
                      \/  (q,act,q') = (q2,b,q1)
                      \/  (q,act,q') = (q2,b,q2)  ). 
Proof. 
  intros. 
  inversion H as [| q_ q' act tail inq trace] .  
  - now destruct A1_no_deadlock with q. 
  - exists q', act, tail. subst q_ t.   
    split; auto. 
    split; auto. 
    destruct q, act; inversion inq; subst.   
    + now left.  
    + now idtac.   
    + now (right; left). 
    + now idtac. 
    + now (right; right; left).    
    + now idtac.  
    + now repeat right.  
    + inversion H0. subst.  
      * now (right; right; right; left).   
      * now idtac.  
Qed. 


Lemma A1_Eventually_b : forall q t, Trace A1 q t -> Eventually (Atomic (eq b)) t. 
Proof. 
  intros. 
  destruct (A1_trace H) as [ q' [ act [ t' [ Heq [ trace [|[|[|[|]]]]]]]]];
      injection H0; intros; subst; clear H0.  
  - apply Eventually_further.  
    destruct (A1_trace trace) as [q' [act' [ t'' [ Heq [ trace' [|[|[|[|]]]]]]]]];
        try discriminate; injection H0; intros; subst; clear H0.  
    apply Eventually_further. 
    destruct (A1_trace trace') as [q' [act' [ t''' [ Heq [ trace'' [|[|[|[|]]]]]]]]]; 
        try discriminate; injection H0; intros; subst; clear H0.  
    + now constructor.  
    + now constructor.  
  - now constructor.  
  - apply Eventually_further.  
    destruct (A1_trace trace) as [q' [act' [ t'' [ Heq [ trace' [|[|[|[|]]]]]]]]];
        try discriminate; injection H0; intros; subst; clear H0.  
    + now constructor. 
    + now constructor. 
  - now constructor.  
  - now constructor. 
Qed. 

Theorem Infinite_bs : forall q t, Trace A1 q t -> 
  satisfies t (F_Infinite (Atomic (eq b))). 
Proof. 
  unfold satisfies, F_Infinite. 
  cofix coH. 
  intros. 
  inversion H as [| q_ q' act tail inq2 trace' Heq Heqtl] ; subst. 
  - now destruct A1_no_deadlock with q.  
  - constructor. 
    + now apply A1_Eventually_b with q. 
    + now apply coH with q'.  
Qed. 





  


                      





Lemma q2_b : forall t,Trace A1 q2 t-> Atomic (eq b) t. 
Proof . 
  simple destruct t; intros. 
    - inversion H. unfold deadlock in H0. set (H0 b). inversion e.  
    - destruct a0.      
      + inversion H. destruct H3.    
      + now constructor.  
Qed. 

Lemma q1_Next_b : forall t, Trace A1 q1 t -> Next (Atomic (eq b)) t. 
Proof. 
  simple destruct t; intros. 
  - inversion H. unfold deadlock in H0. set (H0 a). inversion e. 
  - destruct a0.  
    + constructor. apply q2_b.   
      set (Trace_inv H). 
      destruct e.  
      set (@transition A1 q1 a). 
      apply Trace_cons with q1 a; auto.  
    + inversion H. inversion H3.  
Qed. 

Lemma Next_Eventually : forall A P a l, Next (Next P) (LCons a l) -> Eventually P (LCons a l) (A:=A). 
Proof.  
  intros. 
  inversion H. subst. 
  apply Eventually_further. 
  subst.   
  case l. 
Abort. 

      

Lemma q0_Eventually_b : forall t, Trace A1 q0 t -> Eventually (Atomic (eq b)) t. 
Proof. 
  simple destruct t.   
  - intros. inversion H. unfold deadlock in H0. set (H0 a). inversion e.     
  - simple destruct a0; intros; inversion H; subst.    
    + destruct H3; subst.   
      apply q1_Next_b in H4. 
      apply Eventually_further.  
Abort.       

      




