(* Chapter 6. Insuctive Data Types *) 

(* 6.1 Types Without Recursion *) 

(* 6.1.1. Enumerated Types *) 

Check nat_ind. 

Inductive month : Set := 
    | January   : month 
    | February  : month 
    | March     : month 
    | April     : month 
    | May       : month 
    | June      : month 
    | July      : month 
    | August    : month 
    | September : month 
    | October   : month 
    | November  : month 
    | December  : month . 

(* 6.1.2 Simple Reasoning and Computing *) 
Theorem month_equal : forall m:month , 
    m = January \/ m = February \/ m = March      \/
    m = April   \/ m = May      \/ m = June       \/ 
    m = July    \/ m = August   \/ m = September  \/
    m = October \/ m = November \/ m = December   . 
Proof. 
  intro m. pattern m. apply month_ind.
  left. reflexivity.  
  right. left. reflexivity. 
  right. right. left. reflexivity. 
  right. right. right. left. reflexivity. 
  right. right. right. right. left. reflexivity. 
Restart. 
  induction m; tauto. 
Restart. 
  induction m; auto 12. 
Qed. 



(* ex 6.1 *) 
Inductive season : Set := 
    | Spring : season | Summer : season | Autumn : season | Winter : season . 

Check month_rec. 
Definition season_of_month := month_rec (fun m => season ) 
      Winter Winter Spring Spring Spring Summer 
      Summer Summer Autumn Autumn Autumn Winter.  

Eval compute in season_of_month January. 


(* 6.1.4 Pattern Matching *) 
(* month length *) 
Definition month_length (leap:bool) := month_rec (fun m=>nat) 
      31 (if leap then 29 else 28) 31 30 31 30 31 31 30 31 30 31 .

Definition month_length'' (leap:bool) (m:month) :=
      match m with 
      | February                              => if leap then 29 else 28 
      | April | June | September | November   => 30 
      | other                                 => 31             end . 

(* ex. 6.4 *) 
(* ex. 6.5 *) 
(* ex. 6.6 *) 
Definition bool_id      := bool_rec (fun _=> bool) true false.  
Definition bool_not     := bool_rec (fun _=> bool) false true. 
Definition bool_xor     := bool_rec _  bool_not    (fun b:bool=>b) . 
Definition bool_and     := bool_rec _ (fun b => b) (fun _ => false) . 
Definition bool_or      := bool_rec _ (fun _ => true) (fun b => b) . 
Definition bool_eq      := bool_rec _ (fun b => b)     bool_not . 
Definition bool_nor     := bool_rec _ (fun b => false) bool_not . 

Compute bool_not true. 
Compute bool_eq  true true . 
Compute bool_eq  false false. 
Compute bool_xor true true . 
Compute bool_xor true false. 
Compute bool_xor false true. 
Compute bool_xor false false. 
(* end ex. 6.6 *)  


(* 6.1.5 Record Type *) 
Require Import ZArith . 

Inductive plane : Set := point : Z -> Z -> plane . 

Definition abscissa (p:plane) :Z := match p with point x y => x end . 

(* ex. 6.7  skip *)
(* ex. 6.8  skip *) 


(* 6.1.6 Records with Variants *) 
Inductive vehicle : Set := 
    | bicycle   :   nat         -> vehicle 
    | motorized :   nat -> nat  -> vehicle.

Check vehicle_ind.

Definition nb_wheels (v:vehicle) : nat := 
  match v with 
  | bicycle     x   => 2
  | motorized   x n => n                end. 

Definition nb_seats (v:vehicle) : nat := 
  match v with 
  | bicycle     x   => x
  | motorized   x n => x                end. 

(* ex. 6.9 *) 
Print vehicle_rec. 
Definition nb_seats' := 
  vehicle_rec (fun _ => nat) (fun seat => seat) (fun seat wheel => seat) .  
Compute  nb_seats (bicycle 2) . 
Compute  nb_seats (motorized 4 5). 

Theorem eq_nb_seats_nb_seats' : nb_seats = nb_seats'.  Proof. trivial. Qed. 

(* end ex. 6.9 *)


(* 6.2 Case Based Reasoning *) 

(* 6.2.1 the case Tactic *) 
Theorem at_least_28 :  forall (leap:bool) (m:month) , 28 <= month_length leap m . 
Proof .
  intros leap m. 
  case m    ; simpl; auto with arith. 
  case leap ; simpl; auto with arith. 
Qed. 

Print at_least_28. 



(* 6.2.2 discriminate tactic / injection tactic *)  
Definition next_month := month_rec (fun _ => month) 
    February March April May June July August September October November December January. 

Theorem not_January_eq_February : ~ January = February . 
Proof. 
  unfold not; intros H. 
  change ((fun m => match m with 
                    | January => True 
                    | _       => False end ) February ). 
  now rewrite <- H. 
Qed. 

(* ex. 6.10   skip *)

(* ex 6.11 *) 
Theorem not_true_eq_false : ~ true = false . 
Proof. 
  unfold not; intros H. 
  change ((bool_rect (fun _=>Type) True False) false). 
  now rewrite <- H . 
Qed. 

(* ex 6.12 *) 
Theorem not_bicyvle_eq_motorized : forall x y z:nat, not ( bicycle x = motorized y z ) . 
Proof. 
  unfold not; intros x y z H . 
  change ((vehicle_rect (fun _ => Type) (fun _ => True)  (fun _ _ => False)) (motorized y z)). 
  now rewrite <- H. 
Qed. 


(* 6.2.3 Injective Constructors *)

(* 6.2.3.1 "injection" tactic *)

(* 6.2.3.2 Inner Working of "injection" tactic *) 

Section injection_example. 
  Variable A B : Set. 

  Inductive T : Set := 
    | c1 : A -> T 
    | c2 : B -> T . 

  Theorem inject_c2 : forall x y : B, c2 x = c2 y -> x = y .
  Proof. 
    intros x y H .
    change (let proj2 := fun v:T => match v with 
                                    | c2 v'  => v' 
                                    | _      => x (* or y *) end in  
            proj2 (c2 x) = proj2 (c2 y) ). 
    now rewrite H. 
  Qed. 
End injection_example. 



(* 6.2.4 Inductive Types and Equality *) 

(* ex 6.13 *) 
Require Import Arith. 
Section Rat. 
  Record RatPlus : Set := 
    mkRat { top:nat; bottom:nat; bottom_cond : not (bottom = 0) }. 
  
  Axiom eq_RatPlus : forall r r': RatPlus, 
      top r * bottom r' = top r' * bottom r -> r = r' . 
  
  Lemma not_2_eq_0 : ~ 2 = 0 .  Proof. auto . Qed. 
  Lemma not_4_eq_0 : ~ 4 = 0 .  Proof. auto . Qed. 
  Lemma not_1_2_eq_2_4 : ~ (mkRat 1 2 not_2_eq_0 = mkRat 2 4 not_4_eq_0 ) . 
  Proof.  injection; intros; discriminate . Qed. 
  
  Theorem falsity : False .  Proof. now apply not_1_2_eq_2_4; apply eq_RatPlus. Qed. 
  
  Definition _1_2 : RatPlus. refine {| top:=1; bottom:=2; bottom_cond:=_ |}. auto. Defined. 

  Reset eq_RatPlus. 
End Rat. 
(* end ex. 6.13 *) 



(* 6.2.5 Guidelines for the "case" tactic *) 



(* caseEq == case_eq *) 
Ltac caseEq f := 
  generalize (refl_equal f); pattern f at -1; case f. 

Print next_month. 

Theorem next_march_shorter :  forall (leap:bool) (m1 m2:month), 
    (next_month m1 = March )-> month_length leap m1 <= month_length leap m2. 
Proof. 
  intros leap m1 m2 H.
  generalize H. 
  case m1; simpl; try discriminate. 
  - intro refl_March. 
    pattern leap.
    apply bool_ind; case m2; simpl; auto.    (* Proof Complete *) 

Restart. 
  
  intros leap m1 m2 H. 
  caseEq m1; try (intros H0; rewrite H0 in H; discriminate H). 
  - intros. 
    pattern leap. 
    apply bool_ind; simpl; pattern m2; apply month_ind; simpl; auto.  
Defined. 

Print next_march_shorter. 

(* 6.3 Recursive Types *) 

(* 6.3.1 Natural Numbers as an Inductive Type *) 

(* 6.3.2 Induction on Nat *) 
Check plus. 
Check plus_O_n. 
Check plus_Sn_m.

Theorem plus_assoc : forall x y z : nat, (x+y)+z = x+(y+z) . 
Proof. 
    intros x y z.
    elim x. 
    - now repeat rewrite plus_O_n. 
    - intros n H.  
      repeat rewrite plus_Sn_m. 
      now rewrite H. 
Qed. 


(* 6.3.3 Recursive Programming *) 
(*  Fixpoint f (n:nat) : T := expr  *) 
Fixpoint mult2 n := 
    match n with 
    | O     => O 
    | S p   => S (S (mult2 p))              end. 


(* ex 6.14 *) 
Fixpoint mult n m {struct n} : nat :=
    match n with 
    | O     => O 
    | S(p)  => plus m (mult p m)            end. 

(* Qestion : How to define the followin OCaml function in Coq ? 
 * OCaml
let mult n m = 
    let plus_m = plus m in 
    let rec loop = function 
        | O     -> O
        | S(p)  -> plus_m (loop p)      *) 

(* Answer : *)
Definition mult' n m := 
  let plus_m := plus m in 
    (fix loop n := match n with 
                   | O    => O 
                   | S p  => plus_m (loop p) end ) n  . 
                          

(* ex. 6.15    *) 
Fixpoint smaller_than_3 (n:nat) : bool := 
    match n-2 with 
    | O     => true
    | _     => false                        end. 
(* := if n < 3 then true else false *)

(* ex. 6.16 *)
Fixpoint plus (n m:nat) { struct m } : nat := 
    match m with 
    | O     => n 
    | S(q)  => S(plus n q)                  end .

(* ex. 6.17 *) 
Fixpoint sum_f (f:nat->Z) (n:nat) : Z := 
    match n with 
    | O     => f O
    | S(i)  => f i + sum_f f i              end. 

(* ex. 6.18 *) 
Fixpoint two_power (n :nat) : nat := 
    match n with 
    | O     => 1
    | S(p)  => mult 2 (two_power p)         end. 

Compute two_power 10. 
(* Compute two_power 16.  (* stack over flow : wat ??? *)  *)
(* end ex. 6.18 *) 




(* 6.3.4 Variations of Constructors *) 
Inductive Z_btree : Set     := 
    | Z_leaf   : Z_btree
    | Z_bnode  : Z -> Z_btree -> Z_btree -> Z_btree. 

Check Z_btree_ind . 
Print positive. 

Fixpoint sum_all_values (t:Z_btree) : Z := 
    (match t with 
    | Z_leaf => 0 
    | Z_bnode v t1 t2 => v + sum_all_values t1 + sum_all_values t2      end)%Z .

Fixpoint zero_present (t:Z_btree) : bool := 
    match t with 
    | Z_leaf                => false
    | Z_bnode (0%Z) t1 t2   => true
    | Z_bnode _ t1 t2       => if zero_present t1 then true else zero_present t2    end.

Fixpoint Psucc (x:positive) :=
    match x with 
    | xI x' => xO (Psucc x') 
    | xO x' => xI x' 
    | xH    => xO xH        end. 

Print Psucc. 


(* ex 6.19 *)
Compute  (xO(xO(xO(xI(xO(xI(xI(xI(xI(xH)))))))))) . 
Compute  (xI(xO(xO(xI(xH))))). 
Compute  (xO(xO(xO(xO(xO(xO(xO(xO(xO(xH)))))))))).


(* ex 6.20 *) 
Definition pos_even_bool (n:positive) : bool := 
    match n with 
    | xO _  => true 
    | _     => false  end. 

Compute pos_even_bool 101%positive. 


(* ex 6.21 *)
Print Z. 
Fixpoint pos_div4 (n:positive) : Z := 
    match n with 
    | xH    => 0%Z
    | xI x  => match x with 
               | xH     => 0%Z
               | xI x'  => Zpos x' 
               | xO x'  => Zpos x' end 
    | xO x  => match x with 
               | xH     => 0%Z
               | xI x'  => Zpos x' 
               | xO x'  => Zpos x' end              end. 

Compute pos_div4 123. 


(* ex. 6.22 *) 
Open Scope positive. 
Definition pos_mult a b : positive := a * b . 
Fixpoint mult_Z (n m:Z) {struct n} : Z := 
    match n with 
    | Z0        =>  Z0 
    | Zpos p    =>  match m with 
                    | Z0     => 0 
                    | Zpos q => Zpos(pos_mult p q)
                    | Zneg q => Zneg(pos_mult p q) end
    | Zneg p    =>  match m with 
                    | Z0     => 0 
                    | Zpos q => Zneg(pos_mult p q)
                    | Zneg q => Zpos(pos_mult p q) end      end. 

Open Scope Z. 
Lemma mult_Z_correct : forall n m, mult_Z n m = n * m . 
Proof. 
    induction n; try trivial; induction m. 
Qed. 


(* ex 6.23 *) 
Inductive L : Prop := L_And     : L -> L -> L   
                    | L_Or      : L -> L -> L 
                    | L_Not     : L -> L 
                    | L_Arr     : L -> L -> L 
                    | L_True    : L 
                    | L_False   : L  . 

(* How to use "/\" ? *)  


(* ex 6.24 *) 
Open Scope positive. 
Inductive positive_rational : Set   :=  One : positive_rational
                                    |   N   : positive_rational -> positive_rational 
                                    |   D   : positive_rational -> positive_rational . 

Fixpoint nom_denom (r : positive_rational) : (positive * positive) := 
        match r with 
        | One   =>  (1,1) 
        | N p   =>  let (n,d) := nom_denom p in (n+d,d) 
        | D p   =>  let (n,d) := nom_denom p in (n,n+d) 
        end. 

Compute nom_denom (D(D(N(N(N(D(One))))))) .  


(* ex 6.25 *) 
Print Zeq_bool  .
Print Z_btree   . 

Fixpoint value_present (n:Z) (bt:Z_btree) :  bool :=  
    match bt with 
    | Z_leaf        =>  false 
    | Z_bnode m l r =>  if Zeq_bool n m then true else 
                        if value_present n l then true else value_present n r   end. 
(* how to prove value_present works well ? *) 


(* ex 6.26 *) 
(* ==> see log.v *) 



(* 6.3.5 ** Types with Functional Fields (pp170) *) 

(* 6.3.5.1 Function Representation of Tree *) 
Inductive Z_fbtree : Set    :=  
    | Z_fleaf :                             Z_fbtree 
    | Z_fnode : Z -> (bool -> Z_fbtree) ->  Z_fbtree . 

Check Z_fbtree_ind. 

Definition right_son (t:Z_btree) : Z_btree := 
    match t with 
    | Z_leaf            => Z_leaf 
    | Z_bnode a t1 t2   => t2                       end. 

Definition fright_son (t:Z_fbtree) : Z_fbtree := 
    match t with 
    | Z_fleaf           => Z_fleaf 
    | Z_fnode _ f       => f false                  end. 

Print Z_fbtree_ind. 

Fixpoint fsum_all_values (t:Z_fbtree) : Z := 
    match t with 
    | Z_fleaf       => 0 
    | Z_fnode a f   => a + fsum_all_values (f true) + fsum_all_values (f false)     end. 


(* ex 6.27 *) 
Fixpoint fzero_present (t:Z_fbtree) : bool := 
    match t with 
    | Z_fleaf       => false
    | Z_fnode 0 _   => true 
    | Z_fnode _ f   => if fzero_present (f true) then true else fzero_present (f false)  end. 



(* 6.3.5.2 *** Infinitely Branching Trees *) 
Inductive Z_inf_branch_tree : Set   
    :=  Z_inf_leaf : Z_inf_branch_tree 
    |   Z_inf_node : Z ->(nat -> Z_inf_branch_tree)-> Z_inf_branch_tree . 

Print sum_f . 

Fixpoint n_sum_all_values (n:nat)(t:Z_inf_branch_tree) {struct t} : Z := 
    match t with 
    | Z_inf_leaf        => 0 
    | Z_inf_node v f    => v + sum_f (fun x:nat=> n_sum_all_values n (f x)) n   end . 


(* ex 6.28 *)
Search ( bool -> bool -> bool ). 
Print andb . 

Fixpoint n_zero_present (n:nat) (t:Z_inf_branch_tree) : bool :=
    match t with 
    | Z_inf_leaf        => false
    | Z_inf_node 0 f    => true
    | Z_inf_node v f    => (fix loop (m:nat) : bool := 
             match m with 
             | O    => false
             | S p  => if n_zero_present m (f m) then true else loop p 
             end ) n                                end. 


(* 6.3.6 Proofs on Recursive Functions *) 
Open Scope nat. 

Theorem plus_assoc' : forall x y z : nat, x + y + z = x + (y + z) . 
Proof. induction x; simpl; auto.  Qed. 

Print plus_assoc' .
Print eq_ind. 
Print eq_ind_r. 

(* ex 6.29 *) 
Theorem plus_n_O : forall n : nat, n = n + 0 . 
Proof.  now induction n.  Qed. 
Print plus_n_O .

(* ex. 6.30 *) 
Print Z_btree.
Print Z_fbtree. 

Fixpoint f1 (t:Z_btree) : Z_fbtree :=
    match t with 
    | Z_leaf        => Z_fleaf 
    | Z_bnode v l r => Z_fnode v (fun x=>if x then f1 l else f1 r)  end. 

Fixpoint f2 (t:Z_fbtree) : Z_btree := 
    match t with 
    | Z_fleaf       => Z_leaf 
    | Z_fnode v f   => Z_bnode v (f2(f true)) (f2(f false))         end. 

Require Import FunctionalExtensionality. 
Lemma f2_eq_f1 : (forall t , f2(f1 t) = t )/\ forall t, f1(f2 t) = t . 
Proof. 
    split; induction t; simpl; auto. 
    - now rewrite IHt1, IHt2. 
    - repeat rewrite H. 
      pattern (Z_fnode z) .   
      (* needs function extentionality *) 
      Check functional_extensionality. 
      apply functional_extensionality in H. 
      rewrite <- H.  
      cut ((fun x:bool => if x then f1(f2(z0 true)) else f1(f2(z0 false))) 
        = (fun x:bool => f1(f2(z0 x)))). 
      intros Hr. now rewrite <- Hr. 
      apply functional_extensionality. 
      intros. now case x.  
Qed. 


(* ex 6.31 *) 
Lemma mult2n_n_plus_n : forall n : nat, (mult2 n) = n + n . 
Proof. 
    induction n; simpl.
    - trivial.  
    - Search S (_ + _) . 
      now rewrite IHn, plus_n_Sm. 
Qed. 


(* ex 6.32 *) 
Fixpoint sum_n (n:nat) : nat := 
    match n with 
    | O     => O 
    | S p   => S p + sum_n p                end. 

Lemma sum_succ : forall n , sum_n (S n) = S n + sum_n n  . 
Proof.  now induction n . Qed. 

Lemma sum_solve : forall n:nat, 2 * sum_n n = n*(n + 1). 
Proof. 
    simpl. intros n.  rewrite <-(plus_n_O (sum_n n)). 
    induction n; try trivial. (* omega or lia *) 
    rewrite sum_succ, <- plus_assoc.  
    rewrite (plus_comm (S n)(sum_n n)), (plus_comm (sum_n n + S n + S n)(sum_n n)). 
    rewrite <- plus_assoc, <- plus_assoc, IHn. 
    ring. 
Qed. 


(* ex 6.33 *) 
Theorem n_le_sum_n : forall n:nat, n <= sum_n n . 
Proof.
    induction n; try trivial . 
    - Search (_<=_ -> _<=_+_). 
      rewrite sum_succ, (plus_n_O (S n)) at 1. 
      apply plus_le_compat_l. 
      Search (_<=_ -> _<=_ -> _<=_) . 
      apply (le_trans 0 n _); [now apply le_0_n | trivial] . 
Qed.

Check nat_ind. 
Check nat_rect. 



(* 6.4 Polymorphic Types *) 


(* 6.4.1 Polymorphic Lists *) 
Require Import List. 
Import ListNotations. 
Print List. 
Print list. 

(* ex 6.34 *) 
Definition take2 {A:Type} (l:list A) := 
    match l with 
    | a::b::_       => [a;b]
    | _             =>    []   end . 

Compute take2 (1 :: 2 :: 3 :: nil). 

(* ex 6.35 *) 
Fixpoint take (n:nat) {A:Type} (l:list A) {struct n} : list A :=
    match n, l with 
    | S p, a::tl    => a::take p tl
    | _, _          => []                  end. 

Compute take 4 (1:: 3 ::5 ::5:: 7:: 10:: nil). 
Compute take 0 (cons 1 nil)  . 

(* ex 6.36 *) 
Open Scope Z.  
Definition sum_list (l:list Z) : Z := fold_left (fun n m => n+m) l 0 . 
Compute sum_list (1 ::3 :: 5 :: 10:: nil) . 

(* ex 6.37      :=  fold_(λX.X+1) *) 
Open Scope nat. 
Fixpoint fold_nat (n:nat) {A:Type} (succ:A->A) (zero:A) : A := 
    match n with 
    | O     => zero 
    | S p   => succ (fold_nat p succ zero)      end. 

Definition n_occurance_of_1 (n:nat) : list nat := fold_nat n (cons 1) nil . 

(* ex 6.38      :=  polymorphic recursive fold_(λX.X+1) *) 
Fixpoint fold_nat_poly (n:nat) {A:Type} (psucc:nat->A->A) (zero:A) : A := 
    match n with 
    | O     => zero 
    | S p   => (psucc p) (fold_nat_poly p psucc zero)  end. 

Definition one_to_n (n:nat) := map S (rev (fold_nat_poly n cons nil ) ). 
Compute one_to_n 10. 


(* 6.4.2 "option" type *) 
Definition pred_option (n:nat) : option nat :=
    match n with 
    | O         => None
    | S p       => Some p           end. 

Definition pred2_option (n:nat) : option nat := 
    match pred_option n with
    | None      => None 
    | Some p    => pred_option p    end. 

Fixpoint nth_option {A:Set} (n:nat)(l:list A){struct l} : option A :=
    match n,l with 
    | O, cons a tl      => Some a
    | S p, cons a tl    => nth_option p tl
    | _,nil             => None     end. 


(* ex 6.39 *)
Fixpoint nth_option' {A:Set} (n:nat)(l:list A){struct n} : option A :=
    match n,l with 
    | O, cons a tl      => Some a
    | S p, cons a tl    => nth_option p tl
    | _,nil             => None     end. 

Theorem nth_eq_nth' : forall (n:nat) (A:Set) (l:list A), nth_option n l = nth_option' n l . 
Proof. now induction n; induction l. Qed. 


(* ex. 6.40 *)
Open Scope nat_scope.
Lemma ex_6_40 : forall (A:Set) (n:nat) (l:list A), nth_option n l = None -> length l <= n . 
Proof. induction n; induction l; simpl; try discriminate; auto with arith.  Qed.


(* ex 6.41 The answer is filter' and not filter *) 
Fixpoint filter {A:Set} (f:A->bool) (l:list A) := 
    match l with 
    | nil       => []  
    | a::tl     => if f a then a::filter f tl else filter f tl  end. 
Reset filter. 

Definition filter {A} (P:A->bool) l := 
    fold_right(fun x xs=>if P x then x::xs else xs)[] l. 

Definition is_4 n :=
    match n with 
    | S(S(S(S(O)))) => true
    | _             => false                                end.

Fixpoint isEven n := 
    match n with 
    | O       => true 
    | S(S(p)) => isEven p
    | _       => false    end.  

Compute filter is_4 (1 :: 2 :: 3 :: 5 :: nil) . 
Compute filter is_4 (1 :: 2 :: 4 :: 5 :: nil) . 

Definition some {A:Set} (f:A->bool)(a b:option A) := 
    match a,b with 
    | None    ,_    => b 
    | Some a' ,_    => if f a' then a else b                end. 

Definition filter' {A:Set} f l := fold_right (A:=option A) (some f)None(map Some l). 

Compute filter' is_4 (1 :: 9 :: 2 :: 3 :: 5 :: 100 :: nil) . 
Compute filter' isEven (1 :: 2 :: 4 :: 5 :: nil) . 
Compute filter isEven (1 :: 2 :: 4 :: 5 :: nil) . 
(* end ex. 6.41 *)



(* 6.4.3 The Type of Pairs *) 

Print prod. 
Print fst. 
Print snd. 

(* ex. 6.42 *) 
Check prod. 

Fixpoint split {A B} (l: list (A*B)) := 
    match l with 
    | []            => ([],[])  
    | (a,b)::rest   => (a::fst(split rest),b::snd(split rest))   end. 

Fixpoint combine {A B} (l: list A) (k: list B) := 
    match (l,k) with 
    | (a::l',b::k') => (a,b) :: combine l' k'   
    | _             => []                      end. 

Theorem combine_split_eqv : 
  forall A B (l: list (A*B)), combine (fst(split l))(snd(split l)) = l . 
Proof. 
  induction l; auto. 
  - case a; simpl. now rewrite IHl.    
Qed. 


(* ex 6.43 *)
Open Scope Z. 
Print Z_btree. 
Inductive btree (A:Set) := 
    | leaf     : btree A
    | node     : A -> btree A -> btree A -> btree A. 

Check btree_rec. 

Fixpoint btree_Z_to_Z_btree (t : btree Z) := 
    match t with 
    | leaf _            => Z_leaf
    | node _ v l r      => Z_bnode v (btree_Z_to_Z_btree l) (btree_Z_to_Z_btree r)  end . 

Fixpoint Z_btree_to_btree_Z (t : Z_btree) : btree Z :=
    match t with
    | Z_leaf            => leaf Z
    | Z_bnode v l r     => node Z v (Z_btree_to_btree_Z l) (Z_btree_to_btree_Z r)   end. 

Theorem btZ2btZ_eqv : forall (t:btree Z), Z_btree_to_btree_Z (btree_Z_to_Z_btree t) = t . 
Proof. induction t; simpl; now try rewrite IHt1, IHt2. Qed. 

Theorem Zbt2Zbt_eqv : forall (t:Z_btree), btree_Z_to_Z_btree (Z_btree_to_btree_Z t) = t . 
Proof. induction t; simpl; now try rewrite IHt1, IHt2. Qed. 

Definition btz2zbt := 
  btree_rec _ (fun t=>Z_btree) Z_leaf (fun z _ l _ r => Z_bnode z l r) .  
Print btz2zbt. 

Goal forall (b: btree Z) , btz2zbt b = btree_Z_to_Z_btree b.  
Proof.  now induction b.  Qed. 
(* end ex. 6.43 *) 


(* ex. 6.44 *) 
(* ==> see ex. 6.24 *) 

(* ex. 6.45 *)
(* ==> see prime.v *) 






(* 6.4.4 Sum *) 
Open Scope nat. 
Print sum . 
Check (sum nat bool) . 
Check (inl bool 4). 
Check (inr nat false). 


(* .6.5 * Dependent Inductive Type *) 
(* First Order Data *) 
Inductive ltree (n:nat) : Set := 
    | lleaf : ltree n 
    | lnode : forall p:nat, p<=n -> ltree n -> ltree n -> ltree n . 

Inductive sqrt_data (n:nat) : Set := 
    sqrt_intro : forall x:nat, x*x<=n -> n<(S x)*(S x) -> sqrt_data n. 

Check (sqrt_data 4) .
Lemma sq2 : 2*2 <= 4 . Proof. omega. Defined. 
Lemma sq3 : 4 <  3*3 . Proof. omega. Defined. 
Check (sqrt_intro 4 2 sq2 sq3). 

(* Variably Dependent Inductive Type *)
Inductive htree (A:Set) : nat -> Set := 
    | hleaf : A -> htree A O
    | hnode : forall n:nat, A -> htree A n -> htree A n -> htree A (S n). 

Check htree_ind. 

Fixpoint htree_to_Z_btree (n:nat)(t:htree Z n){struct t} : Z_btree :=
    match t with 
    | hleaf _ z         => Z_bnode z Z_leaf Z_leaf 
    | hnode _ p v l r   => Z_bnode v (htree_to_Z_btree p l)(htree_to_Z_btree p r)
    end. 

Fixpoint invert (A:Set) (n:nat) (t:htree A n) {struct t} : htree A n := 
    match t in htree _ v return htree A v with 
    | hleaf _ v         => hleaf A v 
    | hnode _ p v l r   => hnode A p v (invert A p r) (invert A p l) 
    end. 


(* ex 6.46 *) 
Definition hleft (n:nat) (t:htree nat (S n)) : htree nat n := 
    match t with 
    | hnode _ p v l r => l 
    end. 

Goal forall n(t1 t2 t3 t4:htree nat n),  hnode nat n O t1 t2 = hnode nat n O t3 t4 -> t1 = t3 . 
Proof. 
    intros n t1 t2 t3 t4 H. 
    change (hleft n (hnode nat n 0 t1 t2) = hleft n (hnode nat n 0 t3 t4)). 
    now rewrite H. 
Qed. 


(* ex 6.47 *) 
Fixpoint height_htree (n:nat) := 
    match n with 
    | O     => hleaf Z (0%Z)
    | S p   => hnode Z p (Z_of_nat p) (height_htree p)(height_htree p) 
    end. 

Compute height_htree 4. 


(* ex 6.48 *) 
Inductive binary_word : nat -> Set := 
    | bnil  : binary_word 0 
    | bcons : forall n:nat, bool -> binary_word n -> binary_word (S n).  

Fixpoint binary_word_concat n m (bn:binary_word n)(bm:binary_word m): binary_word (n+m) :=
    match bn with 
    | bnil          => bm 
    | bcons p b bp  => bcons (p+m) b (binary_word_concat p m bp bm) 
    end. 

(* ex 6.49 *) 
Fixpoint binary_word_or (n:nat) (w1 w2:binary_word n) : binary_word n. 
Proof. 
  induction w1. 
  - exact w2. 
  - inversion w2. exact (bcons n (orb b H0) (binary_word_or n w1 H1)). 
Defined. 
Print binary_word_or. 

Compute binary_word_or _
  (bcons _ true  (bcons _ false (bcons _ false bnil))) 
  (bcons _ false (bcons _ true  (bcons _ false bnil))) . 


(* ex 6.50 *) 
Fixpoint ty_bool_nat (n:nat) : Set := 
    match n with 
    | O         => nat
    | 1         => bool
    | S(S p)    => ty_bool_nat p                end. 

Fixpoint fun_bool_nat (n:nat) : ty_bool_nat n :=  
    match n with 
    | O         => O 
    | 1         => true
    | S (S p)   => (fix g (n:nat) : ty_bool_nat n -> ty_bool_nat n :=
                    match n return ty_bool_nat n -> ty_bool_nat n with 
                    | O         => S
                    | 1         => negb
                    | S (S p)   => g p
                    end ) p (fun_bool_nat p)    end. 


Check Empty_set. 

Inductive strange : Set := cs : strange -> strange . 

Theorem strange_empty : forall x : strange, False. 
Proof. 
    intros x; elim x. 
    exact (fun _ fls => fls) . 
    (* induction x with P := (fun _ => False) .  *) 
Qed. 


(* ex 6.51 *) 

Goal forall x y:Empty_set,  x = y.      Proof. induction x.  Qed. 
Goal forall x y:Empty_set, ~x = y.      Proof. induction y.  Qed. 


Inductive even_line : nat -> Set := 
  | even_empty_line : even_line O
  | even_step_line : forall n:nat, even_line n -> even_line (S (S n)). 

Check even_line 1.  
Goal forall x:even_line 1, False.       Proof. inversion 1. Qed.  


