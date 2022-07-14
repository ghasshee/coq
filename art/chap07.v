(* chapter 7. Tactics and Automation *) 



(* 7.1  Reduction        *) 
Require Import Arith. 
Require Import Lia. 

Theorem le_plus_minus' : forall n m : nat, m <= n -> n = m+(n-m) .
Proof. 
  induction n. 
  - intros. now rewrite <- (le_n_0_eq m).  
  - auto with arith.    
Qed. 

Theorem simpl_pattern_example : 3 * 3 + 3 * 3 = 18 . 
Proof. 
    simpl (3*3) at 2. 
    Show 1. 
    cbv beta iota zeta delta [mult] .
Abort. 

Theorem lazy_example : forall n : nat, (S n)  + 0 = S n .
Proof. 
    intros n.
    lazy beta iota zeta delta.  
    fold plus. 
Abort. 


(* 7.2  Auto Database *) 

(* 7.2.1 Hint *)

Hint Extern 4 (_ <> _) => discriminate : core. 
Hint Resolve le_S_n : le_base . 

Goal forall n m: nat , S(S(S n)) <= S(S(S m)) -> n <= m . 
Proof. intros n m H; auto with le_base.  Qed. 


(* 7.2.2 "eauto" tactic *) 





(* 7.3 Auto Rewrite *) 

(* 7.3.1 "autorewrite" tactic *)
Section combinatory_logic . 
    Variables (CL:Set)(App:CL->CL->CL)(S:CL)(K:CL). 
    Hypotheses
        (S_rule : forall A B C:CL, App (App (App S A)B)C = App(App A C)(App B  C))
        (K_rule : forall A B  :CL, App (App K A) B = A). 

    Hint Rewrite S_rule K_rule : CL_rules. 
    Hint Rewrite <- S_rule K_rule : CL_rules2 . 

    Theorem I'_rule : forall A:CL, App (App (App S K)K)A = A . 
    Proof. 
        intros. now autorewrite with CL_rules . 
    Defined. 

    Theorem I''_rule : forall A:CL, App (App (App S K)S)A = A . 
    Proof. 
        intros. now autorewrite with CL_rules . 
    Defined. 

    Definition I'_eq_I''_rule := fun A => eq_trans (I'_rule A) (eq_sym(I''_rule A)) . 

    Check I'_eq_I''_rule .

    Theorem I_rule : forall {X:CL} (A:CL), App (App (App S K) X) A = A . 
    Proof. 
        intros. now autorewrite with CL_rules. 
    Defined. 

    Definition I'_eq_I_rule := 
        fun X A => eq_trans (I'_rule A) (eq_sym (I_rule A : App(App(App S K)X)A = A))  . 
    Check I'_eq_I_rule . 
End combinatory_logic. 


(* 7.3.2  "subst" tactic *) 
Open Scope nat. 
Theorem example_for_subst :  forall a b c d, a = b+c -> c = 1 -> a+b = d -> 2*a = d+c. 
Proof. 
    intros a b c d H H1 H2. 
    subst a c d. 
    ring.  
Qed. 






(* 7.4 Numerical Tactics *)

Require Import Arith ZArith Omega. 
Open Scope Z_scope .

(* 7.4.1    "ring" tactic *) 
Definition square (z:Z) := z*z. 
Theorem ring_eg2 : forall x y : Z, square (x+y) = square x + 2*x*y + square y.  
Proof. intros x y; unfold square; ring. Qed.    

(* 7.4.2    "omega" tactic *) 
Theorem omega_eg3 : forall x y:Z, 0 <= x*x -> 3*(x*x) <= 2*y -> x*x <= y . 
Proof.  intros x y H H0; omega. Qed. 
Theorem omega_eg4 : forall x y:Z, 0 <= x*x -> 3*x*x <= 2*y -> x*x <= y . 
Proof. intros x y H H0. (* omega cannot solve this *)   lia.  Qed.  

(* 7.4.3    "field" tactic *) 
Require Import Reals. 
Open Scope R_scope. 

Theorem eg_for_field : forall x y : R, y <> 0 -> (x+y)/y = 1 +(x/y) . 
Proof. intros x y H; now field.  Qed. 

(* 7.4.4    "fourier" tactic *) 





(* 7.5 Other Decision Procedures *) 

(* 7.5.1    "tauto" tactic *) 
Goal forall A B:Prop, A /\ B -> A .
Proof .  tauto.     Qed. 

(* 7.5.2    "intuition" tactic *) 
Open Scope nat_scope. 
Theorem ex_intuition : forall n p q:nat, n <= p \/ n <= q -> n <= p \/ n <= S q . 
Proof. 
    intros n p q; intuition auto with arith. 
Qed. 




(* 7.6 Ltac *) 
(* ==> see ltac.v *) 


