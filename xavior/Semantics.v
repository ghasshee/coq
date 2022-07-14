Require Import String. 
Require Import List. 
Require Import Sequences.


Open Scope string_scope. 
Open Scope list_scope. 



(* AST *)

Definition var : Type := string. 
Definition var_eq : forall (v1 v2:var), {v1 = v2} + {v1 <> v2} := string_dec. 

Definition const : Type := nat. 

Inductive term : Type :=
  | Var : var -> term 
  | Const : const -> term 
  | Fun : var -> term -> term 
  | App : term -> term -> term . 


Fixpoint subst (x:var) (b a:term) {struct a} : term :=
  match a with 
  | Var y     => if var_eq x y then b else Var y
  | Const n   => Const n
  | Fun y t   => Fun y (if var_eq x y then t else subst x b t)
  | App t1 t2 => App (subst x b t1) (subst x b t2) end . 


Inductive isvalue : term -> Prop :=
  | isvalue_const : forall c  , isvalue (Const c)
  | isvalue_fun   : forall x a, isvalue (Fun x a).

Hint Constructors isvalue : sem. 


(* Reduction : Small Step *) 

Inductive red : term -> term -> Prop := 
  | red_beta  : forall x a v, isvalue v -> red (App (Fun x a) v) (subst x v a)
  | red_app_l : forall t t' b, red t t' -> red (App t b) (App t' b)
  | red_app_r : forall v t t', isvalue v -> red t t' -> red (App v t)(App v t'). 

Hint Constructors red : sem. 





Lemma value_irred : forall v, isvalue v -> irred red v.  
Proof. intros. inversion H; intros b Hred; inversion Hred.  Qed. 


Lemma red_deterministic : forall a b c, red a b -> red a c -> b = c. 
Proof. 
  intros a b c H; revert a b H c. 
  induction 1; intros c Hred; inversion Hred; subst.    
  + reflexivity.   
  + inversion H3.     
  + elim (value_irred v H _ H4).     
  + inversion H.  
  + f_equal; auto.   
  + elim (value_irred t H2 t' H ).  
  + elim (value_irred t H4 t' H0).    
  + elim (value_irred v H t'0 H4).  
  + destruct (IHred t'0 H5); now subst.  
Qed. 



Definition terminates t v := star red t v /\ isvalue v. 

Definition diverges t     := infseq red t.  

Definition goes_wrong t   := exists w, star red t w /\ irred red w /\ ~ isvalue w. 



(* Natural semantics == Big Step *) 

Inductive eval : term -> term -> Prop :=
  | eval_const : forall c, eval (Const c) (Const c)
  | eval_fun   : forall x a, eval (Fun x a) (Fun x a)
  | eval_app   : forall t t' x e v v',
      eval t (Fun x e) -> 
      eval t' v'       -> 
      eval (subst x v' e) v -> 
      eval (App t t')     v. 

Lemma eval_isvalue : forall t t', eval t t' -> isvalue t'. 
Proof. intros. induction H; auto with sem. Qed.  









