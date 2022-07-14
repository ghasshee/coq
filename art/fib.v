(* Fibonacci sequence *) 

(* ex.  9.8   *) 
(* ex.  9.10  *) 
(* ex.  9.17  *) 


Require Import ZArith. 
Require Import CoqArt.chap09. 
Set Implicit Arguments. 





(* ex. 9.8 *) 
Open Scope nat. 
Fixpoint fib (n:nat) : nat := 
    match n with 
    | S (S q as p)  => fib q + fib p 
    | _             => 1            end. 

Fixpoint fib' (n:nat) : nat * nat := 
    match n with 
    | O         =>  (1,1) 
    | S p       =>  let (u1,u2) := fib' p in 
                    (u2, u1+u2)     end. 
Compute fib  10. 
Compute fib' 10.

Theorem fib_fib'_aux : forall n, (fib n, fib (S n)) = fib' n .
Proof. 
    induction n using nat_2_ind; intuition. 
    - simpl fib'. now rewrite <- IHn. 
Qed.  

Theorem fib_fib' : forall n, fib n = fst (fib' n) . 
Proof. intros. rewrite <- fib_fib'_aux; intuition. Qed. 





(* ex. 9.10 *) 
Opaque fib. 
Lemma fib0 : fib 0 = 1. intuition. Qed. 
Lemma fib1 : fib 1 = 1. intuition. Qed. 
Theorem fib_eq : forall n, fib(S(S n)) = fib n + fib(S n). induction n; intuition. Qed.  

Hint Resolve fib0 fib1 fib_eq : fib. 

Theorem nat_1_2_ind : forall P : nat -> Prop, 
    P 0 -> P 1 -> (forall n, P n -> P(S n) -> P(S(S n))) -> forall n, P n. 
Proof. intros. cut (P n /\ P(S n)); try tauto. induction n;intuition. Qed. 

Require Import Lia. 
Theorem fib_lemma'   : forall n p, fib(2+n+p) = fib(1+n) * fib(1+p) + fib n * fib p . 
Proof. 
    simpl. induction n using nat_1_2_ind; intro p. 
    - Transparent fib. simpl. lia.   
    - Transparent fib. simpl. lia. 
    - Opaque fib. simpl. simpl in IHn0.  
      rewrite fib_eq, IHn, IHn0. repeat rewrite fib_eq.    
      lia.  
Qed. 
Theorem fib_lemma : forall n p, fib(n+p+2) = (fib(n+1)) * (fib(p+1)) + (fib n)*(fib p) . 
Proof. 
    intros n p. 
    cutrewrite (n+p+2=2+n+p); [| lia ].  
    cutrewrite (n+1  =1+n  ); [| lia ]. 
    cutrewrite (p+1  =1+p  ); [| lia ]. 
    apply fib_lemma'.    
Qed. 

Lemma quad_a_b : forall a b:nat, (a+b)*(a+b) = a*a + b*b + 2*a*b. 
Proof. lia. Qed.  
Lemma distrib_r : forall a b c, (a+b)*c = a*c + b*c . Proof. lia. Qed. 
Lemma distrib_l : forall c a b, c*(a+b) = c*a + c*b . Proof. lia. Qed. 
Lemma plus_0 : forall a:nat, a+0 = a.                 Proof. lia. Qed. 
Lemma mult_2 : forall a:nat, a+a = 2*a.               Proof. lia. Qed. 
Lemma plus_comm : forall n m:nat, n+m = m+n.          Proof. lia. Qed. 

Hint Resolve 
    quad_a_b plus_0 mult_2 distrib_r distrib_l : fib. 


Opaque fib. 

Theorem fib_lemma_2n : forall n , 
  fib (2*n) = 2 * fib n * fib n + fib(n+1)*fib(n+1) - 2 * fib n * fib(n+1).
Proof.
  induction n. 
  - now simpl. 
  - set (fib_lemma n n).  
    simpl in e.   
    cutrewrite (2*S n= n+n+2); [| lia ].
    cutrewrite (fib(S n+1) = fib n + fib (S n)); [| rewrite <- fib_eq, plus_comm; auto ]. 
    rewrite e. simpl.    
    cutrewrite ((fib n + fib(S n))*(fib n + fib(S n)) 
    = fib n*fib n + fib(S n)*fib(S n) + 2 * fib n * fib(S n)); [| now rewrite quad_a_b]. 
    simpl. eauto with arith.   
    repeat rewrite plus_0. 
    cutrewrite (n+1 = S n); [| lia ].  
    repeat rewrite mult_2. 
    cutrewrite (2*fib(S n)*(fib n + fib(S n)) = 2*fib(S n)*fib(S n) + 2*fib n * fib(S n)); [| lia]. 
    lia. 
Qed. 




(* ex 9.15 *)
(* tail-recursive fibonacci *) 
Fixpoint fib''_aux n a b := 
    match n with 
    | O         => a 
    | S p       => fib''_aux p b (a+b) end.  

Definition fib'' n := fib''_aux n 1 1 . 

Compute fib'' 10. 




(* ex. 9.17 *) 
Open Scope nat. 

Fixpoint fib_bin_aux (n:positive) : nat * nat := 
    match n with 
    | xH    =>  (1,2) 
    | xO n' =>  let (un,un1) := fib_bin_aux n' in 
                (un1*un1 - 2*un1*un + 2*un*un, 2*un1*un - un*un)
    | xI n' =>  let (un,un1) := fib_bin_aux n' in 
                (2*un1*un - un*un, un1*un1 + un*un) end . 

Definition fib_bin (n:positive) := fst (fib_bin_aux n) . 
Compute fib_bin 10.          


Check Pos2Nat.inj_xI. 
Check Pos2Nat.inj_xO. 
Print Pos.to_nat. 
Print Pos.iter_op. 

Theorem fib_bin_eq : forall n, fib_bin (n+2) = fib_bin n + fib_bin (n+1). 
Proof. 
    induction n using positive_2_ind; intuition . 

Search (nat -> positive). 
Abort. 

Definition fib_bin_spec : forall n, { u:nat & { u':nat | u = fib n /\ u' = fib (n+1) }} . 
    intros. 
    exists (fib_bin (Pos.of_nat n)). 
    exists (fib_bin (Pos.of_nat (n+1))). 
    split; induction n using nat_1_2_ind; intuition.  
    - rewrite fib_eq. rewrite <- IHn, <- IHn0. 
Abort. 

Check Z.of_nat. 
Check Z.to_nat. 

