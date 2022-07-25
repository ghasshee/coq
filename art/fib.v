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
Proof. induction n using nat_2_ind; simpl; try rewrite <- IHn; reflexivity. Qed.  

Theorem fib_fib' : forall n, fib n = fst (fib' n) . 
Proof. intros; rewrite <- fib_fib'_aux; reflexivity. Qed. 





(* ex. 9.10 *) 
Opaque fib. 
Theorem fib0    :           fib 0       = 1 .               Proof. intuition. Qed. 
Theorem fib1    :           fib 1       = 1 .               Proof. intuition. Qed. 
Theorem fib_eq  : forall n, fib(S(S n)) = fib n + fib(S n). Proof. intuition. Qed.  

Hint Rewrite fib0 fib1 fib_eq : fib. 

Theorem nat_1_2_ind : forall P : nat -> Prop, 
    P 0 -> P 1 -> (forall n, P n -> P(S n) -> P(S(S n))) -> forall n, P n. 
Proof. intros. cut(P n /\ P(S n)); try induction n; intuition. Qed. 

Require Import Lia. 
Theorem fib_lemma'   : forall n p, fib(2+n+p) = fib(1+n) * fib(1+p) + fib n * fib p . 
Proof. 
    simpl. induction n using nat_1_2_ind; intro p. 
    - Transparent fib. simpl. lia.   
    - Transparent fib. simpl. lia. 
    - Opaque fib. simpl in *.  
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



(* ex 9.15 *)
(* tail-recursive fibonacci *) 
Fixpoint fib''_aux n a b := 
    match n with 
    | O         => a 
    | S p       => fib''_aux p b (a+b) end.  

Definition fib'' n := fib''_aux n 1 1 . 

Compute fib'' 5. 




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


Check Pos2Nat.inj_xI. 
Check Pos2Nat.inj_xO. 
Print Pos.to_nat. 
Print Pos.of_nat. 
Print nat_of_P. 


Let comm := Nat.add_comm. 

Theorem fib_lemma_2n : forall n , 
  fib (2*n) = 2*fib n*fib n + fib(n+1)*fib(n+1) - 2*fib n*fib(n+1).
Proof.
  destruct n. 
  - reflexivity. 
  - cutrewrite ( 2*S n = n+n+2 ); 
    [ rewrite(fib_lemma n n),(comm _ 1),(comm _ 1); simpl;  rewrite fib_eq | ]; 
    auto with zarith.   
Qed. 

Theorem fib_lemma_2n_1 : forall n, 
  fib (2*n+1) = 2*fib(n+1)*fib n - fib n*fib n. 
Proof. 
  destruct n. 
  - reflexivity. 
  - cutrewrite (2*S n+1 = S n+n+2); 
    [ rewrite(fib_lemma(S n)n),(comm _ 1),(comm _ 1); simpl;  rewrite fib_eq | ]; 
    auto with zarith.  
Qed. 

Theorem fib_lemma_2n_2 : forall n, 
  fib (2*n+2) = fib(n+1)*fib(n+1) + fib n*fib n. 
Proof. 
  intros n; cutrewrite(2*n+2=n+n+2); try rewrite(fib_lemma n n); auto with zarith. 
Qed. 


Compute fib 1. 
Compute fib 2. 

Definition fib_bin_spec : forall p:positive, 
  { u:nat & { v:nat | u = fib(nat_of_P p) /\ v = fib(nat_of_P p + 1) }}. 
Proof. 
  refine (fix fib_bin p := match p with 
                           | xI p => match fib_bin p with 
                                     | existT _ u (exist _ v _) => _ end
                           | xO p => match fib_bin p with 
                                     | existT _ u (exist _ v _) => _ end
                           | xH   => _ end). 
  - exists (2*u*v - u*u), (v*v + u*u). 
    subst; split.  
    + cutrewrite (Pos.to_nat p~1 = 2*nat_of_P p + 1);
      [ rewrite fib_lemma_2n_1 |]; auto with zarith. 
    + cutrewrite (Pos.to_nat p~1+1 = 2*Pos.to_nat p + 2);  
      [ rewrite fib_lemma_2n_2 |]; auto with zarith. 
  - exists (2*u*u+v*v-2*u*v), (2*u*v-u*u). 
    subst; split.  
    + cutrewrite (Pos.to_nat p~0 = 2*nat_of_P p); 
      [ rewrite fib_lemma_2n |];  auto with zarith.      
    + cutrewrite (Pos.to_nat p~0+1 = 2*Pos.to_nat p+1); 
      [ rewrite fib_lemma_2n_1 |]; auto with zarith. 
  - Transparent fib. compute.  
    exists 1,2.   
    split; reflexivity. 
Defined. 
    
Compute 
  match fib_bin_spec 21 with 
  | existT _ u (exist _ v _ ) => (u,v) end. 
        

    

Check Z.of_nat. 
Check Z.to_nat. 

