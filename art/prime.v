Require Import Lia List Sumbool Arith. 
Import ListNotations. 
Open Scope nat. 


(* ex 6.45 ***difficulut   *) 
Notation " n <-? l "  := (in_dec Nat.eq_dec n l) (at level 50).  
Notation to_bool dec  := (proj1_sig (bool_of_sumbool dec)). 
Notation "x <- l"     := (List.In x l) (at level 50).  
Notation " x `c` y"   := (List.incl x y) (at level 50).  
Check incl. 


Inductive cmp : Set :=  Less    : cmp
                    |   Equal   : cmp 
                    |   Greater : cmp . 

Fixpoint compare (n m :nat) : cmp :=
    match (n,m) with 
    | (O,O)             => Equal
    | (O,_)             => Less
    | (_,O)             => Greater 
    | (S p, S q)        => compare p q        end. 

Lemma cmp_lt : forall n m, compare n m = Less -> n < m . 
Proof. induction n; destruct m; simpl; try now inversion 1; auto with arith. Qed. 
Lemma lt_cmp : forall n m, n < m -> compare n m = Less.  
Proof. induction n; destruct m; simpl; try now inversion 1; auto with arith. Qed. 
Lemma cmp_eq : forall n m, compare n m = Equal -> n = m . 
Proof. induction n; destruct m; simpl; try now inversion 1; auto with arith. Qed. 
Lemma eq_cmp : forall n m, n = m -> compare n m = Equal. 
Proof. intros. rewrite H. clear n H. now induction m. Qed.   
Lemma cmp_gt : forall n m, n > m -> compare n m = Greater. 
Proof. induction n; destruct m; simpl; try now inversion 1. auto with arith. Qed. 
Lemma gt_cmp : forall n m, compare n m = Greater -> n > m. 
Proof. induction n; destruct m; simpl; try now inversion 1; auto with arith. Qed. 

Theorem list_map_pushforward : forall {A B} P (Q:B->Prop) (f:A->B) l, 
  Forall P l -> (forall x:A, P x -> Q (f x)) -> Forall Q (map f l).  
Proof. 
  intros. 
  Check Forall_forall. 
  rewrite Forall_forall in *|-*. 
  intros y Hin.  
  rewrite in_map_iff in Hin. 
  destruct Hin as [x [fx_y Hin_x] ]. 
  rewrite <- fx_y. intuition. 
Qed. 

Fixpoint elem a l : bool := 
    match l with 
    | x::xs     =>  orb (Nat.eqb a x) (elem a xs) 
    | []        =>  false                     end. 

Definition update_prime k '(p,m) := 
  match compare k m with 
  | Less    => (p,m)
  | _       => (p,m+p) end. 

Definition sieve_pair k  '(p,m) := 
  1 < p < k /\ exists i, 1 < i /\  m = p*i /\ p*(i-1) < k <= p*i .    

Lemma sieve_pair_update : forall k p m, 
  sieve_pair k  (p,m) ->  sieve_pair (S k) (update_prime k (p,m)) . 
Proof. 
  intros. 
  destruct H as [Hcomp [i [Hi [Heq Hle]]]].    
  cut (k <= m); try lia; intros le.     
  destruct (le_lt_eq_dec k m le); unfold update_prime.  
  - (* k < m *) 
    rewrite lt_cmp; auto. 
    + simpl. split; try lia. 
      exists i; lia.     
  - (* k = m *) 
    rewrite eq_cmp; auto.  
    + simpl. split; try lia. 
      exists (S i); lia. 
Qed. 

Definition update_primes k (sieve:list(nat*nat)) :=
  (map (update_prime k) sieve, to_bool( k <-? map snd sieve )). 

Definition sieve_pairs k sieve := Forall (sieve_pair k) sieve . 


Lemma sieve_pairs_update : forall k sieve sieve' notprime, 
  sieve_pairs k sieve -> (sieve', notprime) = update_primes k sieve -> 

  sieve_pairs (S k) sieve'. 
Proof. 
  unfold sieve_pairs, update_primes.
  intros. injection H0. intros. subst. clear H0. 
  Check list_map_pushforward. 
  eapply list_map_pushforward; eauto. 
  intros [p m]. apply sieve_pair_update.  
Qed. 

Fixpoint prime_sieve (n:nat) : list (nat*nat) := 
    match n with 
    | S(S q as p) =>  let (sieve,not_prime) := update_primes n(prime_sieve p) in 
                      if not_prime then sieve else (n,n+n)::sieve   
    | _           =>  []                                              end. 

Lemma sieve_pairs_prime_sieve : forall n, sieve_pairs (S n) (prime_sieve n). 
Proof. 
  induction n as [| k].  
  - constructor. (* apply Forall_nil *)    
  - Print sieve_pairs.  
    Print Forall.  
    unfold prime_sieve. fold prime_sieve. 
    case_eq (update_primes (S k) (prime_sieve k)). 
    intros. 
    destruct k.   
    + constructor. 
    + destruct b; simpl. 
      * eapply sieve_pairs_update; eauto.  
      * constructor.   
        split; [lia | exists 2; lia].  
        eapply sieve_pairs_update; eauto.  
Qed. 


Compute prime_sieve 100. 
Compute prime_sieve 103.  

Definition multiple k n := exists i, n = k*i. 
Definition prime n      := 1 < n /\ forall k, 1 < k < n -> ~ multiple k n. 

Lemma prime_not_0 : ~ prime 0. 
Proof. 
  unfold prime. red. intros. lia.   
Qed. 

Lemma prime_not_sieve_pair : forall p q, prime p -> ~ sieve_pair p (q,p).  
Proof. 
  unfold prime. red. intros.  
  destruct H0 as [Hle [i [Hle1 [Heq [Hlep1 Hlep2]]]]]. 
  destruct H as [p1 H]. 
  apply (H q); auto.   
  unfold multiple. 
  now exists i. 
Qed. 

Lemma prime_not_sieve_pairs : forall p, prime p -> ~ In p (map snd (prime_sieve (p-1))).
Proof. 
  red. intros. 
  apply in_map_iff in H0. 
  destruct H0 as [[q m] [Heq Hin]]. 
  simpl in Heq. subst.  
  set (sieve_pairs_prime_sieve (p-1)).  
  cutrewrite (S(p-1) = p) in s. 
  unfold sieve_pairs in s.  
  rewrite Forall_forall in s. 
  destruct (s (q,p) Hin) as [i [Hlt1 [Heq [Hltp1 Hltp2]]]].   
  eapply H; eauto.  
  - unfold multiple. now exists Hlt1. 
  - unfold prime in H. lia.    
Qed. 
  
Definition non_prime_added_dec n  := n <-? List.map snd (prime_sieve (n-1)). 
Definition non_prime_added_bool n := to_bool (non_prime_added_dec n). 
Definition primes n               := map fst (prime_sieve n). 

Lemma non_prime_added : forall n, 
  non_prime_added_bool (S n) = true -> primes n = primes (S n).  
Proof.  
  unfold non_prime_added_bool, non_prime_added_dec, primes.
  unfold prime_sieve. fold prime_sieve.  
  intros k Hnp.
  simpl in Hnp. rewrite <- minus_n_O in Hnp. 
  case_eq (update_primes (S k) (prime_sieve k)). 
  intros sieve nonprime Heq. 
  injection Heq; intros; subst.
  set (prime_sieve k) as ps_k. fold ps_k. fold ps_k in Hnp.   
  destruct (S k <-? map snd ps_k). 
  - destruct k.  
    + reflexivity.  
    + simpl. fold ps_k. 
      rewrite map_map. apply map_ext. 
      intros [p m]. unfold update_prime. 
      now destruct compare.  
  - discriminate Hnp.  
Qed. 

Lemma prime_added : forall n, 0 < n -> 
  non_prime_added_bool (S n) = false ->  (S n) :: primes n = primes (S n). 
Proof. 
  unfold non_prime_added_bool, non_prime_added_dec, primes.
  unfold prime_sieve. fold prime_sieve. 
  intros k Hlt1 Hp. simpl in Hp. rewrite <- minus_n_O in Hp. 
  case_eq (update_primes (S k) (prime_sieve k)). 
  intros sieve nonprime Heq. 
  injection Heq; intros; subst. 
  set (prime_sieve k) as ps_k. fold ps_k. fold ps_k in Hp.  
  destruct (S k <-? map snd ps_k); destruct k; simpl.  
  + inversion Hlt1.   
  + inversion Hp.  
  + inversion Hlt1.  
  + cut (map fst ps_k = map fst (map (update_prime (S(S k))) ps_k));
    [intro; now rewrite H |].  
    rewrite map_map. apply map_ext. 
    intros [p m]. unfold update_prime. 
    now destruct compare. 
Qed. 


Lemma primes_inclusion : forall n, primes n `c` primes (S n). 
Proof. 
  destruct n as [| k].  
  - now idtac.  
  - set (S k) as k1.   
    case_eq (non_prime_added_bool (S k1)); intros.  
    + apply non_prime_added in H. now rewrite H.  
    + apply     prime_added in H. rewrite <- H.
      * now apply incl_tl. 
      * lia.   
Qed. 

Lemma prime_added_prime : forall p, prime p -> non_prime_added_bool p = false. 
Proof. 
  intros. 
  unfold non_prime_added_bool, non_prime_added_dec.
  destruct (p <-? map snd (prime_sieve (p - 1))); intuition.  
  - now destruct (prime_not_sieve_pairs _ H).   
Qed. 

Theorem prime_sieve_correct : forall k p:nat , p <= k -> prime p -> p <- primes k . 
Proof. 
  induction k as [| [| k]]; intros. 
  - inversion H; intros; subst; inversion H0; inversion H1.        
  - destruct H0 as [Hlt1 Hp]. lia.  
  - set (S k) as k1. fold k1 in H. fold k1 in IHk.  
    inversion H. 
    + (* p = k + 1 + 1 *) 
      case_eq (non_prime_added_bool (S k1)).  
      * intros. 
        rewrite <- H1 in *.  
        now rewrite prime_added_prime in H2.  
      * intros. 
        { rewrite <-  prime_added. 
        - now constructor.     
        - lia.  
        - assumption. }    
    + apply primes_inclusion. now apply IHk.  
Qed. 

















(* 9.2.6 Minimal Specification Strengthening *) 
Open Scope nat. 

Section minimal_specification_strengthening. 
  Variable prime : nat -> Prop.

  Definition divides n p        := exists q, q*p = n. 
  Definition prime_divisor n p  := prime p /\ divides n p. 

  Variable prime_test : nat -> bool. 
  Hypothesis prime_test_t : forall n, prime_test n = true  -> prime n. 
  Hypothesis prime_test_f : forall n, prime_test n = false -> ~ prime n. 

  Variable   get_primediv_weak : forall n, ~ prime n -> nat. 
  Hypothesis get_primediv_weak_ok : forall n (H:~prime n), 1 < n -> 
      prime_divisor n (get_primediv_weak n H). 



  Theorem divides_refl : forall n, divides n n. 
  Proof. intros. exists 1; auto with arith. Qed.  

  Hint Resolve divides_refl. 


  Definition bad_get_prime : nat -> nat .
  Proof. 
    intro n; case_eq (prime_test n).  
    - intro; exact n. 
    - intro Hfalse; apply (get_primediv_weak n); auto. 
  Defined. 

  Theorem bad_get_primediv_ok : 
    forall n, 1 < n -> prime_divisor n (bad_get_prime n). 
  Proof. 
    intros n Hlt1. unfold bad_get_prime.  
    (* case (prime_test n).  *)
  Abort. 


  Definition stronger_prime_test : 
    forall n, { prime_test n = true } + { prime_test n = false }. 
  Proof. 
    intros n. case (prime_test n); [left | right] ; reflexivity.  
  Qed. 

  Definition get_prime n :=
    match stronger_prime_test n with 
    | left H  => n 
    | right H => get_primediv_weak n (prime_test_f n H)
    end. 

  Theorem get_primediv_ok : 
    forall n, 1 < n -> prime_divisor n (get_prime n). 
  Proof. 
    intros n Hlt1. unfold get_prime. 
    case (stronger_prime_test n); auto.
    split; auto.  
  Qed. 

End minimal_specification_strengthening. 


















