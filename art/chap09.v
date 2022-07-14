(* Chapter 9 *) 
(* Functions and Their Specifications *) 

(* 9.1 Indctive Types for Specifications *) 
(* 9.2 Strong Specifications *) 
(* 9.3 Variations on Structural Recursion *) 
(* 9.4 Binary Division *) 


Require Import ZArith Lia. 
Set Implicit Arguments. 




(* 9.1 Indctive Types for Specifications *) 

(* 9.1.1 The Subset Type *) 
Inductive sig (A:Set) (P:A->Prop) : Set := 
    exist : forall x:A, P x -> sig P. 
Arguments sig [A] . 
Check sig_ind. 
Reset sig. 








(* ex 9.1 *)
Definition extract (A:Type) (P:A->Prop) : sig P -> A .  
Proof.  intros.  now inversion X.   Defined. 
Reset extract. 
Definition extract (A:Type) (P:A -> Prop) : sig P -> A := 
    fun X : sig P => let (x,H) := X in x . 
Theorem extract_correct : forall A (P:A->Prop) (y: {x:A | P x}), P (extract y). 
Proof.  now induction y .  Qed.     
(* end ex. 9.1 *) 


(* ex 9.2 *) 
Open Scope Z_scope.  
Section div_pair . 
    Unset Implicit Arguments. 

    Variable div_pair : 
        forall a b:Z, 0<b -> { p:Z*Z | a=(fst p)*b + snd p /\ 0 <= snd p < b } . 

    Definition div_pair' (a:Z) (x:{ b:Z | 0<b }) : Z*Z := 
        match x with 
        | exist _ b H  => extract (div_pair a b H)      end.
End div_pair. 
(* end ex. 9.2 *) 


(* ex 9.3 *) 
Definition sig_rec_simple (A:Set)(P:A->Prop)(B:Set) : 
    (forall x:A, P x -> B) -> sig P -> B.
Proof.  intros. destruct H0. exact (H x p).  Defined. 
Print sig_rec_simple. 
(* end ex. 9.3 *) 





(* 9.1.2 The nested Subset Type *) 
Print sigT.  

(* 9.1.3 Certified Disjoint Sum *) 
Print sumbool. 




(* ex 9.4 *) 
Definition eq_dec (A:Type) := forall x y:A, {x=y} + {x<>y}. 

Theorem nat_eq_dec : eq_dec nat. 
Proof. red. induction x; destruct y; intuition. elim (IHx y); intuition. Qed.  
(* end ex. 9.4 *) 






(* 9.1.4 Hybrid Disjoint Sum *) 
Inductive sumor (A:Set)(B:Prop) : Set := 
  | inleft : A -> sumor A B | inright : B -> sumor A B . 
Reset sumor. 








(* 9.2 Strong Specification *) 

(* sigS A [x:A]B =: {x:A & B} *) 
Inductive sigS {A:Set} (P:A -> Set) : Set := 
  | existS : forall x : A, P x -> sigS P. 
Reset sigS. 



Section pred. 
  Definition pred' (n:nat) : {p:nat | n = S p} + {n=O} := 
      match n return {p:nat | n = S p} + {n=O} with 
      | O     => inright _ (refl_equal O) 
      | S p   => inleft  _ (exist (fun p':nat => S p=S p')p(refl_equal (S p))) end. 
  Reset pred'. 
  
  Definition pred' : forall n:nat, {p:nat | n = S p}+{n=O} . 
  Proof.  induction n; [ now right | left; now exists n ] . Defined. 
  
  (* 9.2.3 Preconditions for Partial Functions *) 
  
  Definition pred_partial : forall n:nat, n<>O -> nat. 
  Proof. induction n; intros H; [ now elim H | exact n ] .  Defined. 
  
  (* 9.2.4 Proving Preconditions *) 
  Open Scope nat. 
  
  Theorem le_2_n_not_O : forall n:nat, 2 <= n -> n <> 0 . 
  Proof. intuition . Qed. 
  
  Theorem le_2_n_pred : forall n (h:2<=n), pred_partial n (le_2_n_not_O n h) <> 0 .   
      (* cannot solve 2nd order unification *)  Abort. 
  
  Theorem le_2_n_pred' : forall n, 2<=n -> forall h:n<>0, pred_partial n h <> 0. 
  Proof. induction 1; intros; [ discriminate | now apply le_2_n_not_O ] .  Qed. 
  
  Theorem le_2_n_pred : forall n (h:2<=n), pred_partial n (le_2_n_not_O n h) <> 0 .   
  Proof. intros; exact (le_2_n_pred' n h (le_2_n_not_O n h)) . Qed. 
  
  Definition pred_partial_2 n (h:2<=n) := 
      pred_partial (pred_partial n (le_2_n_not_O n h)) (le_2_n_pred n h). 
  
  
  
  (* 9.2.5 ** Reinforcing Specifications *) 
  
  Definition pred_strong : forall n, n <> O -> { v:nat | n = S v } .
  Proof. induction n; [ now intros H | now exists n ] . Defined. 
  
  Theorem pred_strong2_th1 : forall n p, 2 <= n -> n = S p -> p <> O .  Proof. lia. Qed.  
  
  Theorem pred_th1 : forall n p q, n = S p -> p = S q -> n = S (S q) .  Proof. lia. Qed. 
  
  Definition pred_strong2 n (h:2<=n) : {v:nat | n = S(S v)} := 
      match pred_strong n (le_2_n_not_O n h) with 
      | exist _ p h' => 
          match pred_strong p (pred_strong2_th1 n p h h') with 
          | exist _ p' h'' => exist(fun x=>n=S(S x))p'(pred_th1 n p p' h' h'') end end.    
  Reset pred_strong2. 
  
  Definition pred_strong2 : forall n, 2 <= n -> {v:nat | n = S(S v)} . 
  Proof. 
      intros n h; case (pred_strong n).  
      - now apply le_2_n_not_O. 
      - intros p H; case (pred_strong p).    
        + now apply (pred_strong2_th1 n).  
        + intros p' H'; exists p'; intuition .     
  Defined. 

End pred. 


(* 9.2.6  *** Minimal Specification Strengthening *) 

(* ==> see prime.v *) 


(* 9.2.7 "refine" tactic *)
Open Scope nat. 
Definition pred_partial' : forall n, n <> 0 -> nat. 
Proof. 
  refine (fun n => 
          match n as x return x <> 0 -> nat with 
          | O => fun h: 0<>0 => _ 
          | S _ => _ end ) .   
Abort. 













(* 9.3 Variations on Strucural Recursion *)

(* 9.3.1 Structural Recursion with Mulitiple Steps *) 

Open Scope nat. 

Fixpoint div2 (n:nat) : nat := 
    match n with 
    | O     => O 
    | 1     => O 
    | S(S p)=> S (div2 p)   end. 

Theorem div2_le : forall n : nat, div2 n <= n . 
Proof.  
    intros n. 
    cut (div2 n <= n /\ div2 (S n) <= S n); [ tauto | ].    
    induction n; [ | destruct IHn ] ; split; simpl; auto with arith.  
Qed. 


(* ex. 9.6 *) 
Fixpoint div3 (n:nat) : nat := 
    match n with 
    | S(S(S p)) => S(div3 p) 
    | _         => O          end. 

Theorem div3_le : forall n : nat, div3 n <= n . 
Proof. 
    intros n. 
    cut (div3 n <= n /\ div3 (S n) <= S n /\ div3 (S(S n)) <= S(S n)); [ tauto | ].  
    induction n; [ | destruct IHn as [Hn [HSn HSSn]] ]; split; simpl; auto with arith.    
Qed. 


(* ex. 9.7 *) 
Fixpoint mod2 (n:nat) : nat := 
    match n with 
    | O     => O 
    | 1     => 1 
    | S(S p)=> mod2 p   end. 

Compute mod2 5. 
Compute div2 5. 

Lemma mul2 : forall n, 2 * n = n+n .  Proof. lia.  Qed. 

Theorem division_nat : forall n, n = 2 * div2 n + mod2 n . 
Proof. 
    intros n . 
    cut (n = 2 * div2 n + mod2 n /\ (S n) = 2 * div2 (S n) + mod2 (S n)); try tauto. 
    induction n; intuition. 
    - simpl; auto with arith.     
      SearchRewrite (_ + O).  rewrite <-plus_n_O. 
      SearchRewrite (S(_+_)). rewrite <-plus_n_Sm, plus_Sn_m . 
      omega.    
Qed. 

Theorem nat_2_ind : forall P : nat->Prop, 
    P O -> P 1 -> (forall n, P n -> P(S(S n))) -> forall n, P n. 
Proof.  intros. cut (P n /\ P (S n)); elim n; intuition.  Qed. 


(* ex. 9.8 Fibonacci *) 
(* ==> see fib.v *) 


(* ex 9.9 *) 
Theorem nat_3_ind : 
    forall P : nat -> Prop, 
    P 0 -> P 1 -> P 2 -> (forall n, P n -> P (S(S(S n)))) -> forall n, P n. 
Proof. intros. cut (P n /\ P(S n) /\ P(S(S n))); elim n; intuition. Qed. 

Theorem nat_4_ind : 
    forall P : nat -> Prop, 
    P 0 -> P 1 -> P 2 -> P 3 -> (forall n, P n -> P (S(S(S(S n))))) -> forall n, P n. 
Proof. intros. cut (P n /\ P(S n) /\ P(S(S n)) /\ P(S(S(S n)))); elim n; intuition. Qed. 
(* end ex. 9.9 *) 


(* ex. 9.10 *) 
(* ==> see fib.v *) 


(* ex. 9.11 *)
(* redo ex. 9.6 ~ 9.8 with the corresponding induction principles *) 


(* 9.3.2 Simplifying the Step *) 


(* ex. 9.12 *) 
Fixpoint mult2 (n:nat) : nat := 
    match n with 
    | O     => O 
    | S p   => S(S(mult2 p)) end. 

Definition div2_mod2 : forall n, {q:nat & {r:nat | n = (mult2 q)+r /\ r <= 1}} .
Proof. 
    refine (
    fun n => 
        existT (fun q => { r | (n = mult2 q + r) /\ r <= 1 } )
        (div2 n)  (exist (fun r => n = mult2(div2 n)+r /\ r<=1) (mod2 n) _ ) 
    ). 
    induction n using nat_2_ind; intuition; simpl; lia.   
Defined.  



(* 9.3.3 Recursive Functions with Several Arguments *) 

Open Scope nat. 

Fixpoint plus   n m :=  match n with 
                        | O     => m 
                        | S p   => S (plus p m) end.  
Fixpoint plus'  n m :=  match m with 
                        | O     => n
                        | S p   => S (plus' n p) end. 

Theorem plus_n_O  : forall n, n = n + O.           Proof. intuition.  Qed.  
Theorem plus_n_Sm : forall n m, S(n+m) = n + S m.  Proof. destruct n; intuition . Qed. 
Theorem plus_comm : forall n m, n+m = m+n. 
Proof. induction n; try (intros; rewrite <- plus_n_Sm) ; intuition.  Qed. 
Theorem plus'_O_n : forall n, n = plus' O n. 
Proof. induction n; simpl; intuition.    Qed. 
Theorem plus'_Sn_m : forall n m : nat, S(plus' n m) = plus' (S n) m. 
Proof. intros n m; induction m;simpl; intuition.   Qed. 
Theorem plus'_comm : forall n m , plus' n m = plus' m n. 
Proof. induction n; simpl; intuition; 
        [ rewrite <- plus'_O_n | intros; rewrite <- plus'_Sn_m ] ; intuition . Qed. 
Theorem plus_plus' : forall n m, n+m = plus' n m . 
Proof. 
    intros.
    rewrite plus'_comm .    (* This changes the principle argument of plus':    *) 
                            (* plus' n m {struct m} -> plus' m n {struct n}     *)  
    induction n; simpl; intuition. 
Qed. 


(* tail recursive addition *) 

Fixpoint plus'' n m :=  match m with 
                        | O     => n 
                        | S p   => plus'' (S n) p end. (* tail recursive *) 

Theorem plus''_Sn_m : forall n m, S (plus'' n m) = plus'' (S n) m. 
Proof. intros; generalize n; induction m; simpl; intuition. Qed. 
Theorem plus''_n_Sm : forall n m, S (plus'' n m) = plus'' n (S m). 
Proof. intros; generalize n; induction m; simpl; intuition; now rewrite IHm. Qed. 

(* ex. 9.13 *) 
Theorem plus'_assoc : forall n m l, plus' n (plus' m l) = plus' (plus' n m) l.  
Proof. 
    induction n; intuition;
    [ repeat rewrite <- plus'_O_n | repeat rewrite <- plus'_Sn_m]; intuition. 
Qed. 

(* ex. 9.14 *) 
Theorem plus''_assoc : forall n m l, plus'' n (plus'' m l) = plus'' (plus'' n m) l. 
Proof. 
    intros; generalize n m; induction l; intuition.  
    - repeat rewrite <- plus''_Sn_m. 
      repeat rewrite <- plus''_n_Sm.  intuition.  
Qed. 

(* ex 9.15 : tail-recursive fibonacci *) 
(* ==> see fib.v *) 





(* 9.4  Binary Division *) 


(* weak specification *) 

Open Scope Z_scope. 

Fixpoint div_bin (n m: positive) {struct n} : Z * Z := 
    match n with 
    | 1%positive    =>  match m with 
                        | 1%positive    => (1,0)
                        | v             => (0,1) end 
    | xO n'         =>  let (q', r') := div_bin n' m in 
                        match Z_lt_ge_dec (2*r')(Zpos m) with 
                        | left Hlt      => (2*q', 2*r') 
                        | right Hgt     => (2*q'+1, 2*r' - (Zpos m)) end
    | xI n'         =>  let (q', r') := div_bin n' m in 
                        match Z_lt_ge_dec (2*r'+1)(Zpos m) with 
                        | left Hlt      => (2*q', 2*r'+1)
                        | right Hgt     => (2*q'+1, 2*r'-(Zpos m) + 1) end end . 

Print Z_lt_ge_dec . 
Print Z_lt_dec. 
Locate "_ < _". 
Print Z.lt . 

Compute div_bin 1231237489 13218. 


Theorem rem_1_1_interval : 0 <= 0 < 1 . 
Proof. omega. Qed. 
Theorem rem_1_even_interval : forall m, 0 <= 1 < Zpos(xO m) . 
Proof. 
    intros; split.
    - auto with zarith. 
    - Locate "_ < _". 
      Print Z.lt . 
      compute. intuition.  
Qed. 
Theorem rem_1_odd_interval : forall m, 0 <= 1 < Zpos(xI m) . 
Proof. split; [auto with zarith | compute; intuition] . Qed. 
Theorem rem_even_ge_interval : forall m r, 0 <= r < m -> 2*r >= m -> 0 <= 2*r - m < m .
Proof. intros. omega. Qed. 
Theorem rem_even_lt_interval : forall m r, 0 <= r < m -> 2*r < m -> 0 <= 2*r < m .
Proof. intros. omega. Qed. 
Theorem rem_odd_ge_interval  : forall m r, 0 <= r < m -> 2*r+1 >= m -> 2*r+1 - m < m .  
Proof. intros. omega. Qed. 
Theorem rem_odd_lt_interval  : forall m r, 0 <= r < m -> 2*r+1 < m -> 0 <= 2*r+1 < m . 
Proof. intros. omega. Qed. 


Hint Resolve 
    rem_odd_ge_interval rem_even_ge_interval
    rem_odd_lt_interval rem_even_lt_interval
    rem_1_odd_interval  rem_1_even_interval 
    rem_1_1_interval rem_1_even_interval . 

Ltac div_bin_tac arg1 arg2 := 
    elim arg1;
    [ intros p; lazy beta iota delta [div_bin]; fold div_bin;
        case (div_bin p arg2); unfold snd; intros q' r' Hrec;
        case (Z_lt_ge_dec (2*r'+1)(Zpos arg2)); intros H
    | intros p; lazy beta iota delta [div_bin]; fold div_bin;
        case (div_bin p arg2); unfold snd; intros q' r' Hrec; 
        case (Z_lt_ge_dec (2*r')(Zpos arg2)); intros H
    | case arg2; lazy beta iota delta [div_bin]; intros]. 

Theorem div_bin_rem_lt : 
    forall n m, 0 <= snd(div_bin n m) < Zpos m. 
Proof. intros n m; div_bin_tac n m; unfold snd; auto.  omega. Qed.  

SearchRewrite (Zpos (xI _)).

Theorem div_bin_eq : 
    forall n m, Zpos n = (fst(div_bin n m))*(Zpos m) + snd (div_bin n m).
Proof. 
    intros; div_bin_tac n m; 
    rewrite Zpos_xI || (try rewrite Zpos_xO); 
    try rewrite Hrec; unfold fst, snd; ring.    
Qed. 


(* strong specification *) 

Inductive div_data (n m: positive) : Set := 
    div_data_def : forall q r:Z, Zpos n = q*(Zpos m)+r -> 0<=r<Zpos m -> div_data n m.


Definition div_bin' : forall n m, div_data n m. 
Proof. 
    intros n m; elim n. 
    - intros n' [q r H_eq H_int] . 
      case (Z_lt_ge_dec (2*r + 1)(Zpos m)). 
      + exists (2*q) (2*r+1). 
        rewrite Zpos_xI; rewrite H_eq; ring. 
        auto. 
      + exists (2*q+1)(2*r+1 - (Zpos m)). 
        rewrite Zpos_xI; rewrite H_eq; ring. 
        omega. 
    - intros n' [q r H_eq H_int] .  
      case (Z_lt_ge_dec (2*r) (Zpos m)). 
      + exists (2*q) (2*r).  
        rewrite Zpos_xO; rewrite H_eq; ring.
        auto. 
      + exists (2*q+1)(2*r - (Zpos m)) . 
        rewrite Zpos_xO; rewrite H_eq; ring. 
        omega.  
    - elim m. 
      + exists 0 1; auto. 
      + exists 0 1; auto. 
      + exists 1 0; omega.   
Qed. 


(* ex. 9.16 *) 
(* ==> see sqrt.v *)  

Check positive_ind. 
Theorem positive_2_ind : forall P : positive -> Prop, 
    (forall p, P p -> P (p~1~1)%positive) -> 
    (forall p, P p -> P (p~1~0)%positive) -> 
    (forall p, P p -> P (p~0~1)%positive) -> 
    (forall p, P p -> P (p~0~0)%positive) -> 
    P 1%positive -> P 2%positive -> P 3%positive -> forall p, P p. 
Proof. 
    intros; cut (P p /\ P(p~0)%positive   /\ P(p~1)%positive   /\ 
    P(p~1~1)%positive /\ P(p~1~0)%positive /\ P(p~0~1%positive) /\ P(p~0~0)%positive). 
    tauto. 
    elim p; intuition. 
Qed. 


(* ex. 9.17 *) 
(* ==> see fib.v *) 

