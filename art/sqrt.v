
Require Import ZArith. 
Require Export CoqArt.chap15 . 
Open Scope Z_scope. 




(* ex. 9.16 *) 

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

Check positive_rec. 
Theorem positive_2_rec : forall P : positive -> Set, 
    (forall p, P p -> P (p~1~1)%positive) -> 
    (forall p, P p -> P (p~1~0)%positive) -> 
    (forall p, P p -> P (p~0~1)%positive) -> 
    (forall p, P p -> P (p~0~0)%positive) -> 
    P 1%positive -> P 2%positive -> P 3%positive -> forall p, P p. 
Proof. 
    intros. Check (P p, P (p~1)%positive) . 
Abort. 

Fixpoint sqrt_bin (n:positive) : Z * Z := 
    match n with 
    | xH        =>  (1,0) 
    | xO p      =>  match p with 
                    | xH        =>  (1,1) 
                    | xO n'     =>  let (s',r') := sqrt_bin n'      in 
                                    let (s,r)   := (2*s',4*r')      in 
                                    match Z_lt_ge_dec r (2*s+1) with 
                                    | left Hlt  => (s,r) 
                                    | right Hgt => (s+1,r-2*s-1)    end 
                    | xI n'     =>  let (s',r') := sqrt_bin n'      in 
                                    let (s,r)   := (2*s',4*r'+2)    in 
                                    match Z_lt_ge_dec r (2*s+1) with 
                                    | left Hlt  => (s,r) 
                                    | right Hgt => (s+1,r-2*s-1)    end end
    | xI p      =>  match p with 
                    | xH        =>  (1,2)
                    | xO n'     =>  let (s',r') := sqrt_bin n'      in 
                                    let (s,r)   := (2*s',4*r'+1)    in 
                                    match Z_lt_ge_dec r (2*s+1) with 
                                    | left Hlt  => (s,r) 
                                    | right Hgt => (s+1,r-2*s-1)    end 
                    | xI n'     =>  let (s',r') := sqrt_bin n'      in 
                                    let (s,r)   := (2*s',4*r'+3)    in 
                                    match Z_lt_ge_dec r (2*s+1) with 
                                    | left Hlt  => (s,r) 
                                    | right Hgt => (s+1,r-2*s-1)    end end 
    end. 

Compute sqrt_bin 1000000.  

Ltac Zpos_XX :=
    try rewrite Zpos_xI; try rewrite Zpos_xO; 
    try rewrite Zpos_xI; try rewrite Zpos_xO.  

(* strong specification *) 
Inductive sqrt_data (n:positive) : Set := sqrt_data_def : 
    forall s r, Zpos n = s*s + r -> s*s <= Zpos n < (s+1)*(s+1) -> sqrt_data n .  

Require Import Lia. 
Definition sqrt_bin' : forall n, sqrt_data n. 
    refine ( fix sqrt_bin' (n:positive) : sqrt_data n := 
    match n return sqrt_data n with 
    | xH    => sqrt_data_def _ 1 0 _ _ 
    | xO p  => match p with 
               | xH    => sqrt_data_def _ 1 1 _ _ 
               | xO n' => match sqrt_bin' n' with 
                          | sqrt_data_def _ s' r' Heq H => 
                                  match Z_lt_ge_dec (4*r')(4*s'+1) with 
                                  | left Hlt => sqrt_data_def _ (2*s')(4*r')_ _ 
                                  | right Hge=> sqrt_data_def _(2*s'+1)(4*r'-4*s'-1)_ _ end end
               | xI n' => match sqrt_bin' n' with 
                          | sqrt_data_def _ s' r' Heq H => 
                                  match Z_lt_ge_dec (4*r'+2)(4*s'+1) with 
                                  | left Hlt => sqrt_data_def _(2*s')(4*r'+2)_ _ 
                                  | right Hge=> sqrt_data_def _(2*s'+1)(4*r'-4*s'+1)_ _ end end end
    | xI p  => match p with 
               | xH    => sqrt_data_def _ 1 2 _ _ 
               | xO n' => match sqrt_bin' n' with 
                          | sqrt_data_def _ s' r' Heq H => 
                                  match Z_lt_ge_dec (4*r'+1)(4*s'+1) with 
                                  | left Hlt => sqrt_data_def _(2*s')(4*r'+1)_ _ 
                                  | right Hge=> sqrt_data_def _(2*s'+1)(4*r'-4*s')_ _ end end 
               | xI n' => match sqrt_bin' n' with 
                          | sqrt_data_def _ s' r' Heq H => 
                                  match Z_lt_ge_dec (4*r'+3)(4*s'+1) with 
                                  | left Hlt => sqrt_data_def _(2*s')(4*r'+3) _ _ 
                                  | right Hge=> sqrt_data_def _(2*s'+1)(4*r'-4*s'+2)_ _ end end end end); 
    try Zpos_XX; try rewrite Heq; try lia.   
Qed. 

Check Z.of_nat. 
Check Z.to_nat. 



(* ex. 15.4 *)


Print div.  

  
Eval compute in match div 1000 13 _ with 
    existT _ s _ => s end. 

Compute sqrt_bin 2000000000000000000000000.  



(* ex. 16.2 *)
Open Scope Z. 
Theorem division_sqrt : forall n m k, 0 < m < n -> n = m * k -> 
    0 < m <= Z.sqrt n   \/  0 < k <= Z.sqrt n . 
Proof. 
  intros; elim (Z_lt_le_dec (Z.sqrt n) m); elim (Z_lt_le_dec (Z.sqrt n) k); 
  intros; auto with zarith. 
  - assert (Z.succ(Z.sqrt n) <= k); assert (Z.succ(Z.sqrt n) <= m); auto with zarith. 
    set (Z.sqrt_spec n). 
    assert (Z.succ(Z.sqrt n) * Z.succ(Z.sqrt n) <= m * k).     
    + Search ( _ * _ <= _ * _ ).     
      apply Zmult_le_compat; assert(0<=Z.sqrt n); auto with zarith; apply Z.sqrt_nonneg. 
    + subst. eapply Z.lt_le_trans in H3; 
      [ apply Z.lt_irrefl in H3 | apply a1]; auto with zarith. 
Qed. 

     
