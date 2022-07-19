(* Chapter 15. General Recursion *) 





Require Import Arith Lia. 
(* 15.1 Bounded Recursion *)

Search le_gt_dec. 
Fixpoint bdiv_aux (b m n : nat) {struct b} : nat * nat :=
  match b with 
  | O   =>  (O,O)
  | S b'=>  match le_gt_dec n m with 
            | left H   => match bdiv_aux b' (m-n) n with 
                          | pair q r => (S q, r) end 
            | right H  => (O, m) end end. 


Theorem bdiv_aux_correct1 : 
  forall b m n, m <= b -> O < n -> m = fst(bdiv_aux b m n) * n + snd (bdiv_aux b m n). 
Proof. 
  intros b; elim b; simpl.  
  - intros. now inversion H.    
  - intros b' Hrec m n Hleb Hlt; case (le_gt_dec n m); simpl; auto.      
    intros Hle; generalize (Hrec (m-n) n).
    case (bdiv_aux b' (m-n) n); simpl; intros q r Hrec'. 
    rewrite <- plus_assoc; rewrite <- Hrec'; lia.  
Qed. 

(* ex. 15.1 *)
Theorem bdiv_aux_correct2 : 
  forall b m n, m <= b -> 0 < n -> snd (bdiv_aux b m n) < n . 
Proof. 
  simple induction b. 
  - intros. now inversion H. 
  - intros b' Hrec m n Hleb Hlt. simpl. case (le_gt_dec n m);
    intros Hle; simpl; auto.   
    generalize (Hrec (m-n) n). 
    case (bdiv_aux b' (m-n) n); simpl; intros q r Hrec'.     
    apply Hrec'; lia.  
Qed. 
(* end 15.1 *)

Definition bdiv : forall m n, O < n -> {q & {r | m = q*n+r /\ r < n}}. 
refine (fun m n h => 
  let p := bdiv_aux m m n in 
  existT (fun q => {r | m = q*n+r /\ r < n}) (fst p) (exist _ (snd p) _ )). 
  unfold p; split; [ apply bdiv_aux_correct1 | eapply bdiv_aux_correct2]; lia.   
Defined. 

Time Eval compute in match bdiv 20000 31 (lt_O_Sn 30) with 
  existT _ q (exist _ r h ) => (q,r) end. 

Time Eval lazy beta delta iota zeta in match bdiv 20000 31 (lt_O_Sn 30) with 
  existT _ q (exist _ r h ) => (q,r) end. 

Time Eval lazy beta delta iota zeta in bdiv_aux 20000 20000 31. 


(* ex 15.2 *)
Definition bdiv_aux' : forall b m n, m <= b -> 0 < n -> {q & {r | m = q*n+r /\ r < n}}.  
refine (fun b m n hb h => 
  let p := bdiv_aux b m n in 
  existT (fun q => {r | m = q*n+r /\ r < n}) (fst p) (exist _ (snd p) _ )). 
unfold p; split; [ apply bdiv_aux_correct1 | eapply bdiv_aux_correct2]; lia.   
Defined.  


(* ex. 15.3 *) 
(* ==> see sort.v *) 










(* 15.2 ** Well-founded Recursive Functions *) 

(* 15.2.1 Well-founded Relations *) 

Check lt_wf. 

Theorem wf_lt : well_founded lt. 
Proof. 
  intros n. 
  induction n. 
  constructor. 
  + inversion 1.  
  + constructor.  
    intros. 
    inversion IHn. 
    inversion H.
    - assumption.  
    - apply H0. assumption.  
Qed. 


(* 15.2.2 Accessibility Proofs *) 



Require Import Wellfounded ZArith. 
Search (well_founded _). 
Print Z.lt_wf. 

(* Require Import RecursiveDefinition. *)


Require Import Wellfounded. 
Require Import Relations. 
Require Import Relations.Relation_Operators.


(* Assembling Well-founded Relations *) 


(* ex. 15.5 *) 
Section wf_btree. 
  Variable A : Type. 
  
  Inductive btree : Type :=
    | bleaf 
    | bnode (a:A) (l r: btree).  
  
  Inductive subtree (t:btree) : btree -> Prop := 
    | subL     : forall r a, subtree t (bnode a t r)
    | subR     : forall l a, subtree t (bnode a l t). 
  
  Theorem wellfounded_subtree : well_founded subtree. 
  Proof. red. induction a; constructor; intros; now inversion H. Qed. 
  
  Definition subtree_wf := wf_clos_trans _ _  wellfounded_subtree. 
  
  Print wf_clos_trans. 
  Print Acc_clos_trans. 
  Print clos_trans. 
  
End wf_btree. 


(* 15.2.4 Well-founded Recursion *) 

(* 15.2.5 The Recursor well_founded_induction *)  


(* ex 15.6 *)
Lemma wf_inclusion : forall A R S, inclusion A R S -> well_founded S -> well_founded R. 
Proof. red. intros. induction (H0 a); econstructor; eauto. Qed.  


(* ex 15.7 *)
Lemma not_acc {A: Type} {R : A->A->Prop} : 
  forall a b : A, R a b -> ~ Acc R a -> ~ Acc R b. 
Proof. 
  intros a b H H0 H1. 
  apply H0. constructor. 
  (* ASSUMPTION : Acc"<"b ,   a < b    *)  
  (* --------------------------------- *)
  (* GOAL : forall y, y < a -> Acc"<"y *)  

  (* since a < b , forall y < a is Acc by Acc"<"b *) 
  (* induction H1. intros. *) (* now transitivity of y < a and a < x. QED  *)  

  (* more generally in the case "<" is not transitive *) 
  generalize a H. induction H1. apply H1. 
Qed. 



Lemma not_decreasing_aux : 
  forall A R (seq:nat->A), well_founded R -> ~ (forall i, R(seq(S i))(seq i)).  
Proof. 
  intros A R seq H H_inf_decrease. 
  (* now we have "seq", an infinite R - decreasing chain *)  
  (* so if a is some point of the sequence, we can have the infinite R sequence *) 
  (* let us show that ; *) 
  assert ( H_belong_inf_seq : forall a_i, (exists i, a_i = seq i ) -> ~ Acc R a_i). 
  - intros a_i. 
    Check well_founded_ind . 
    pattern a_i. 
    apply well_founded_ind with A R; auto. 
    + intros x Hx [i Hi]; subst. 
      apply not_acc with (seq (S i)); auto. 
      * apply Hx; auto.  
        { now exists (S i). }
  - apply (H_belong_inf_seq (seq 13)).  
    + now exists 13. 
    + apply H.  
Qed. 
        
Theorem not_decreasing : forall A R, well_founded R -> 
  ~ exists seq:nat->A, forall i, R (seq (S i))(seq i). 
Proof. 
  red. intros A R Hwf Hseq. 
  destruct Hseq as [seq Hseq].  
  assert (forall a, ( exists i, a = seq i ) -> ~ Acc R a) . 
  - intro a; pattern a. apply well_founded_ind with A R.     
    + assumption.  
    + intros x Hx [i Hi]. generalize (Hseq i). intro H0; subst.
      apply not_acc with (seq (S i)); auto. 
      apply Hx; auto.  
      now exists (S i). 
  - apply (H (seq 0)). 
    + now exists 0. 
    + red in Hwf. apply Hwf.    
Qed. 


Require Import Inverse_Image. 
Check wf_inverse_image. 

Lemma wf_from_nat A R : well_founded R -> 
  forall seq:nat->A,
  well_founded (fun i j => R (seq i) (seq j)). 
Proof. 
  intros. 
  eapply wf_inverse_image; eauto. 
Qed. 

Theorem not_decreasing' : forall A (R:A->A->Prop), well_founded R -> 
  ~ exists seq, forall i, R (seq(S i))(seq i). 
Proof. 
  intros A R Hwf ex.   
  destruct ex as [seq infseq]. 
  Check well_founded_ind. 
  set (wf_from_nat A R Hwf seq ). 
  set (well_founded_ind (wf_from_nat A R Hwf seq)). 
  apply p . 
  + intros. now apply (H (S x)).   
  + exact O.   
Qed. 



Print Acc_inv. 
Lemma Acc_inv' : forall A R, 
  (forall x:A, Acc R x) -> forall x y, R y x -> Acc R y.  
Proof. 
  intros. 
  eapply Acc_inv; eauto. 
Qed. 


Require Import Classical.   
Check NNPP. 

Lemma contra : forall P Q, (~ Q -> ~ P) <-> (P -> Q ). 
Proof. intuition. apply NNPP. intuition. Qed.   
Lemma comp : forall P Q R, (P -> Q) -> (Q -> R) -> (P -> R). 
Proof. tauto. Qed.  

Definition notnot := NNPP. 

Lemma not_imp_and_not : forall P Q: Prop, (~ (P -> Q)) -> P /\ ~ Q .  
Proof. intros. split; tauto. Qed.      

Print ex. 
Print Acc_inv. 

Definition Acc_inv := 
  fun A (R:A->A->Prop) (x:A) (H: Acc R x) => 
  match H in (Acc _ _) return (forall y, R y _ -> Acc R y) with 
  | Acc_intro _ H0 => H0 end. 
Print Acc. 

Section not_decrease_inv. 
  Variable A:Type.  
  Variable R : A -> A -> Prop. 
  Axiom R_dec : forall x y, {R x y} + { ~ R x y}.  
  Axiom not_R : forall x y, ~ R x y -> {R y x} + { x = y }. 
  Axiom sym_eq_R : forall x y, R x y -> R y x -> x = y. 
  Axiom tran : transitive _ R. 
  Print Acc. 

  Fixpoint recf (f:A->A) i a := match i with 
                       | O    => f a 
                       | S i' => f (recf f i' a) end. 

  Fixpoint repeat' (a:A) (f: forall a, exists b:A, R b a )  i  := 
      match i  with 
      | O   => f a
      | S p => 
          match f a with 
          | ex_intro _ b Rba => 
              match repeat' b f p with 
              | ex_intro _ y Ryb => 
                  match f y return exists z, R z a with 
                  | ex_intro _ z Rzy => ex_intro _ z (tran _ _ _ Rzy (tran _ _ _ Ryb Rba)) end
                  end end end. 
  Print eq. 
  Definition mkfun (a:A) (Nacc : ~ Acc R a) : exists b:A, R b a. 
  Proof. 
    intros. 
    red in Nacc. 
    apply NNPP. 
    intros Nex. 
    apply Nacc. 
    set (Acc_intro (R := R) a ) as acc. 
    destruct (not_all_ex_not _ _ (comp _ _ _ acc Nacc)) as [a1 H1'].   
    destruct (not_imp_and_not _ _ H1') as [R1 H1].  
    apply False_ind. 
    apply Nex. 
    now exists a1. 
  Qed. 

  Lemma seq_lemma' : 
    forall (a:A) (f:forall a, exists b, R b a), exists seq, forall i, R(seq(S i))(seq i).
  Proof. 
    intros. 
    destruct (f a) as [b H]. 
    (*
    exists (fun i => match repeat' a f i with ex_intro _ z _ => z end) . 
    *) 
  Abort. 
  Lemma seq'_seq : forall a, (exists b, R b a) -> (exists f, R (f a) a).  
  Proof. 
    intros a [b H].  
    now exists (fun _ => b). 
  Qed. 

  Lemma seq_lemma : 
    forall (a:A), (exists f, forall a, R (f a) a)  ->
    exists seq, forall i, R (seq(S i))(seq i). 
  Proof. 
    intros a [f H].  
    exists (fun i => recf f i a). 
    intros. 
    simpl. 
    apply H. 
  Qed. 


  Theorem not_decreasing_inv : 
    (~ exists seq:nat->A, forall i, R(seq(S i))(seq i) )-> well_founded R. 
  Proof. 
    apply contra. 
    intros Nwf Ninf.  
    red in Nwf.  

    unfold well_founded in Nwf. 
    red in Ninf. 
    Check not_ex_all_not. 
    apply not_all_ex_not in Nwf. 
    destruct Nwf as [a H]. 
    Check Acc_intro. 
    red in H. 
    apply H. 
    Check well_founded_ind. 
  
    set (Acc_intro (R:=R) a) as acc.   
    destruct (not_all_ex_not _ _ (comp _ _ _ acc H)) as [a1 H1'].   
    destruct (not_imp_and_not _ _ H1') as [R1 H1].  
    set (Acc_intro (R:=R) a1) as acc1. 
    destruct (not_all_ex_not _ _ (comp _ _ _ acc1 H1)) as [a2 H2'].   
    destruct (not_imp_and_not _ _ H2') as [R2 H2].  
    set (Acc_intro (R:=R) a2) as acc2. 
    
  Restart. 
    apply contra. 
    intros Nwf Ninf. 
    unfold well_founded in Nwf. 
    apply not_all_ex_not in Nwf. 
    destruct Nwf as [a H]. 
    eapply not_ex_all_not in Ninf. 
    eapply not_all_ex_not in Ninf. 
    destruct Ninf as [i Ninf1] .  
    induction Ninf1. 
    set (Acc_intro (R:=R) a) as acc. 
    destruct (not_all_ex_not _ _ (comp _ _ _ acc H)) as [a1 H1']. 
    destruct (not_imp_and_not _ _ H1') as [R1 H1]. 

    (* seq inhabits in a FUNCTION SPACE, 
       so we need lemmas that connect type A with the FUNCTION SPACE. 

       we only need seq to be PARTIAL if we see seq as a member of ENDO(A) 
       so that the countable sequence is partial to the whole space A.  
    *) 

  Restart. 
    apply contra. 
    intros Nwf Ninf. 
    unfold well_founded in Nwf. 
    apply not_all_ex_not in Nwf. 
    destruct Nwf as [a Nacc]. 
    apply Ninf. 
    apply seq_lemma; auto. 
    cut (forall a, exists f, R (f a) a). 
    intros.
    destruct (H a) as [f Rfaa].  

  Abort. 
End not_decrease_inv. 

(* end 15.7 *)







Check sigT. 





(* 15.2.6 Well-founded Euclidean Division *) 
Check le_plus_minus. 
Check plus_assoc. 

Definition div_type  (m:nat)  := forall n, 0<n -> {q & { r | m = q*n+r /\ r < n }}. 

Definition sqrt_type (n:nat)  := {s & { r | n = s*s+r /\ n < (S s)*(S s) }}. 

Definition div_type' m n q    := { r | m = q*n+r /\ r < n }. 
Definition sqrt_type' n s     := { r | n = s*s+r /\ n < (S s)*(S s) }. 

Definition div_type'' m n q r := m = q*n+r /\ r < n. 
Definition sqrt_type'' n s r  := n = s*s+r /\ n < (S s)*(S s).  

Check Acc_inv_dep. 

Definition div_F : 
  forall x, (forall y, y < x -> div_type y) -> div_type x. 
Proof. 
  unfold div_type at 2. 
  refine (fun m div_rec n Hlt => 
      match le_gt_dec n m with 
      | left H_n_le_m => 
          match div_rec (m-n) _ n _ with 
          | existT _ q (exist _ r H_spec) => 
                existT (div_type' m n)(S q)(exist (div_type'' m n (S q)) r _ ) end 
      | right H_n_gt_m => 
            existT (div_type' m n) O (exist (div_type'' m n O) m _ ) end );  
  unfold div_type'' ; lia. 
Defined.  

Definition div : forall m n, 0 < n -> {q & {r | m = q*n+r /\ r < n }} :=
  well_founded_induction lt_wf div_type div_F. 

Definition sqrt_F : 
  forall x, (forall y, y < x -> sqrt_type y) -> sqrt_type x. 
Proof. 
  destruct x. 
  - refine (fun sqrt_rec => existT _ 0 (exist _ 0 _ )); lia. 
  - unfold sqrt_type at 2. 
    refine (fun sqrt_rec => 
      let n := S x in 
      match div n 4 _ with 
      | existT _ q (exist _ r0 _ ) => 
          match sqrt_rec q _ with 
          | existT _ s' (exist _ r' H_spec) => 
              match le_gt_dec (S(4*s')) (4*r'+r0) with 
              | left HSs => 
                  let s := S(2*s') in 
                  let r := 4*r'+r0 - S(4*s') in 
                  existT(sqrt_type' n) s (exist (sqrt_type'' n s) r _ ) 
              | right Hs => 
                  let s := 2*s' in 
                  let r := 4*r'+r0 in 
                  existT(sqrt_type' n) s (exist (sqrt_type'' n s) r _ )  end end end); 
    unfold sqrt_type''; auto with zarith. 
Defined. 

Definition sqrt : forall n, {s & {r | n = s*s+r /\ n <(S s)*(S s)}} :=
  well_founded_induction lt_wf sqrt_type sqrt_F. 

Eval compute in 
  match sqrt 10 with 
  | existT _ s _ => s end . 

Eval compute in 
        match div 100 15 _ with 
        | existT _ q (exist _ r _ )   => (q,r) end . 


(* ex. 15.11 *) 
Definition sqrt_F' : 
  forall x, (forall y, y < x -> sqrt_type y) -> sqrt_type x. 
Proof. 
  destruct x. 
  - intros. exists 0. exists 0. auto with arith.  
  - intros sqrt_rec. set (S x) as n. fold n. 
    refine (match div n 4 _ with 
            | existT _ q (exist _ r0 _) => _ end ); auto with zarith. 
    + destruct (sqrt_rec q) as [s' [r' [H1' H2']]]; auto with zarith.  
      * { destruct (le_gt_dec (S(4*s')) (4*r'+r0)).   
        - exists (S(2*s')); exists (4*r'+r0-S(4*s')); auto with zarith.            
        - exists (2*s'   ); exists (4*r'+r0        ); auto with zarith. }
Defined.  

Definition sqrt' : forall n:nat, {s & { r | n = s*s+r /\ n < (S s)*(S s) }} :=
  well_founded_induction lt_wf sqrt_type sqrt_F'. 

Eval compute in  match sqrt' 10 with 
  existT _ s _ => s end. 



(* 15.3 ** General Recursion by Iteration *) 

(* 15.3.1 The Functional Related to a Recursive Function *)

Definition div_it_F (f:nat->nat->nat*nat) (m n:nat) :=
  match le_gt_dec n m with
  | left  _ => let (q,r) := f (m-n) n in (S q, r)
  | right _ => (O, m)                             end. 

(* 15.3.2 Termination Proof *)
Fixpoint iter {A} n (F:A->A) g := 
  match n with 
  | O     => g 
  | S p   => F (iter p F g) end. 

Definition div_it_terminates : 
  forall n m, 0<m -> 
  { v | exists p, forall k, p<k -> forall g, iter k div_it_F g n m = v }.
Proof. 
  induction n using (well_founded_induction lt_wf). 
  intros m Hlt0 . 
  case_eq (le_gt_dec m n); intros Hle Heqdec.  
  - case H with (y := n-m) (2 :=  Hlt0); try lia.  
    intros [q r] Hex. 
    exists (S q, r). 
    elim Hex; intros p Heq.  
    exists (S p). 
    intros k. 
    case k. 
    + now intros. 
    + intros k' Hplt g. simpl. 
      unfold div_it_F at 1. 
      rewrite Heq; auto with arith.  
      rewrite Heqdec; trivial.  
  - exists (0, n). exists 0. intros k.   
    case k. 
    + now intros. 
    + intros k' Hplt g. simpl.  
      unfold div_it_F at 1. 
      rewrite Heqdec. trivial.   
Defined. 

(* 15.3.3 Building the actual function *) 
Definition div_it n m (H:0<m) : nat * nat := 
  let (v,_) := div_it_terminates n m H in v. 


(* 15.3.4 Proving Fixpoint Equation *) 
Definition max m n : nat := 
  match le_gt_dec m n with left _ => n | right _ => m end.  

Theorem max1_correct : forall m n, m <= max m n. 
Proof. intros. unfold max; case (le_gt_dec m n); lia. Qed.   
Theorem max2_correct : forall m n, n <= max m n. 
Proof. intros. unfold max; case (le_gt_dec m n); lia. Qed.   

Hint Resolve max1_correct max2_correct : arith. 

Theorem div_it_fix_eqn : forall n m (h:0<m), 
  div_it n m h = match le_gt_dec m n with 
                 | left  Hle => let (q,r) := div_it (n-m) m h in (S q, r)
                 | right Hgt => (0,n) end. 
Proof. 
  intros n m h. 
  unfold  div_it. case (div_it_terminates n m h). 
  intros v  Hex1. case (div_it_terminates (n-m) m h).  
  intros v' Hex2.   
  elim Hex2; elim Hex1. intros p Heq1 p' Heq2.  
  rewrite <- Heq1 with (k := S(S(max p p')))( g := fun x y => v). 
  - rewrite <- Heq2 with (k :=   S(max p p')) ( g := fun x y => v). 
    + reflexivity.  
    + eauto with arith. 
  - eauto with arith. 
Qed. 
  
(* 15.3.5 Using the Fixpoint Equation *) 
Theorem div_it_correct1 : forall m n (h:0<n), 
  m = fst (div_it m n h) * n + snd (div_it m n h). 
Proof. 
  induction m using (well_founded_ind lt_wf). 
  intros. rewrite div_it_fix_eqn.  
  case (le_gt_dec n m); intros Hle; auto. 
  Check le_plus_minus. 
  pattern m at 1; rewrite (le_plus_minus n m); auto. 
  pattern (m-n) at 1.  
  rewrite H with (m-n) n h; auto with arith. 
  case (div_it (m-n) n h); simpl; auto with arith. 
Qed. 


(* ex. 15.16 *)
Theorem div_it_correct2 : forall m n (h:0<n), snd (div_it m n h) < n. 
Proof. 
  induction m using (well_founded_ind lt_wf). 
  intros. rewrite div_it_fix_eqn. 
  case (le_gt_dec n m); intros Hle; auto. 
  cut (m-n<m); auto with arith; intros. 
  set (H (m-n) H0 n h).  
  case_eq (div_it (m-n) n h). intros.   
  cut (snd (div_it (m-n) n h) = n1).  
  - intros. now rewrite <- H2.   
  - now rewrite H1. 
Qed. 




(* ex. 15.17 *) 

(* ex. 15.18 *) 



Require Import Recdef.   






(* 15.4 *** Recursion on an Ad Hoc Predicate *)


(* 15.4.1 Defining an Ad Hoc Predicate *)
(* We would like to define "log" function like; *) 
(* OCAML CODE: 
   let rec log x = match x with 
   | S O    -> O 
   | S(S p) -> S (log (S (div2 p)))     *)

Require Export CoqArt.chap09 . 
Print div2. 

Open Scope nat. 

Inductive log_domain : nat -> Prop :=
  | log_domain_1 : log_domain 1
  | log_domain_2 : forall p, log_domain(S(div2 p)) -> log_domain (S(S p)). 

Theorem log_domain_non_0 : forall x, log_domain x -> x <> O. 
Proof. intros. case H; intros; discriminate.  Qed. 

Print log_domain_non_0. 

Theorem log_domain_inv : forall x p, 
    log_domain x -> x = S(S p) -> log_domain (S (div2 p)).  
Proof. 
  intros x p H. case H.   
  - intros; discriminate. 
  - intros p' H1 Heq; injection Heq; intros Heq'; rewrite <- Heq'; assumption.   
(* not Qed. *) 
Defined. 

Fixpoint log x (h:log_domain x) : nat . 
Proof. 
  refine ( (match x as y return x = y -> nat with 
            | O     => _ 
            | S O   => fun h' => O 
            | S(S p)=> fun h' => S(log (S (div2 p)) _) end ) (refl_equal x)) . 
  - intros. apply False_rec. apply (log_domain_non_0 x h). assumption.     
  - apply log_domain_inv with x; assumption. 
Defined. 

Print log. 


Inductive log2_domain : nat->Prop :=
  | l21 : log2_domain 1
  | l22 : forall x, x<>1 -> x<>0 -> log2_domain (div2 x) -> log2_domain x. 

Theorem log2_domain_non_0 : forall x, log2_domain x -> x <> 0. 
Proof. intros. case H; intros.    
  - discriminate. 
  - assumption.  
Qed. 

Print log2_domain_non_0. 

Theorem log2_domain_inv : forall x, 
  log2_domain x -> x<>0 -> x<>1 -> log2_domain (div2 x). 
Proof. 
  intros x H. case H.  
  - intros. elim H1. reflexivity.      
  - intros. assumption. 
Defined.  

Fixpoint log2 x (h:log2_domain x) {struct h} : nat.  
Proof. 
  refine (match eq_nat_dec x 0 with 
          | left  heq => _ 
          | right neq =>  match eq_nat_dec x 1 with 
                          | left heq1    => O
                          | right hneq1  => S(log2(div2 x) _ ) end end ). 
  - apply False_rec. apply log2_domain_non_0 with x; assumption.     
  - apply log2_domain_inv; assumption.
Defined.  




Scheme log_domain_ind2 := Induction for log_domain Sort Prop. 

Fixpoint two_power n :=
  match n with 
  | O   => 1 
  | S p => 2 * two_power p end.  

Lemma mult2_div2_le : forall x, 2 * div2 x <= x. 
Proof. 
  induction x using nat_2_ind; auto with arith.   
  - simpl. lia. 
Qed.  

Theorem pow_log_le : 
  forall x (h:log_domain x), two_power (log x h) <= x. 
Proof. 
  intros x h. elim h using log_domain_ind2.  
  - simpl. auto with arith.   
  - intros. simpl. 
    apply le_trans with (2*S(div2 p)). 
    + lia.  
    + exact (mult2_div2_le (S(S p))).  
Qed. 


(* ex. 15.19 *) 
Lemma le_S_mult2_div2 : forall p, p <= S (2 * div2 p).  
Proof. 
  induction p using nat_2_ind; auto with arith. 
  - intros. simpl. lia.  
Qed. 

Theorem lt_pow_log : 
  forall x (h:log_domain x), x < two_power (S(log x h)). 
Proof. 
  intros x h. elim h using log_domain_ind2.  
  - simpl. auto with arith. 
  - simpl. intros.      
    set (S(div2 p)) as n. fold n. fold n in H.  
    set (two_power (log n l)) as t. fold t. fold t in H. 
    set (le_S_mult2_div2 p). lia.  
Qed. 


Fixpoint log' x (h:log_domain x) {struct h} : 
    {y | two_power y <= x /\ x < two_power (S y)}. 
Proof. 
  exists (log x h). 
  split. 
  - apply pow_log_le. 
  - apply lt_pow_log.  
Qed. 


(* ex. 15.20 *) 
(* ==> see hoare.v *) 
















    

    


Require Import Recdef.   



