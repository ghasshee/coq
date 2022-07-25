
(* 8.1.1 A Few Examples *) 
Require Import List  Arith .  
Import ListNotations. 

Inductive sorted {A} (R:A->A->Prop) : list A -> Prop := 
    | sorted0 : sorted R  [] 
    | sorted1 : forall x, sorted R [x] 
    | sorted2 : forall x y (l:list A), R x y -> sorted R(y::l)-> sorted R (x::y::l).

Inductive le n : nat -> Prop := 
    | le_n : le n n 
    | le_S : forall m:nat, le n m -> le n (S m) . 
Reset le. 

Hint Resolve le_n le_S sorted0 sorted1 sorted2 : sorted_base . 

Theorem sorted_nat_123 : sorted le (1 :: 2 :: 3 :: nil) . 
Proof.  auto with sorted_base arith.  Qed. 


(* ex 8.16 *) 

Section sorted'. 
  Variable A : Type. 
  Variable R : A -> A -> Prop. 
  Definition sorted' (l:list A) := forall l1 l2 x y, l = l1 ++ (x::y::l2) -> R x y.   

  Lemma sorted'1 : forall x, sorted' [x]. 
  Proof. 
    intros x l1 l2 n1 n2 Heq. induction l1; try now simpl. 
    + apply IHl1. injection Heq. now induction l1.  
  Qed. 
  
  Lemma sorted'2 : forall x y l, R x y->sorted' (y::l)-> sorted' (x::y::l).  
  Proof. 
    unfold sorted'; intros. 
    induction l1; injection H1; intros; subst; now try apply H0 with l1 l2. 
  Qed. 
  
  Lemma sorted'_weak : forall a l, sorted' (a::l) -> sorted' l. 
  Proof. intros a l H l1 l2 n1 n2 Heq. apply H with (a::l1)l2. now rewrite Heq. Qed. 

  Hint Resolve sorted'1 sorted'2 sorted'_weak : sort'. 
  
  Theorem sorted_equiv_sorted' : forall l, sorted R l <-> sorted' l. 
  Proof. 
      split.
      - induction 1; intros l1 l2 n1 n2 Heq. 
        + induction l1; discriminate Heq.  
        + induction l1 as [| a [| b l1]]; discriminate Heq. 
        + induction l1; injection Heq; intros; subst; eauto with sort'.  
      - intros Hsorted'. 
        induction l as [| a [| b l ]]; try constructor. 
          * now apply Hsorted' with [] l. 
          * eauto with sort'. 
  Qed.
End sorted'. 

(* ex. 8.28 *) 
Print sorted. 
Goal ~ sorted le (1::3::2::nil) . 
Proof. 
    red. 
    intros H. 
    inversion H. 
    inversion H4.  
    inversion H7. 
    inversion H11. 
    inversion H13. 
Qed. 


(* ex. 15.3 *) 

Reset sorted. 

Require Import Lia. 
Require Import List. 
Import ListNotations. 
Require Import Relations Orders. 



Section merge_sort. 
  Variable (A : Set) (Ale : A -> A -> Prop) (Ale_dec : forall x y, {Ale x y}+{~ (Ale x y)}). 
  Axiom Ale_eq : forall a b, Ale a b -> Ale b a -> a = b.  
  Axiom Ale_eq_dec : forall a b, Ale a b -> {a=b}+{~Ale b a}. 
  Axiom Ale_ordered : order A Ale. 
  Axiom not_Ale_Ale : forall a b, ~ Ale a b -> Ale b a. 

  Inductive sorted : list A ->  Prop := 
    | sorted_nil  : sorted [] 
    | sorted_uniq : forall a, sorted [a]
    | sorted_cons : forall a b l, Ale a b -> sorted (b::l) -> sorted (a::b::l) . 
    
  Hint Resolve 
    sorted_nil sorted_uniq sorted_cons : sort. 

  Lemma sorted_trans : forall a b l, sorted [a;b] -> sorted (b::l) -> sorted (a::b::l). 
  Proof.  intros; inversion H; auto with sort. Qed. 

  Lemma sorted_inv1 : forall a b l, sorted (a::b::l) -> sorted [a;b]. 
  Proof. intros; inversion H; auto with sort. Qed.  

  Lemma sorted_inv2 : forall a l, sorted (a::l) -> sorted l. 
  Proof. intros. inversion H; auto with sort. Qed.  

  Lemma sorted_inv3 : forall a b l, sorted (a::b::l) -> sorted (a::l). 
  Proof. intros. inversion H; inversion H4;subst; auto with sort. 
         destruct Ale_ordered; set (ord_trans _ _ _ H2 H7); auto with sort.  Qed. 

  Hint Resolve
    sorted_trans sorted_inv1 sorted_inv2 sorted_inv3 : sort. 

  Fixpoint merge_aux bound l1 l2 {struct bound} := 
    match bound with 
    | O   => [] 
    | S n => match l1 ,l2 with 
             | [], _        => l2  
             | _, []        => l1
             | a::l,b::k  => match Ale_dec a b with 
                               | left  H => a::merge_aux n l l2
                               | right H => b::merge_aux n l1 k end end end.

  Lemma unfold_merge_aux bound l1 l2 : merge_aux bound l1 l2 = 
    match bound with 
    | O   => [] 
    | S n => match l1 ,l2 with 
             | [], _        => l2  
             | _, []        => l1
             | a::l,b::k  => match Ale_dec a b with 
                               | left  H => a::merge_aux n l l2
                               | right H => b::merge_aux n l1 k end end end.
  Proof. now induction bound. Qed.  


  Compute length [1;2]. 

  Lemma len : forall (a:A) l, length (a::l) = S (length l).  
  Proof. now simpl. Qed.   
            
  Theorem merge_correct1 : 
    forall bound a b l l', 
    length (a::l) + length (b::l') <= bound -> 
    sorted (a::l) -> sorted (b::l') -> Ale a b -> 
    merge_aux (S bound) (a::l) (b::l') = a :: (merge_aux bound l (b::l')). 
  Proof. 
    intros n a b l l' Hle. 
    generalize n a b l l'.  
    induction Hle. 
    - intros. simpl. 
      case (Ale_dec a0 b0).     
      + trivial. 
      + intros. elim (n0 H1). 
    - intros. simpl.   
      case (Ale_dec a0 b0). 
      + trivial. 
      + intros. elim (n0 H1).  
  Qed. 

  Theorem merge_correct2 : 
    forall bound a b l l', 
    length (a::l') + length (b::l) <= bound -> 
    sorted (a::l') -> sorted (b::l) -> Ale a b -> 
    merge_aux (S bound) (b::l) (a::l') = a :: (merge_aux bound (b::l) l'). 
  Proof. 
    intros n a b l l' Hle. 
    inversion Hle. 
    - intros. 
      rewrite unfold_merge_aux. 
      case (Ale_dec b a); trivial.  
      + generalize l l' a b H0 H1 H2.
        induction l0. 
        * intros. 
          rewrite (Ale_eq _ _ a1 H5) in * |- *. 
          inversion H3; subst; trivial. 
          rewrite unfold_merge_aux. 
          rewrite unfold_merge_aux. 
          case (Ale_dec a0 b1); tauto. 
        * intros.  
          rewrite unfold_merge_aux. 
          rewrite (unfold_merge_aux (length _ + _  )). 
          inversion H4; subst.  
          rewrite (Ale_eq _ _ a2 H5) in * |- *. clear a2 H5.  
          case (Ale_dec a0 a1); try tauto.  
          -- intros. 
             simpl (length _ + _ )      in * |- *. 
             rewrite <- plus_n_Sm       in * |- *. 
             rewrite (Ale_eq _ _ a2 H8) in * |- *. clear a2 H8. 
             rewrite (IHl0 l'0); try inversion H4; try tauto.  
             ++ induction l'0; try tauto.
                inversion H3; subst.  
                case (Ale_dec a1 a3); try tauto.  
          -- intros.   
             induction l'0; try tauto. 
             ++ case (Ale_dec a1 a2); try tauto. 
                ** inversion H3; intros; tauto.  
    - subst.  
      intros. 
      rewrite unfold_merge_aux. 
      case (Ale_dec b a); trivial. 
      + generalize H0 H1 H2 H.  
        generalize l l' a b m.
        induction l0. 
        * intros. 
          rewrite (Ale_eq _ _ a1 H5) in * |- *. 
          inversion H3; subst; trivial. 
          rewrite unfold_merge_aux. 
          rewrite unfold_merge_aux. 
          case (Ale_dec a0 b1); try tauto. 
          inversion H6; try tauto.  
        * intros.  
          rewrite unfold_merge_aux. 
          rewrite (unfold_merge_aux (S _ )). 
          inversion H4; subst.  
          rewrite (Ale_eq _ _ a2 H5) in * |- *. clear a2 H5.  
          case (Ale_dec a0 a1); try tauto.  
          -- intros. 
             simpl (S _) in IHl0. 
             simpl (length _ + _ ) in * |- * . 
             rewrite <- plus_n_Sm in * |- *. 
             rewrite (Ale_eq _ _ a2 H9) in * |- *. clear a2 H9. 
             inversion H6; try tauto.  
             ++ rewrite (IHl0); try inversion H4; try tauto.    
                ** induction l'0; try tauto.  
                   clear IHl'0. 
                   inversion H3; subst. 
                   case (Ale_dec a1 a3); try tauto.  
                ** trivial. 
             ++ rewrite (IHl0 l'0); try inversion H4; try tauto.  
                ** induction l'0; try tauto.
                   clear IHl'0. 
                   inversion H3; subst.  
                   case (Ale_dec a1 a3); try tauto.  
                ** inversion H5; subst; try lia.     
          -- intros.   
             induction l'0; try tauto. 
             ++ inversion H6; trivial.  
             ++ case (Ale_dec a1 a2); try tauto. 
                ** inversion H3; intros; tauto.  
  Qed. 

  Definition merge l1 l2 := merge_aux (S(length l1 + length l2)) l1 l2. 


  Lemma merge_weak : forall a l k, sorted l -> sorted (a::k) -> 
    sorted (merge l (a::k)) -> sorted (merge l k) . 
  Proof. 
    unfold merge. 
    simple induction l. 
    - induction k; simpl; intros; inversion H0; auto with sort.   
    - intros b l' Hrec k Hsorted_bl' Hsorted_ak Hsorted_bl'ak . 
      case (Ale_dec b a).
      + intros.  
        rewrite merge_correct1 in Hsorted_bl'ak; auto with sort.  
        apply sorted_inv2      in Hsorted_bl'ak. 
        apply Hrec             in Hsorted_bl'ak; inversion Hsorted_bl'; auto with sort. 
        * subst.  
          induction k; simpl; auto with sort.  
          -- case (Ale_dec b a1); inversion Hsorted_ak.    
             ++ intros. auto with sort.  
             ++ destruct (Ale_ordered). set (ord_trans _ _ _ a0 H1). tauto. 
        * subst.  
          induction k; try now simpl. 
          -- case (Ale_dec b0 a1); intros. 
             ++ rewrite merge_correct1; auto with sort.  
                ** simpl (length _ + _ ) in * |- *.     
                   rewrite merge_correct1; auto with sort. 
                   --- constructor; auto with sort.  
                       rewrite merge_correct1 in Hsorted_bl'ak; auto with sort. 
                       now inversion Hsorted_ak. 
                   --- now inversion Hsorted_ak.  
                ** now inversion Hsorted_ak.  
                ** destruct (Ale_ordered). set (ord_trans _ _ _ H1 a2). tauto. 
             ++ inversion Hsorted_ak. subst. 
                destruct (Ale_ordered). set (ord_trans _ _ _ a0 H3). 
                rewrite merge_correct1; auto with sort. 
                ** simpl (length _ + _ ) in * |- *.     
                   rewrite merge_correct2; auto with sort. 
                   --- constructor; auto with sort. 
                       rewrite merge_correct2 in Hsorted_bl'ak; auto with sort. 
                       +++ simpl. lia.   
                       +++ now set (not_Ale_Ale _ _ n). 
                   --- simpl. lia.  
                   --- now set (not_Ale_Ale _ _ n). 
      + intros.  
        rewrite merge_correct2 in Hsorted_bl'ak; auto with sort.  
        * simpl (length _ + _) in * |- *.  
          rewrite <- plus_n_Sm in * |- *. 
          now apply sorted_inv2 in Hsorted_bl'ak. 
        * simpl. lia.  
        * now set (not_Ale_Ale _ _ n).  
  Qed. 


  Theorem merge_sorted l1 l2 : sorted l1 -> sorted l2 -> sorted (merge l1 l2). 
  Proof. 
    unfold merge. intros. 
    induction H; induction H0; try now (simpl; auto with sort). 
    - simpl; case (Ale_dec a a0). 
      + intros. auto with sort. 
      + intros. set (not_Ale_Ale _ _ n); auto with sort.  
    - rewrite unfold_merge_aux. case (Ale_dec a a0).  
      + simpl. intros. auto with sort.  
      + simpl . 
        simpl in IHsorted. 
        generalize IHsorted.  
        case (Ale_dec a b). 
        * intros. 
          set (not_Ale_Ale _ _ n). 
          auto with sort. 
        * intros.  
          set (not_Ale_Ale _ _ n). 
          auto with sort. 
    - rewrite unfold_merge_aux. case (Ale_dec a a0).  
      + simpl in * |- *.  
        intros. generalize IHsorted. 
        case (Ale_dec b a0); auto with sort. 
      + simpl.    
        intros. set (not_Ale_Ale _ _ n); auto with sort.  
    - case (Ale_dec a a0); intros.
      + rewrite merge_correct1; auto with sort. 
        generalize IHsorted. clear IHsorted.  
        simpl (length _ + _ ). 
        rewrite (unfold_merge_aux (S(S _))). 
        case (Ale_dec b a0); auto with sort.  
      + set (not_Ale_Ale _ _ n). 
        rewrite merge_correct2; auto with sort; try lia. 
        generalize IHsorted0. clear IHsorted0.
        simpl (length _ + _ ). 
        repeat rewrite <- plus_n_Sm. 
        rewrite (unfold_merge_aux (S(S(S(S _))))). 
        case (Ale_dec a b0); auto with sort; intros. 
        * apply merge_weak in IHsorted; auto with sort. 
          -- constructor; auto with sort.   
             apply IHsorted0. clear IHsorted0.  
             unfold merge in IHsorted. 
             simpl (length _ + _ ) in IHsorted. 
             now rewrite <- plus_n_Sm in IHsorted. 
        * constructor; auto with sort.  
          apply IHsorted0. clear IHsorted0.   
          apply merge_weak in IHsorted; auto with sort. 
             unfold merge               in IHsorted. 
             simpl (length _ + _ )      in IHsorted. 
             now rewrite <- plus_n_Sm   in IHsorted. 
  Qed.  





  (*

  Lemma merge_app : forall n l l' k k', n <> 0 ->  
    merge_aux n l k = merge_aux n l' k' -> merge_aux (S n) l k = merge_aux (S n) l' k'. 
  Proof. Abort. 

  Lemma merge_sym : forall n l k, length k + length l < n -> merge_aux n l k = merge_aux n k l. 
  Proof. Abort. 

  Lemma merge1 : forall n a b l k, Ale a b -> 
    length (a::l) + length (b::k) < n -> 
    merge_aux (S n)(a::l) (b::k) = a :: merge_aux n l(b::k).
  Proof. Abort. 
  Lemma merge2 : forall n a b c l k, 
    ~ Ale a c -> Ale c b -> 
    merge_aux (S n)(c::a::l)(b::k) = merge_aux(S n)(a::l)(c::b::k).
  Proof. 
    simpl. intros.  
    case (Ale_dec c b); case (Ale_dec a c); tauto.
  Qed. 

  Lemma merge2' : forall n a b c l k, 
    length (a::l) + length (b::k) < n ->
    Ale c a -> Ale c b -> 
    merge_aux n (c::a::l)(b::k) = merge_aux n (a::l)(c::b::k).
  Proof. Abort. 
   *)


End merge_sort. 


Require Import Extraction. 

Extraction "extract/merge_sort.ml" merge. 

