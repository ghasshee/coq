Require Import List. 
Import ListNotations. 

(* ex. 8.5 *)
Inductive par : Set := open | close . 

Definition expr := list par . 

Inductive wp : expr -> Prop := (* wp := well-parenthesized *) 
    | wp_empty : wp [] 
    | wp_wrap  : forall e, wp e -> wp (open :: e ++ [close]) 
    | wp_cat   : forall e e', wp e -> wp e' -> wp (e++e') . 

Lemma wp_oc : wp [open;close] . Proof. apply (wp_wrap []); constructor. Qed. 

Hint Resolve wp_empty wp_wrap wp_cat wp_oc : paren.  

Lemma wp_o_head_c : forall l1 l2:expr, wp l1->wp l2->wp(open::(l1++(close::l2))). 
Proof. 
    intros. 
    SearchRewrite (_::_++_). rewrite (app_comm_cons l1 (close::l2) open). 
    SearchRewrite (_++_).    rewrite <- (firstn_skipn 1 (close ::l2) ) .  
    simpl (skipn  1 (close :: l2)).   
    simpl (firstn 1 (close :: l2)). 
    SearchRewrite (_++_++_). rewrite app_assoc,<-(app_comm_cons l1 [_] _). 
    apply (wp_cat (open::l1 ++ [close]) l2); auto with paren. 
Qed. 

Lemma wp_o_tail_c : forall l1 l2, wp l1 -> wp l2 -> wp (l1++(open::(l2++[close]))) . 
Proof. now repeat constructor. Qed. 

Hint Resolve wp_o_tail_c wp_o_head_c : paren. 
(* end 8.5 *)


(* ex. 8.6 *) 
Inductive bin := 
    | L : bin 
    | N : bin -> bin -> bin . 

Fixpoint bin_to_string t : expr := 
    match t with 
    | L     => []
    | N l r => open :: (bin_to_string l ++ (close :: bin_to_string r))  end. 

Lemma wp_bin : forall t, wp (bin_to_string t) . 
Proof.  induction 0; simpl; auto with paren.  Qed. 

(* ex. 8.7 *) 
Fixpoint bin_to_string' t : expr := 
    match t with 
    | L     => []
    | N l r => bin_to_string' l ++ (open :: (bin_to_string' r ++ [close]))  end. 

Lemma wp_bin' : forall t, wp (bin_to_string' t) . 
Proof. induction 0; simpl; auto with paren. Qed.  



(* ex. 8.19 *)
Inductive wp' : list par -> Prop :=
    | wp'_nil : wp' []
    | wp'_cons : forall l1 l2, wp' l1 -> wp' l2 -> wp' (open :: (l1 ++ (close :: l2))). 

Lemma wp'_app : forall l1 l2, wp' l1 -> wp' l2 -> wp' (l1 ++ l2). 
Proof. 
    intros l1 l2 Hwp1 Hwp2. 
    induction Hwp1.
    - now simpl. 
    - simpl. rewrite <- app_assoc. simpl. 
      now constructor. 
Qed. 

Lemma wp'_wp : forall l, wp' l -> wp l. 
    intros. induction H. 
    - apply wp_empty. 
    - rewrite app_comm_cons,<- (firstn_skipn 1(close ::l2)), app_assoc. simpl. 
      rewrite app_comm_cons. 
      apply wp_cat.  
      + now apply wp_wrap.
      + assumption. 
Qed. 

Lemma wp_wp' : forall l, wp l -> wp' l. 
    intros. induction H.     
    - constructor. 
    - now repeat constructor.   
Restart. 
    intros. induction H. 
    - apply wp'_nil. 
    - apply wp'_cons. 
      + assumption . 
      + apply wp'_nil.
    - now apply wp'_app. 
Qed.

Theorem wp'_eq_wp : forall l, wp' l <-> wp l. 
Proof. 
    split; [ apply wp'_wp | apply wp_wp' ].   
Qed. 


(* ex. 8.20 *)
Inductive wp'' : list par -> Prop :=
    | wp''_nil  : wp'' nil
    | wp''_cons : forall l1 l2, wp'' l1 -> wp'' l2 -> wp'' (l1 ++ open :: l2 ++ [close]) . 

Lemma wp''_app : forall l1 l2, wp'' l1 -> wp'' l2 -> wp'' (l1 ++ l2). 
Proof. 
    intros l1 l2 Hwp1 Hwp2. 
    induction Hwp2. 
    - now rewrite <- app_nil_end.  
    - rewrite app_assoc. 
      now constructor. 
Qed. 

Lemma wp''_wp : forall l, wp'' l -> wp l. 
Proof. 
    intros; induction H. 
    - constructor . 
    - rewrite app_comm_cons. 
      now repeat constructor.  
Qed. 

Lemma wp_wp'' : forall l, wp l -> wp'' l. 
    intros; induction H.     
      + constructor. 
      + apply (wp''_cons [] e); [ constructor | trivial ] .   
      + now apply wp''_app. 
Qed. 

Theorem wp''_eq_wp : forall l, wp'' l <-> wp l. 
Proof.  split; [ apply wp''_wp | apply wp_wp'' ].   Qed. 


(* ex. 8.21 *) 
Fixpoint recognize (n:nat) (l:list par) {struct l} : bool :=
    match l with 
    | []        =>  match n with 
                    | O     => true
                    | _     => false end 
    | open ::l' =>  recognize (S n) l' 
    | close::l' =>  match n with 
                    | O     => false 
                    | S n'  => recognize n' l' end 
    end. 

Lemma recognize_complete_aux : 
    forall l: expr, wp l -> forall n l', recognize n (l++l') = recognize n l'. 
Proof. 
  intros l Hwp.  
  induction Hwp; simpl; intros;  
  [ | rewrite <- app_assoc, IHHwp | rewrite <- app_assoc, IHHwp1, IHHwp2 ]; auto. 
Qed. 

Theorem recognize_complete : 
    forall l, wp l -> recognize 0 l = true. 
Proof. 
    intros. 
    induction H; try trivial; simpl; now rewrite recognize_complete_aux.   
Qed. 


(* ex. 8.22 *)
Definition wp_o_c := wp_wrap [] wp_empty. 

Lemma recognize_succ : forall n l, recognize n l = true -> recognize (S n) l = false. 
Proof.
    intros n l. generalize n. clear n. 
    induction l.  
    - trivial. 
    - simpl. induction a.  
      + intros. now apply IHl.   
      + induction n.  
        * discriminate. 
        * intros. now apply IHl .  
Qed. 

Fixpoint opens (n:nat) : expr := 
    match n with 
    | O     => []
    | S n'  => open :: opens n' end. 

Lemma opens_open : forall n l, opens n ++ open::l = opens (S n) ++ l.  
Proof. intros; induction n; simpl; [ trivial | now rewrite IHn ]. Qed. 
Lemma open_opens : forall n l, open :: opens n ++ l = opens (S n) ++ l.  
Proof. intros; induction n; simpl; [ trivial | now rewrite IHn ]. Qed.        
Lemma opens_close : forall n l, opens(S n) ++ close::l = opens n ++ [open;close] ++ l . 
Proof. intros; induction n; simpl; [ trivial | now rewrite opens_open ]. Qed.  
Lemma cons_app : forall {A:Set} (a:A) l, a :: l = [a] ++ l.  
Proof.  intros. trivial. Qed. 
Lemma discriminate_last_1 : forall l1 l2, l1++[close] = l2++[open] -> False. 
Proof. 
    intros l1. induction l1; simpl; intros.  
    - induction l2; simpl in H; intros. 
      + elim H; discriminate.   
      + induction a; elim H; try discriminate. 
        * induction l2; discriminate H.   
    - induction l2; simpl in H; intros. 
      + induction a; elim H; try discriminate.  
        * induction l1; discriminate H.  
      + injection H; intros. subst a0. 
        now apply IHl1 in H0.  
Qed.  
Lemma wp_opens_false : forall n, wp(opens (S n)) -> False.
Proof. 
    induction n; intros; apply wp_wp'' in H; inversion H. 
    - rewrite <-(app_nil_l[open]),app_comm_cons, app_assoc in H0. 
      now apply discriminate_last_1 in H0. 
    - rewrite (app_nil_end (opens n)), open_opens, <- opens_open, 
                app_comm_cons, app_assoc,app_comm_cons in H0. 
      now apply discriminate_last_1 in H0. 
Qed. 

(* List Lemmas *) 
Check app_inv_tail. 
Check app_comm_cons. 
Check app_nil_r. 
Check app_nil_l. 
Check app_assoc. 
Lemma hd_hd_app : forall A (a b:A)l, a::b::l = [a;b]++l. 
Proof. now induction l. Qed. 
Lemma app_cons : forall A l (a:A) l', l ++ a :: l' = (l ++ [a]) ++ l'. 
Proof. intros. induction l; intuition. simpl. now rewrite IHl. Qed. 
Lemma list_last_neq : forall{A} (a b:A) l1 l2, a <> b -> ~ l1++[a] = l2++[b] . 
Proof. 
  simple induction l1; red; intros.
  - induction l2; simpl in *.   
    + now injection H0.   
    + now induction l2.    
  - induction l2; simpl in *.  
    + now induction l.    
    + inversion H1. subst. injection H1. now apply (H l2).   
Qed. 

Hint Resolve app_inv_tail : list.
Hint Rewrite 
          app_comm_cons app_nil_r app_nil_l app_assoc : list. 


Lemma wp_o_c_l_wp_l : forall l, wp (open::close::l) -> wp l. 
Proof. 
    intros. apply wp_wp' in H. apply wp'_wp. 
    inversion H. 
    induction l1. 
    - simpl in H0. 
      injection H0. intros. now subst l.  
    - injection H0. intros. subst a l.    
      inversion H1. 
Qed. 
Lemma wp_l_wp_o_c_l : forall l, wp l -> wp (open::close::l). 
Proof. 
  intros. set (wp_cat [open;close] l). simpl in w. 
  apply w; auto with paren.   
Qed. 

Lemma wp_l_o_c_wp_l : forall l, wp(l++[open;close]) -> wp l. 
Proof. 
    intros. apply wp_wp'' in H. apply wp''_wp. 
    inversion H. 
    - now induction l.   
    - inversion H2. subst. simpl in *.   
      + apply app_inv_tail in H0. now subst. 
      + subst. 
        rewrite <- (app_nil_l [close]) in H0 at 3. 
        rewrite (app_comm_cons [] [close] open) in H0. 
        repeat rewrite app_assoc in H0. 
        rewrite app_comm_cons in H0. 
        repeat rewrite app_assoc in H0. 
        apply app_inv_tail in H0. 
        repeat rewrite app_comm_cons in H0. 
        repeat rewrite app_assoc in H0. 
        now apply list_last_neq in H0. 
Qed.

Lemma list_app_eq_inv : forall {A} (l1 l2 k1 k2:list A), 
    l1 ++ l2 = k1 ++ k2 -> 
    (exists k11 k12, l1 = k11  /\  l2 = k12++k2) \/ 
    (exists k21 k22, l1 = k1++k21  /\  k2 = k22) . 
Proof. 
  intros A l1 l2 k1 k2. revert l1 l2 k2.  
  induction k1; simpl; intros.  
  - right. now exists l1, k2.  
  - destruct l1; simpl in *. 
Abort. 

Lemma wp_o_c_middle : forall l l1 l2, wp l -> l = l1 ++ l2 -> wp(l1++open::close::l2). 
Proof. 
  intros. revert l1 l2 H0. 
  apply wp_wp' in H.   
  induction H; simpl; intros; apply wp'_wp. 
  - cut (open :: close :: l2 = open :: [] ++ close :: l2); auto with paren.   
    intros. rewrite H.   
    now (destruct l1; destruct l2; repeat constructor).    
Abort. 

Lemma wp_l_o_c_l'_wp_l_l' : forall l l', wp(l++open::close::l') -> wp (l ++ l'). 
Proof. 
  intros l l'; generalize l; induction l'; simpl; intros. 
  - rewrite app_nil_r. now apply wp_l_o_c_wp_l.  
  - rewrite app_cons. 
    apply IHl'.  
Abort. 

Lemma cons_wp_false : forall a l, wp l -> wp(a::l) -> False. 
Proof. 
    intros.
    apply recognize_complete    in H. 
    apply recognize_complete    in H0.  simpl in H0. 
    apply (recognize_succ 0 l ) in H . 
    induction a; try rewrite H in H0; discriminate H0.  
Qed.
Lemma head_last_nil : forall {A} (l1 l2 l3:list A) , [] = l1++l3  -> l2 = l1 ++ l2 ++ l3 .  
Proof. 
    intros. 
    induction l1. 
    - simpl in H. subst l3. 
      simpl. rewrite <- app_nil_end.   
      trivial. 
    - discriminate H.  
Qed. 
Lemma incr_o_recognize : forall n l, recognize(S n)l=true -> recognize n(open::l)=true.  
Proof.  induction n; trivial.  Qed. 
Lemma incr_c_recognize : forall n l, recognize n l=true -> recognize(S n)(close::l)=true. 
Proof. induction n; simpl; intros; trivial. Qed.  


Print wp'. 
(*
Fixpoint from_wp'_proof (l:expr) (H:wp' l):Prop := 
    match H with 
    | wp'_nil               => [] = l
    | wp'_cons l1 l2 H1 H2  => open::l1++close::l2 = l 
    end. 
*)
Print ex. 


Fixpoint wrap l (H:wp' l) := 
    match H with 
    | wp'_nil                   => wp'_cons _ _ H wp'_nil
    | wp'_cons _ _ _ _          => wp'_cons _ _ H wp'_nil end . 

Fixpoint head (l:expr) := 
    match l with 
    | []            => []
    | x::y::[]      => [x]
    | x::xs         => x::(head xs) end. 

Fixpoint add_o_c' (l:expr) (H:wp' l) := 
    match H return exists y, wp' y with 
    | wp'_nil                   =>  ex_intro _ (open::l++close::l) (wp'_cons _ _ H H)
    | wp'_cons l1 l2 H1 H2      =>  match add_o_c' l1 H1 with 
                                    | ex_intro _ l1' H1' => 
                                        ex_intro _(open::l1'++close::l2)(wp'_cons _ _ H1' H2) end   end.  

Ltac hoge H := 
    match H with 
    | ex_intro _ _ ?x       => apply x      end. 


Lemma recognize_sound_aux : 
    forall n l, recognize n l = true -> wp (opens n ++l) . 
Proof. 
  intros n l. generalize n. clear n.  
  induction l; simpl; intros. 
  - induction n; now auto with paren.       
  - destruct a.  
    + rewrite opens_open. now apply IHl.   
    + induction n.  
      * discriminate H. 
      * rewrite <- opens_open. 


Restart. 
    intros n l. generalize n. clear n. 
    induction l.  
    - simpl. intros. constructor; try constructor.   
      + induction n; simpl. try constructor. 
        * discriminate H.   
    - intros. induction a; simpl. 
      + rewrite opens_open. 
        induction l; simpl.   
        * discriminate.
        * induction a; rewrite open_opens; apply IHl; simpl; simpl in H; trivial.  
      + induction n; simpl in H.   
        * discriminate. 
        * apply IHl in H.  
          apply wp_wp' in H. 
          rewrite <- opens_open . 
          set (add_o_c' (opens n++l) H) as H'. 

        (* #TODO now exact (add_o_c (opens n::l) H).  with equivalence wp' <-> wp  *) 

Restart. 
    intros n l. generalize n. clear n. 
    induction l.  
    - simpl. intros. constructor; try constructor.   
      + induction n; simpl. try constructor. 
        * discriminate H.   
    - Print recognize.  
      intros. induction a; simpl. 
      + rewrite opens_open. 
        induction l; simpl.   
        * discriminate.
        * induction a; rewrite open_opens; apply IHl; simpl; simpl in H; trivial.  
      + induction n; simpl in H.   
        * discriminate. 
        * induction l.   
          ** induction n. 
             *** simpl. exact (wp_wrap [] wp_empty). 
             *** discriminate.  
          ** induction a.    
              *** simpl in H. 
                  apply IHl in H.
                  (* #TODO now exact (add_o_c (opens n++open::l) H).  *) 

Abort. 

Theorem recognize_sound :  forall l, recognize 0 l = true -> wp l . 
Proof. 
Abort. 





(* ex. 8.23 *)



(* ex 8.24 *)
Inductive parse_rel : expr -> expr -> bin -> Prop :=
    | parse_node : forall (l1 l2 l3:expr) (t1 t2:bin), parse_rel l1 (close::l2) t1 -> parse_rel l2 l3 t2 -> parse_rel (open::l1) l3 (N t1 t2). 




