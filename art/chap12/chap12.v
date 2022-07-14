Require Import Arith ZArith . 


Module Type DICT. 
    Parameters key data dict : Type .
    Parameter empty : dict . 
    Parameter add   : key -> data -> dict -> dict. 
    Parameter find  : key -> dict -> option data. 

    Axiom empty_def : forall k:key, find k empty = None. 
    Axiom success   : forall (d:dict)(k:key)(v:data), find k (add k v d) = Some v. 
    Axiom diff_key  : forall (d:dict)(k k':key)(v:data), 
            k <> k' -> find k (add k' v d) = find k d . 
End DICT. 


Module Type DICT_PLUS. 
    Declare Module Dict : DICT. 
    Parameter build : list (Dict.key * Dict.data) -> Dict.dict . 
End DICT_PLUS. 


Module Type KEY. 
    Parameter A : Type. 
    Parameter eqdec : forall a b:A, {a = b} + {a <> b} . 
End KEY.


Open Scope Z_scope. 
Module ZKey : KEY . 
    Definition A:=Z. 
    Definition eqdec := Z.eq_dec. 
End ZKey . 

(* Check (ZKey.eqdec (9*7)(8*8)).  *) (* error ZKey.A <> Z *) 
Print ZKey.eqdec. 
Reset ZKey. 

Module ZKey <: KEY . 
    Definition A:=Z. 
    Definition eqdec := Z.eq_dec. 
End ZKey . 

Print ZKey.eqdec. 
Reset ZKey. 

Module Type ZKEY := KEY with Definition A := Z. 
Module ZKey : ZKEY. 
    Definition A := Z.
    Definition eqdec := Z.eq_dec. 
End ZKey. 

Check (ZKey.eqdec (9*7)(8*8)). 

Module NatKey : KEY with Definition A:=nat. 
    Definition A := nat. 
    Definition eqdec := eq_nat_dec. 
End NatKey. 




Require List. 

Module LKey (K:KEY) : KEY with Definition A := list K.A . 
    Definition A := list K.A . 
    Definition eqdec : forall a b:A, {a=b}+{a<>b} . 
    simple induction a. 
    - induction b; [now left | now right].  
    - intros a0 k Ha; induction b. 
      + now right. 
      + case (K.eqdec a0 a1); intro; 
        try case (Ha b); intro; subst; 
        try tauto; right; red; now injection 1.   
    Defined. 
End LKey. 




Locate order. 
Require Import Relations.       Print order. 

Require Import Orders.          Print order. 



Module Type DEC_ORDER. 
    Parameter A     : Type. 
    Parameter le    : A -> A -> Prop. 
    Parameter lt    : A -> A -> Prop.
    Axiom ordered           : order A le. 
    Axiom lt_le_weak        : forall a b, lt a b -> le a b. 
    Axiom lt_diff           : forall a b, lt a b -> a <> b. 
    Axiom le_lt_or_eq       : forall a b, le a b -> lt a b \/ a = b . 
    Parameter lt_eq_lt_dec  
                    : forall a b, {lt a b}+{a = b}+{lt b a}. 
End DEC_ORDER. 



Module Type MORE_DEC_ORDERS. 
    Parameter A     : Type. 
    Parameter le    : A -> A -> Prop. 
    Parameter lt    : A -> A -> Prop. 

    Axiom le_trans          : transitive A le. 
    Axiom le_refl           : reflexive  A le.
    Axiom le_antisym        : antisymmetric A le. 
    Axiom lt_irreflexive    : forall a, ~ lt a a. 
    Axiom lt_trans          : transitive A lt. 
    Axiom lt_not_le         : forall a b, lt a b -> ~ le b a. 
    Axiom le_not_lt         : forall a b, le a b -> ~ lt b a. 
    Axiom lt_intro          : forall a b, le a b -> a <> b -> lt a b. 

    Parameter le_lt_dec     : forall a b, {le a b}+{lt b a}. 
    Parameter le_lt_eq_dec  : forall a b, le a b -> {lt a b}+{a = b}. 
End MORE_DEC_ORDERS. 


Module More_Dec_Orders (P:DEC_ORDER) : MORE_DEC_ORDERS 
                                        with Definition A   := P.A
                                        with Definition le  := P.le 
                                        with Definition lt  := P.lt. 
    Definition A    := P.A. 
    Definition le   := P.le. 
    Definition lt   := P.lt. 

    Theorem le_trans : transitive A le. 
    Proof.  case P.ordered. now intros.     Qed. 

    Theorem le_refl : reflexive A le. 
    Proof.  case P.ordered. now intros.     Qed. 

    Theorem le_antisym : antisymmetric A le. 
    Proof.  case P.ordered. now intros.     Qed. 

    Theorem lt_intro : forall a b, le a b -> a<>b -> lt a b. 
    Proof.  intros. case (P.le_lt_or_eq a b); now intros.   Qed. 

    Theorem lt_irreflexive : forall a, ~ lt a a. 
    Proof.  intros a H. case (P.lt_diff a a); auto.         Qed. 

    Theorem lt_not_le : forall a b, lt a b -> ~ le b a.  
    Proof. 
        intros a b H Hba.  
        set (P.lt_le_weak a b H) as Hab.  
        case P.ordered; unfold antisymmetric; intros. 
        set (ord_antisym a b Hab Hba). 
        case (P.lt_diff a b); auto.  
    Qed. 

    Theorem le_not_lt : forall a b, le a b -> ~ lt b a. 
    Proof. 
        intros a b Hab H. 
        case P.ordered; unfold antisymmetric; intros. 
        set (P.lt_le_weak b a H) as Hba. 
        set (ord_antisym a b Hab Hba). 
        set (P.lt_diff b a H). auto. 
    Qed. 

    Theorem lt_trans : transitive A lt. 
    Proof. 
        case P.ordered; intros _ trans _ x y z ltxy ltyz. 
        set (P.lt_le_weak x y ltxy)     as Hxy. 
        set (P.lt_le_weak y z ltyz)     as Hyz. 
        set (trans x y z Hxy Hyz)       as Hxz. 
        set (P.le_lt_or_eq x z)         as orxz.   
        destruct orxz; auto. 
        - subst. set (lt_not_le z y ltxy) as nyz.  
          now set (nyz Hyz). 
    Qed. 

    Definition le_lt_dec : forall a b, {le a b}+{lt b a}. 
        intros a b; case (P.lt_eq_lt_dec a b). 
        - intro D; case D. 
          + left. now apply P.lt_le_weak.   
          + intros. subst. left. apply le_refl. 
        - now right. 
    Defined. 

    Definition le_lt_eq_dec : forall a b, le a b -> {lt a b}+{a = b}. 
        intros a b; case (P.lt_eq_lt_dec a b); intros.  
        - assumption. 
        - set (le_not_lt a b H) as not_lt.  
          now set (not_lt l).  
    Defined.  
         
End More_Dec_Orders. 
        


Module Lexico (D1:DEC_ORDER)(D2:DEC_ORDER) <: 
            DEC_ORDER with Definition A := (D1.A * D2.A)%type. 

    Open Scope type_scope. 
    
    Module M1 := More_Dec_Orders D1. 
    Module M2 := More_Dec_Orders D2. 

    Definition A            :=  D1.A * D2.A. 
    Definition le (a b:A)   :=  let (a1,a2) := a in 
                                let (b1,b2) := b in 
                                D1.lt a1 b1 \/ a1 = b1 /\ D2.le a2 b2. 
    Definition lt (a b:A)   :=  let (a1,a2) := a in 
                                let (b1,b2) := b in 
                                D1.lt a1 b1 \/ a1 = b1 /\ D2.lt a2 b2. 

    Lemma refl : reflexive A le. 
    Proof. case D1.ordered, D2.ordered. red. destruct x. simpl. right. now split. Qed. 

    Lemma trans : transitive A le. 
    Proof. 
        case D1.ordered, D2.ordered. red; intros. 
        destruct x as (a1,b1), y as (a2,b2), z as (a3,b3). 
        case H, H0; intros. 
        - left. now apply (M1.lt_trans a1 a2 a3). 
        - destruct H0. subst. now left.     
        - destruct H.  subst. now left.     
        - destruct H, H0. right. split. 
          + now subst.  
          + now apply (ord_trans0 b1 b2 b3).  
    Qed.  
    
    Lemma antisym : antisymmetric A le. 
    Proof. 
        case D1.ordered; case D2.ordered. red; intros.
        destruct x as (a1,b1), y as (a2,b2). 
        case H, H0; intros.  
        - set (D1.lt_le_weak a1 a2 H). apply M1.le_not_lt in l. tauto. 
        - destruct H0. subst. now apply M1.lt_irreflexive in H. 
        - destruct H.  rewrite H in H0. now apply M1.lt_irreflexive in H0. 
        - destruct H, H0. subst. set(ord_antisym b1 b2 H1 H2). now rewrite e. 
    Qed. 

    Theorem ordered : order A le. 
    Proof. split; [ apply refl | apply trans | apply antisym ]. Qed.  

    Theorem lt_le_weak : forall a b, lt a b -> le a b. 
    Proof. 
        red; intros; destruct a, b; case H; intros; try tauto. 
        - right. destruct H0. split; [ auto | now apply D2.lt_le_weak ].   
    Qed. 

    Theorem lt_diff : forall a b, lt a b -> a <> b.  
    Proof. 
        compute; intros. subst. destruct b. repeat destruct H.   
        - now apply (D1.lt_diff a a H ).  
        - now apply (D2.lt_diff a0 a0 H0).  
    Qed.  
    
    Theorem le_lt_or_eq : forall a b, le a b -> lt a b \/ a = b. 
    Proof. 
        compute; intros. destruct a as (a1,a2), b as (b1,b2). case H; intros.  
        - now repeat left.
        - destruct H0. apply D2.le_lt_or_eq in H1. case H1; intros.  
          + left.  now right.  
          + right. now subst.    
    Qed. 

    Definition lt_eq_lt_dec : forall (a b: A), {lt a b}+{a = b}+{lt b a}. 
        intros. compute. destruct a as(a1,a2), b as(b1,b2).    
        case (D1.lt_eq_lt_dec a1 b1), (D2.lt_eq_lt_dec a2 b2); intros. 
        - case s, s0; intros; auto. 
          + left. right. now subst.    
        - case s; intros; auto.  
        - case s; intros; auto.  
        - right. now left.   
    Defined.

End Lexico. 

Require Import List. 
Import ListNotations. 

Module List_Order (D:DEC_ORDER) : 
    DEC_ORDER with Definition A := list D.A. 

    Module M := More_Dec_Orders D.  

    Definition A := list D.A. 
    
    Fixpoint   le (la lb: A) := 
        match la with 
        | []        => True
        | a :: ass  => match lb with 
                       | []         => False
                       | b :: bss   => D.lt a b \/ a = b /\ le ass bss end end.  

    Fixpoint   lt (la lb: A) := 
        match la with 
        | []        => [] <> lb
        | a :: ass  => match lb with 
                       | []         => False 
                       | b :: bss   => D.lt a b \/ a = b /\ lt ass bss end end. 

    Lemma refl : reflexive A le. 
    Proof. compute. induction x; auto. Qed. 

    Lemma trans : transitive A le. 
    Proof. 
        unfold transitive. induction x; destruct y,z; intros; try now idtac. 
        - induction H ,H0; intros. 
          + set (M.lt_trans a a0 a1 H H0). now left. 
          + destruct H0.    subst. now left.  
          + destruct H.     subst. now left.      
          + destruct H,H0.  subst. right; split; trivial. 
            now apply (IHx y z).     
    Qed. 

    Lemma asym : antisymmetric A le.  
    Proof. 
        unfold antisymmetric. 
        simple induction x; simple induction y; intros; auto.  
        - inversion H1. 
        - inversion H0.  
        - cut (a = a0 /\ l = l0).  
          + intros. destruct H3. now subst.   
          + inversion H1; inversion H2.   
            * set (M.lt_trans a a0 a H3 H4).  
              set (M.lt_irreflexive a l1). tauto. 
            * destruct H4.  apply D.lt_diff in H3. now subst.   
            * destruct H3.  apply D.lt_diff in H4. now subst. 
            * destruct H3, H4.  split; auto. 
    Qed. 

    Theorem ordered : order A le. 
    Proof. split; [ apply refl | apply trans | apply asym ]. Qed. 

    Print DEC_ORDER. 
    Print M. 

    Theorem lt_le_weak : forall a b, lt a b  -> le a b. 
    Proof.
        simple induction a; simple induction b; try now compute.   
        - intros. unfold le. fold le.     
          unfold lt in H1. fold lt in H1. 
          case H1; intros. 
          + now left. 
          + right. split. now destruct H2. now apply H.    
    Qed. 
    
    Theorem lt_diff : forall a b, lt a b -> a <> b. 
    Proof. 
        simple induction a; simple induction b; auto; intros. 
        unfold lt in H1. fold lt in H1. 
        injection. intros. subst.  
        case H1; intros.  
        - now apply (D.lt_diff a1 a1 H3).
        - destruct H3. now apply (H l0).   
    Qed. 
    
    Theorem le_lt_or_eq : forall a b, le a b -> lt a b \/ a = b. 
    Proof. 
        simple induction a; simple induction b; auto; intros. 
        - left. now compute.  
        - unfold le in H1. fold le in H1.   
          case H1; intros. 
          + left. unfold lt. fold lt. now left.     
          + destruct H2. subst. unfold lt. fold lt.    
            apply H in H3. case H3; intros.   
            * left. right. now split. 
            * right. now subst.    
    Qed. 

    Definition  lt_eq_lt_dec : forall a b, {lt a b}+{a = b}+{lt b a}. 
    induction a as [| x l IHl]; intros. 
    - destruct b; cbn; auto.     
      + left. left. now compute.     
    - destruct b; cbn; auto.  
      + right. discriminate.    
      + case (D.lt_eq_lt_dec x a); case (IHl b); intros; simpl; auto. 
        * case s, s0; intros; simpl; auto. left. right. now subst.  
        * case s; intros. simpl; auto. right. right. split; auto.          
    Defined. 

End List_Order. 






Require Import Arith Lia.  

Module Nat_Order : DEC_ORDER 
    with Definition A   := nat
    with Definition le  := Peano.le
    with Definition lt  := Peano.lt. 

    Definition A    := nat.
    Definition le   := Peano.le.
    Definition lt   := Peano.lt. 
                            
    Theorem ordered : order A le. 
    Proof. split; unfold A,le,reflexive,transitive,antisymmetric; eauto with arith. Qed.
    Theorem lt_le_weak : forall a b, lt a b -> le a b.
    Proof. unfold A, lt, le; lia. Qed.
    Theorem lt_diff : forall a b, lt a b -> a <> b . 
    Proof. unfold A, lt; lia. Qed.  
    Theorem le_lt_or_eq : forall a b, le a b -> lt a b \/ a = b . 
    Proof. exact le_lt_or_eq. Qed.    
    
    Definition lt_eq_lt_dec := Compare_dec.lt_eq_lt_dec.
End Nat_Order. 


Module NatNat       := Lexico Nat_Order Nat_Order.
Module MoreNatNat   := More_Dec_Orders NatNat. 




(* TABLE implementation *) 
(* 12.4 A Dictionary Module *) 


Open Scope type_scope. 


Module Dict_Plus (D:DICT) : DICT_PLUS with Module Dict := D. 
    Module Dict := D. 
    Definition key      := D.key.
    Definition data     := D.data.
    Definition dict     := D.dict. 
    Definition add      := D.add. 
    Definition empty    := D.empty. 

    Fixpoint addlist (l:list(key*data)) d :=
        match l with 
        | nil           =>  d 
        | cons p l'     =>  match p with 
                            | pair k v      => addlist l' (add k v d) end end .  

    Definition build l  := addlist l empty. 
End Dict_Plus. 


Module Type DATA. 
    Parameter data : Type. 
End DATA. 


Module TrivialDict (K:KEY) (V:DATA) : DICT 
    with Definition key     := K.A
    with Definition data    := V.data. 

    Definition key              := K.A. 
    Definition data             := V.data. 
    Definition dict             := key -> option data. 
    Definition empty(k:key)     := None (A := data). 
    Definition find k(d:dict)   := d k . 
    Definition add k v (d:dict) := fun k':key => 
        match K.eqdec k' k with 
        | left _    => Some v
        | right _   => d k'         end. 

    Theorem empty_def : forall k , find k empty = None. 
    Proof. unfold find, empty; auto.  Qed. 

    Theorem success : forall d k v, find k (add k v d) = Some v. 
    Proof. unfold find, add; intros; case (K.eqdec k k); tauto.  Qed. 

    Theorem diff_key : forall d k k' v, k <> k' -> find k (add k' v d) = find k d. 
    Proof. unfold find, add; intros; case (K.eqdec k k'); tauto. Qed.  
End TrivialDict. 


Print DICT.  Print KEY. 
Module LDict (K:KEY) (V:DATA) : DICT 
    with Definition key     := K.A
    with Definition data    := V.data. 

    Definition key              := K.A.
    Definition data             := V.data. 
    Definition dict             := list (key * data) . 
    Definition empty  : dict    := [] . 
    Definition add k v (d:dict) := (k,v) :: d . 
    Fixpoint   find k (d:dict)  := match d with
                                   | []         => None
                                   | (k',v)::d' => match (K.eqdec k k') with  
                                                   | left _   => Some v    
                                                   | right _  => find k d' end end.  

    Theorem empty_def : forall k, find k empty = None. 
    Proof. unfold find, empty; auto. Qed. 

    Theorem success : forall d k v, find k (add k v d) = Some v. 
    Proof. unfold find, add; intros; case (K.eqdec k k); tauto. Qed. 

    Theorem diff_key : forall d k k' v, k <> k' -> find k (add k' v d) = find k d. 
    Proof. unfold find, add; intros; case (K.eqdec k k'); tauto. Qed.  
End LDict. 



Module TDict (K:DEC_ORDER) (V:DATA) : DICT 
    with Definition key := K.A
    with Definition data := V.data. 

    Definition key              := K.A. 
    Definition data             := V.data. 
    
    Module M                    := More_Dec_Orders K. 

    Inductive btree : Type       := 
      | leaf      : btree
      | bnode     : key -> data -> btree -> btree -> btree. 

    Inductive occ v k : btree -> Prop := 
      | occ_root  : forall       l r,              occ v k (bnode k  v  l r) 
      | occ_l     : forall v' k' l r, occ v k l -> occ v k (bnode k' v' l r)
      | occ_r     : forall v' k' l r, occ v k r -> occ v k (bnode k' v' l r) . 

    Inductive min n t : Prop :=
      | min_intro : (forall k v, occ v k t -> K.lt n k) -> min n t .  
    
    Inductive maj n t : Prop :=
      | maj_intro : (forall k v, occ v k t -> K.lt k n) -> maj n t. 

    Inductive search_tree : btree -> Prop :=
      | leaf_search_tree  : search_tree leaf
      | bnode_search_tree : forall k v l r, search_tree l -> search_tree r ->
                            maj k l -> min k r -> search_tree (bnode k v l r). 

    Hint Resolve 
      leaf bnode occ_root occ_l occ_r min_intro maj_intro
      leaf_search_tree bnode_search_tree : searchtrees. 


    Lemma min_leaf : forall n, min n leaf. 
    Proof. intros. constructor. intros. inversion H. Qed. 

    Lemma maj_leaf : forall n, maj n leaf. 
    Proof. intros. constructor. intros. inversion H. Qed. 
    
    Lemma maj_not_occ : forall n v t, maj n t -> ~ occ v n t. 
    Proof. 
      red. intros. induction t.   
      - inversion H0.  
      - inversion H. set (H1 n v H0). now set (K.lt_diff n n l).      
    Qed.  

    Lemma min_not_occ : forall n v t, min n t -> ~ occ v n t. 
    Proof. 
      red. intros n v t Hmin H. induction t.   
      - inversion H. 
      - inversion Hmin. set (H0 n v H). now set (K.lt_diff n n l). 
    Qed. 

    Section search_tree_basic_properties. 
      Variable  n   : key. 
      Variable  v v': data. 
      Variables l r : btree. 
      Hypothesis se : search_tree (bnode n v l r). 

      Lemma search_tree_l : search_tree l.  Proof. now inversion se. Qed. 
      Lemma search_tree_r : search_tree r.  Proof. now inversion se. Qed. 
      Lemma maj_l : maj n l.                Proof. now inversion se. Qed. 
      Lemma min_r : min n r.                Proof. now inversion se. Qed. 
      Lemma not_right : forall p, K.le p n -> ~ occ v p r. 
      Proof. 
        inversion se. subst. 
        inversion H6. intros p le_p_n Hocc. 
        set (H p v Hocc) as lt_n_p. 
        apply M.le_not_lt in le_p_n; tauto.  
      Qed. 
      Lemma not_left : forall p, K.le n p -> ~ occ v p l. 
      Proof. 
        inversion se. subst. 
        inversion H5. intros p le_n_p Hocc. 
        set (H p v Hocc) as lt_p_n.  
        apply M.le_not_lt in le_n_p; tauto.  
      Qed. 
      Lemma go_left : forall p, occ v p (bnode n v' l r) -> K.lt p n -> occ v p l. 
      Proof. 
        inversion se; subst; intros.
        inversion H ; subst; intros; auto. 
        - now set (K.lt_diff n n H0). 
        - apply K.lt_le_weak in H0. apply not_right in H0. tauto.  
      Qed. 
      Lemma go_right : forall p, occ v p (bnode n v' l r) -> K.lt n p -> occ v p r. 
      Proof. 
        inversion se; subst; intros.
        inversion H ; subst; intros; auto. 
        - now set (K.lt_diff n n H0). 
        - apply K.lt_le_weak in H0. apply not_left in H0. tauto. 
      Qed. 
    End search_tree_basic_properties. 

    Hint Resolve 
      go_left go_right not_left not_right
      search_tree_l search_tree_r maj_l min_r 
      maj_not_occ min_not_occ min_leaf maj_leaf : searchtrees. 



    Definition occ_dec_spec (k:key)(t:btree) := 
        search_tree t -> {d:data | occ d k t}+{forall (d:data), ~ occ d k t} . 

    Definition occ_dec : forall k t, occ_dec_spec k t. 
      refine( fix occ_dec k t {struct t} := _ ). 
      refine( match t with 
              | leaf            => _ 
              | bnode k' v' l r => _ end ). 
      - refine ( fun H => _ ). 
        right. red. intros. inversion H0. 
      - refine ( fun H => _ ).   
        refine ( match M.le_lt_dec k k' with 
                 | left  Hle  => _
                 | right Hlt  => _ end ).   
        + refine ( match M.le_lt_eq_dec k k' Hle with 
                   | left Hlt   => _ 
                   | right Heq  => _ end ).  
          * refine ( match occ_dec k l _ with 
                     | inleft H'   => _ 
                     | inright nH' => _  end ); eauto with searchtrees. 
            -- left. destruct H'. exists x. now constructor.       
            -- right. inversion H. intros x H'. Check go_left. 
               apply (nH' x). apply (go_left k' x v' l r); eauto with searchtrees. 
          * subst. left. exists v'. constructor.     
        + refine ( match occ_dec k r _ with 
                   | inleft H'    => _ 
                   | inright nH'  => _ end ); eauto with searchtrees.  
          * left. destruct H'. exists x. now constructor.   
          * right. inversion H. intros x H'. 
            apply (nH' x). apply (go_right k' x v' l r); eauto with searchtrees. 
    Defined. 


    Inductive INSERT (k:key) v t t' : Prop := 
      | insert_intro : 
          (forall k' v', occ v' k' t -> k'=k \/ occ v' k' t') -> 
          (* if keys are the very insertion key or what were in the rest of tree *) 
          occ v k t' -> 
          (* proof that the key is already inserted *)
          (forall k' v', occ v' k' t'-> occ v' k' t \/ k=k' /\ v=v') -> 
          (* if a (key,value) pair occured,it's just inserted or occurs in the rest *)
          search_tree t' -> 
          (* it's ordered *)
          INSERT k v t t'. 


    Definition insert_spec (k:key) v t : Type := 
      search_tree t -> {t': btree | INSERT k v t t'} . 
    

    Lemma insert_leaf : forall k v, INSERT k v leaf (bnode k v leaf leaf). 
    Proof. 
      intros. constructor; intros; eauto with searchtrees.   
      - inversion H; now right.  
    Qed. 

    Lemma insert_l :  forall k k' v v' l l' r, 
                        K.lt k k' -> 
                        search_tree (bnode k' v' l r) -> 
                        INSERT k v l l' -> 
                        INSERT k v (bnode k' v' l r) (bnode k' v' l' r).
    Proof. 
      intros k k' v v' l l' r Hlt Hord Hins. 
      inversion Hins.  (* decompose INSERT k v l l'                                  *) 
      constructor.     (* decompose INSERT k v (bnode k' v' l r) (bnode k' v' l' r)  *) 
      + intros k'' v'' Hocc. inversion Hocc; subst. 
        * right. now constructor. 
        * case (H k'' v''); eauto with searchtrees. 
        * right. now constructor.  
      + apply occ_l. case (H1 k v); eauto with searchtrees.    
      + intros k'' v'' Hocc. inversion Hocc; subst. 
        * left. now constructor.  
        * case (H1 k'' v''); eauto with searchtrees.   
        * left. now constructor.  
      + inversion Hord; subst; constructor; eauto with searchtrees. 
        * constructor. inversion H9. intros k'' v'' Hocc. 
          case (H1 k'' v''); eauto with searchtrees. 
          - intros Heqs. destruct Heqs. now subst. 
    Qed. 

    Lemma insert_r :  forall kk k vv v l r r', 
                        K.lt k kk -> 
                        search_tree (bnode k v l r) -> 
                        INSERT kk vv r r' -> 
                        INSERT kk vv (bnode k v l r) (bnode k v l r'). 
    Proof. 
      intros kk k vv v l r r' Hlt Hord Hins. 
      inversion Hins.   (* decompose INSERT kk vv r r' *)
      constructor.      (* decompose INSERT kk vv (bnode k v l r) (bnode k v l r') *) 
      + intros k' v' Hocc. inversion Hocc; subst.   
        * right. now constructor. 
        * right. now constructor.  
        * case (H k' v'); eauto with searchtrees.  
      + eauto with searchtrees. 
      + intros k' v' Hocc. inversion Hocc; subst. 
        * left. now constructor. 
        * left. now constructor. 
        * case (H1 k' v'); eauto with searchtrees. 
      + inversion Hord; subst; constructor; eauto with searchtrees. 
        * constructor. inversion H10. intros k' v' Hocc. 
          case (H1 k' v'); eauto with searchtrees. 
          - intros Heqs. destruct Heqs. now subst. 
    Qed. 

    Lemma insert_eq :   forall k v v' l r, 
                          search_tree (bnode k v' l r) -> 
                          INSERT k v (bnode k v' l r) (bnode k v l r). 
    Proof. 
      intros kk vv v l r Hord. 
      constructor. 
      + intros k' v' Hocc. inversion Hocc; subst; eauto with searchtrees. 
      + constructor. 
      + intros k' v' Hocc. inversion Hocc; subst; eauto with searchtrees. 
      + inversion Hord; subst.                (* decompose search_tree (bnode kk v  l r) *)
        constructor; eauto with searchtrees.  (* decompose search_tree (bnode kk vv l r) *) 
    Qed. 

    Hint Resolve insert_leaf insert_l insert_r insert_eq : searchtrees. 

    Definition insert : forall (k:key)(v:data)(t:btree), insert_spec k v t. 
      refine ( fix insert k v t := _ ). 
      refine ( match t with 
             | leaf             => _ 
             | bnode k' v' l r  => _ end ). 
      - refine (fun s => exist _ ( bnode k v leaf leaf ) _ ). 
        apply insert_leaf. 
      - refine (match M.le_lt_dec k k' with 
                | left Hle  => match M.le_lt_eq_dec k k' Hle with 
                               | left Hlt   => _ 
                               | right Heq  => _ end 
                | right Hlt => _ end ); unfold insert_spec; intros Hocc.  
        + set (insert k v l) as Hins. destruct Hins.  
          * now inversion Hocc. 
          * exists (bnode k' v' x r).  
            apply insert_l; eauto with searchtrees.  
        + subst k'. exists (bnode k v l r). eauto with searchtrees.  
        + set (insert k v r) as Hins. destruct Hins.  
          * now inversion Hocc. 
          * exists (bnode k' v' l x). eauto with searchtrees. 
    Defined. 


    Definition dict : Type := sig (A := btree) search_tree. 
    Definition empty : dict. 
      unfold dict. exists leaf. constructor.    
    Defined. 
    Definition find k (d:dict) : option data := 
      let (t, Ht) := d in 
      match occ_dec k t Ht with 
      | inleft s  => let (v,_) := s in Some v
      | inright _ => None                 end. 

    Definition add : key -> data -> dict -> dict. 
      refine (fun k v d =>  let (t, Ht) := d                in 
                            let (x, Hx) := insert k v t Ht  in 
                            exist search_tree x _   ) . 
      now inversion Hx.   
    Defined. 
    Print exist. 

    Print DICT.  
    Theorem empty_def : forall k, find k empty = None. 
    Proof. intros. eauto with searchtrees. Qed. 


    Lemma occ_uniq_root : forall k v v' l r, 
        search_tree (bnode k v' l r) -> occ v k (bnode k v' l r) -> v = v'. 
    Proof. 
      intros. 
      inversion H; subst; eauto with searchtrees.  
      set (maj_not_occ k v l H7).  
      set (min_not_occ k v r H8). 
      inversion H0; subst; now idtac. 
    Qed. 

    Lemma occ_uniq : forall k v v' t , search_tree t -> occ v k t -> occ v' k t -> v = v'. 
    Print occ. 
    Print search_tree. 
    Proof. 
      simple induction t. 
      + intros. inversion H0. 
      + intros. inversion H1. subst v0 b b0 k0. 
        case (M.le_lt_dec k k1); intros; auto. 
        * case (M.le_lt_eq_dec k k1); intros; auto.    
          - apply H; clear H0; eauto with searchtrees. 
          - subst; apply occ_uniq_root in H3;   
            subst; apply occ_uniq_root in H2; now subst. 
        * apply H0; clear H; eauto with searchtrees.   
    Qed. 


    Theorem success : forall d k v, find k (add k v d) = Some v. 
    Proof. 
      intros. unfold find, add.  
      set (add k v d). 
      destruct d as [t Ht].
      destruct d0 as [t' Ht']. 
      set (insert k v t Ht) as ins. 
      destruct ins as [x Hx]. 
      destruct Hx.  
      case (occ_dec k x s). 
      - intros. destruct s0 as [v0 Hocc].   
        case (o1 k v0 Hocc). 
        + intros. eauto with searchtrees.  
          set (occ_uniq k v v0 x s o0 Hocc).
          now rewrite e.  
        + intros Heq; destruct Heq. now subst. 
      - intros. set (n v). now idtac.   
    Qed. 

    Theorem diff_key : forall d k k' v , k <> k' -> find k (add k' v d) = find k d. 
    Proof. 
      intros. unfold find, add.  
      destruct d as [t Ht]. 
      set (insert k' v t Ht) as d'. 
      destruct d' as [x Hx]. 
      case (occ_dec k x); intros.  
      - destruct s as [v0 Hocc0].  
        case (occ_dec k t Ht); intros. 
        + destruct s as [v1 Hocc1].  
          inversion Hx. 
          case (H0 k v1); auto. 
          * intros. subst. tauto.     
          * intros. set (occ_uniq k v0 v1 x H3 Hocc0 H4). now rewrite e.  
        + inversion Hx. set (H2 k v0 Hocc0). case o.    
          * intros. set (n v0). now idtac.  
          * intros Heq. destruct Heq. subst. now idtac.   
      - case (occ_dec k t Ht); intros.  
        + destruct s. set (n x0).   
          inversion Hx. case (H0 k x0 o); intros.  
          * now idtac.  
          * now idtac.  
        + trivial.  
    Qed. 

           
      
End TDict. 



Module Type LSORT. 
  Parameter A : Set . 
  Parameter le : A -> A -> Prop. 
  Parameter lt : A -> A -> Prop. 
  Parameter sorted : list A -> Prop.
  Axiom sorted_inv : forall a l, sorted (a :: l) -> sorted l. 

  Parameter equiv : list A -> list A -> Prop. 
  Axiom equiv_refl : forall l, equiv l l.
  Axiom equiv_sym  : forall l l', equiv l l' -> equiv l' l. 
  Axiom equiv_trans : forall l l' l'', equiv l l' -> equiv l' l'' -> equiv l l''.
  Axiom equiv_cons : forall a l l', equiv l l' -> equiv(a::l)(a::l'). 
  Axiom equiv_perm : forall a b l l', equiv l l' -> equiv(a::b::l)(b::a::l'). 

  Parameter sort : forall l, { l' | equiv l l' /\ sorted l'}. 
End LSORT. 



