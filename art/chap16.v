(* Chapter 16 * Proof by Reflection *)



(* 16.1 General Presentation *) 

Theorem plus_assoc : forall x y z:nat, x + (y + z) = x+y+z . 
Proof. 
  intros x y z; induction x. 
  - exact (refl_equal (y+z)). 
  - simpl. rewrite IHx. reflexivity.    
Qed. 



(* 16.2 Direct Computation Proofs *)

Require Import Arith ZArith Lia. 
Require Export Zdiv. 
(* Export means  
  Importing Zdiv and then Exporting Zdiv to those who use this file *) 

Check Z.div_eucl. 
Check Z_div_mod. 
Check Zmod. 

Locate "mod". 
Locate "*". 

Lemma lt_Z_of_nat : forall n m:nat, n < m -> (Z.of_nat n < Z.of_nat m)%Z.  
Proof. auto with zarith. Qed.   

Lemma mul_Z_of_nat : forall n m, Z.of_nat (n * m) = (Z.of_nat n * Z.of_nat m)%Z. 
Proof. auto with zarith. Qed. 

Check Z.mul_comm. 
Check Z_mod_mult. 
  
Theorem verif_divide :  forall m p: nat, O < m -> O < p -> 
                        ( exists q, m = q*p ) -> 
                        (Z.of_nat m mod Z.of_nat p = 0)%Z. 
Proof. 
  intros m p Hm Hp [q Heq]. 
  rewrite Heq, mul_Z_of_nat, Z_mod_mult. 
  reflexivity. 
Qed. 

Theorem verif_divide_nat :  forall m p, O < m -> O < p -> 
                            (exists q, m = q*p) -> m mod p = O . 
Proof. 
  intros m p Hm Hp [q Heq]; rewrite Heq. 
  rewrite Nat.mod_mul; auto with zarith.   
Qed. 

Theorem divisor_smaller :   forall m p:nat, 0 < m -> forall q, m = q*p -> q <= m. 
Proof. 
  intros m p Hlt q Heq.  
  cut (0<p); [ rewrite Heq ; destruct p | ] ; auto with zarith. 
Qed. 

Fixpoint check_range (v:Z) (r:nat) (sr:Z) {struct r} : bool :=
   match r with 
   | O    => true
   | S r' => match (v mod sr)%Z with 
             | Z0   => false
             | _    => check_range v r' (Z.pred sr) end end. 

Definition check_primality (n:nat) := 
  check_range (Z.of_nat n) (pred (pred n)) (Z.of_nat (pred n)). 


Compute check_primality 2333. 
Compute check_primality 2330. 

Fixpoint check_range_nat v r := 
    match r with 
    | O     => true
    | S r'  => match v mod S r with 
               | O  => false
               | _  => check_range_nat v r'  end end. 

Theorem check_range_correct_nat : forall v r, 
    0 < v ->  
    check_range_nat v r = true -> 
    ~ (exists k, k <= S r /\ k <> 1 /\ (exists q, v = q * k)). 
Proof. 
  induction r.  
  + intros Hlt Heq Hex; case Hex; intros k; case k. 
    - intros [_ [_ [q Heq0]]]. lia.  
    - lia.   
  + intros Hlt Heq Hex; case Hex; intros k; case k. 
    - intros [_ [_ [q Heq0]]]. lia. 
    - intros n [Hle [Sn_not_1 [q Heqv]]].  
      inversion Hle.  
      * unfold check_range_nat in Heq. fold check_range_nat in Heq.     
        { assert (v mod S(S r) = 0).  
          - apply verif_divide_nat; [ | | exists q ]; lia.  
          - rewrite H in Heq; discriminate Heq. }  
      * unfold check_range_nat in Heq. fold check_range_nat in Heq.  
        { case_eq (v mod S(S r)); intros; rewrite H1 in Heq; try discriminate. 
          - destruct r; auto with zarith. 
            + unfold check_range_nat in Heq. fold check_range_nat in Heq. 
              { case_eq (v mod S (S r)); intros; rewrite H2 in Heq; try discriminate. 
                - destruct Hex as [k' [Hle' [Hlt' [q' Hq']]]]. 
                  apply IHr; try lia.  
                  + unfold check_range_nat. fold check_range_nat.   
                    rewrite H2. assumption.  
                  + exists (S n). intuition. exists q. assumption. } }
Qed.                        

Lemma Z_of_abs_nat : forall z, (z > 0)%Z -> Z.of_nat (Z.abs_nat z) = z. 
Proof. auto with zarith. Qed.  
Lemma Z_abs_of_nat : forall n, Z.abs_nat (Z.of_nat n) = n. 
Proof. auto with zarith. Qed. 


Check mod_Zmod. 

Lemma chk_rng_eq_chk_rng_nat : forall v r, (v > 0)%Z -> 
  check_range v r (Z.of_nat (S r)) = check_range_nat (Z.abs_nat v) r. 
Proof. 
  intros. 
  induction r; auto with zarith.  
  - unfold check_range,check_range_nat. fold check_range. fold check_range_nat.  
    rewrite <- IHr. 
    assert ( (v mod Z.of_nat(S (S r)))%Z = Z.of_nat(Z.abs_nat v mod S(S r)) ). 
    + rewrite (mod_Zmod (Z.abs_nat v) (S(S r))), Z_of_abs_nat; auto with zarith. 
    + rewrite H0. repeat rewrite inj_S. rewrite Z.pred_succ. 
      induction (Z.abs_nat v mod S(S r)); auto.   
Qed.  

Theorem check_range_correct : forall v r rz, (0<v)%Z -> 
    Z.of_nat (S r) = rz -> 
    check_range v r rz = true -> 
    ~ (exists k, k <= S r /\ k <> 1 /\ (exists q, Z.abs_nat v = q * k)). 
Proof. 
  intros; subst; apply (check_range_correct_nat (Z.abs_nat v) r); 
  [ | rewrite <- chk_rng_eq_chk_rng_nat ];  auto with zarith. 
Qed.   

Compute check_primality 0.  (* true *) 
Compute check_primality 1.  (* true *) 

Theorem check_correct : 
  forall p, 1 < p -> check_primality p = true -> 
  ~ (exists k, k <> 1 /\ k <> p /\ (exists q, p = q*k)). 
Proof. 
  unfold check_primality. intros p Hlt H [k [Hn1 [ Hnp [q Heq]]]]. 
  apply check_range_correct in H; auto with zarith.  
  - apply H; rewrite Z_abs_of_nat. 
    exists k. repeat split; 
    [ assert (Hp : 0 < p); try set (divisor_smaller p q Hp k) | | exists q ]; 
    auto with zarith. 
Qed.


Theorem prime_2333: 
  ~ (exists k, k <> 1 /\ k <> 2333/\ (exists q, 2333= q * k)). 
Proof. 
  Time apply check_correct; compute; auto with arith. 
  Time 
Qed. 



(* ex. 16.2 *) 
(* ==> see sqrt.v *) 


(* 16.3 ** Proof by Algebraic Computation *) 


(* 16.3.1 Proofs Module Associativity *) 

Theorem reflection_test : forall x y z t u, x+(y+z+(t+u)) = x+y+(z+(t+u)). 
Proof. intros; repeat rewrite plus_assoc. reflexivity.   Qed. 


Inductive bin : Type := 
  | node : bin -> bin -> bin 
  | leaf : nat -> bin . 

Fixpoint flatten_aux (t fin:bin) :=
    match t with 
    | node l r  => flatten_aux l (flatten_aux r fin)
    | leaf n    => node (leaf n) fin          end. 

Fixpoint flatten t := 
    match t with 
    | node l r  => flatten_aux l (flatten r) 
    | x         => x                          end. 


Eval compute in 
  (flatten
    (node (leaf 1) ( node (node (leaf 2)(leaf 3)) (leaf 4)))). 


Fixpoint bin_nat t :=
  match t with 
  | node l r  => bin_nat l + bin_nat r 
  | leaf n    => n                      end. 


Theorem flatten_aux_valid : forall t t', 
    bin_nat t + bin_nat t' = bin_nat (flatten_aux t t'). 
Proof. 
  simple induction t; simple destruct t'; simpl; intros; 
  try rewrite <- H; try rewrite <- H0; simpl; auto with arith. 
Qed. 

Theorem flatten_valid : forall t, bin_nat t = bin_nat (flatten t). 
Proof. 
  simple induction t; simpl; intros; 
  try rewrite <- flatten_aux_valid; auto. 
Qed. 

Theorem flatten_valid_2 : forall t t', 
    bin_nat (flatten t) = bin_nat (flatten t') -> bin_nat t = bin_nat t'. 
Proof. intros; rewrite (flatten_valid t), (flatten_valid t'); assumption. Qed. 


Theorem reflection_test' : 
  forall x y z t u, x + ( y + z + (t + u)) = x + y + (z + (t + u)) . 
Proof. 
  intros. 
  change (bin_nat 
    ( node  (leaf x)
            (node   (node (leaf y)(leaf z))
                    (node (leaf t)(leaf u)))) = 
          bin_nat
    ( node  (node   (leaf x)(leaf y))
            (node   (leaf z)
                    (node (leaf t)(leaf u))))). 
  apply flatten_valid_2. 
  reflexivity. 
Qed. 



Ltac model v := 
  match v with 
  | (?L + ?R) => 
      let   l := model L 
      with  r := model R in 
      constr : (node l r)
  | ?N => 
      constr : (leaf N) end. 

Ltac assoc_eq_nat := 
  match goal with
  | [ |- (?X = ?Y :> nat) ] => 
      let   t := model X 
      with  t':= model Y in (
      change (bin_nat t = bin_nat t'); 
      apply flatten_valid_2;
      lazy beta iota zeta delta [flatten flatten_aux bin_nat]; 
      auto ) end. 


Theorem reflection_test'' : 
  forall x y z t u, x + ( y + z + (t + u)) = x + y + (z + (t + u)) . 
Proof. 
  intros; assoc_eq_nat. 
Qed. 







(* 16.3.2 Making the Types and the Operator More Generic *) 

Require Import List. 
Import ListNotations. 

Section assoc_eq. 
  Variables (A:Type) (f : A->A->A) . 

  Fixpoint bin_A l default t := 
    match t with 
    | node L R    => f (bin_A l default L)(bin_A l default R)
    | leaf N      => nth N l default end. 

  Theorem flatten_aux_valid_A 
    (assoc: forall x y z, f x (f y z) = f (f x y) z) : 
    forall l df L R, f (bin_A l df L) (bin_A l df R) = bin_A l df (flatten_aux L R). 
  Proof. 
    simple induction L; simple destruct R; simpl; intros;
    try rewrite <- H, <- H0, <- assoc; reflexivity. 
  Qed. 
  
  Theorem flatten_valid_A (assoc: forall x y z, f x(f y z) = f (f x y) z) : 
    forall l df t, bin_A l df t = bin_A l df (flatten t). 
  Proof. 
    simple induction t; simpl; intros; 
    try rewrite H0; try apply (flatten_aux_valid_A assoc); reflexivity. 
  Qed. 

  Theorem flatten_valid_A_2 (assoc: forall x y z, f x(f y z) = f (f x y) z) : 
    forall l df L R, 
    bin_A l df (flatten L) = bin_A l df (flatten R) -> 
    bin_A l df L = bin_A l df R. 
  Proof. 
    intros; rewrite flatten_valid_A, (flatten_valid_A assoc l df R); assumption. 
  Qed. 

End assoc_eq. 


Ltac term_list f l v :=
  match v with 
  | (f ?L ?R)   =>  let l' := term_list f l R in 
                    term_list f l' L
  | ?N          =>  constr : ( cons N l )       end. 

Ltac compute_rank l n v := 
  match l with 
  | (cons ?A ?AS) => 
      match constr : (A = v) with 
      | (?A = ?A)   => n 
      | _           => compute_rank AS (S n) v  end end. 

Ltac model_aux l f v := 
  match v with 
  | (f ?L ?R) =>  let   L' := model_aux l f L 
                  with  R' := model_aux l f R in 
                  constr : (node L' R') 
  | ?N        =>  let n := compute_rank l 0 N in 
                  constr : (leaf n)
  | _         =>  constr : (leaf 0)                   end. 

Ltac model_A A f df v := 
  let l := term_list f (nil (A:=A)) v in 
  let t := model_aux l f v  in 
  constr : (bin_A A f l df t) . 

Ltac assoc_eq A f assoc_thm := 
  match goal with 
  | [ |- (@eq A ?X ?Y) ] => 
      let   t   := model_A A f X X 
      with  t'  := model_A A f X Y in 
      (
      change (t = t'); 
      apply (flatten_valid_A_2 A f assoc_thm);
      reflexivity
      ) end. 

Check flatten_valid_A_2. 

Theorem reflection_test3 : 
  forall x y z t u, (x*(y*z*(t*u)) = x*y*(z*(t*u)))%Z. 
Proof.  intros. assoc_eq Z Zmult Zmult_assoc.  Qed. 



(* ex. 16.5 *) 
Search (0 + _ = _ ). 
Search (_ + 0 = _ ). 
Search (1 * _ = _ ). 
Ltac assoc_unit_eq A f assoc_thm unit_left_thm unit_right_thm :=
  repeat rewrite unit_left_thm; 
  repeat rewrite unit_right_thm; 
  assoc_eq A f assoc_thm. 

Theorem reflection_test4 : 
  forall x y z, (x+0) + (y + (z+0)) =  x + (y + (z + 0)).  
Proof. 
  intros; assoc_unit_eq nat Nat.add plus_assoc Nat.add_0_l Nat.add_0_r . 
Qed. 

(* end ex. 16.5 *) 









(* 16.3.3 *** Commutativity : Sorting Variables *) 


Fixpoint nat_le_bool n m := 
  match n, m with 
  | O , _     => true
  | _ , O     => false
  | S p, S q  => nat_le_bool p q end. 


Fixpoint insert_bin n t :=  (* tree t is already flattened *) 
  match t with 
  | leaf m          =>  match nat_le_bool n m with 
                        | true  => node (leaf n) (leaf m)
                        | false => node (leaf m) (leaf n) end 
  | node (leaf m) R =>  match nat_le_bool n m with 
                        | true  => node (leaf n) t 
                        | false => node (leaf m) (insert_bin n R) end 
  |  _              =>  node (leaf n) t   end.


Fixpoint sort_bin t := 
  match t with 
  | node (leaf n) R   => insert_bin n (sort_bin R)
  | _                 => t                            end. 


Section comm_eq. 
  Variables (A:Type) (f:A->A->A). 
  Hypothesis comm  : forall x y, f x y = f y x . 
  Hypothesis assoc : forall x y z, f x (f y z) = f (f x y) z . 
  
  Definition bin_A' := bin_A A f. 
  Theorem insert_is_f : forall l df n t, 
    bin_A' l df (insert_bin n t) = f (nth n l df) (bin_A' l df t). 
  Proof.
    induction t; intros; 
    try destruct t1; simpl; 
    try destruct (nat_le_bool n n0); simpl; 
    [ | | rewrite IHt2,assoc,assoc,(comm(nth n0 l df)),comm | | rewrite comm ]; 
    reflexivity. 
  Qed. 


  Theorem sort_eq : forall l df t, bin_A' l df (sort_bin t) = bin_A' l df t. 
  Proof. 
    induction t; intros; simpl; 
    try destruct t1; simpl; try rewrite <- IHt2, insert_is_f; 
    reflexivity. 
  Qed. 


  Theorem sort_eq_2 : forall l df t t', 
    bin_A' l df (sort_bin t) = bin_A' l df (sort_bin t') -> 
    bin_A' l df t = bin_A' l df t' . 
  Proof. 
    intros. rewrite <- sort_eq, <- (sort_eq l df t'); assumption.     
  Qed. 

End comm_eq. 


Ltac comm_eq A f assoc_thm comm_thm := 
  match goal with 
  | [ |- (?X = ?Y :> A) ]   =>  let   l := term_list f (nil (A:=A)) X in 
                                let   t := model_aux l f X 
                                with  t':= model_aux l f Y in 
                                (
                                change (bin_A A f l X t = bin_A A f l X t'); 
                                apply (flatten_valid_A_2 A f assoc_thm);
                                apply sort_eq_2; 
                                set assoc_thm; set comm_thm; auto
                                ) end.  
Require Import ZArith. 

Theorem reflection_test5 : forall x y z, ( x + (y + z) = (z + x) + y )%Z . 
Proof. intros. comm_eq Z Z.add Z.add_assoc Z.add_comm. Qed.  





