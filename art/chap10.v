


(* 10.1.1 "Extraction" Commend *) 

Require Import Extraction ZArith . 

(* assume there is ./extract/ directory *) 
Extraction "extract/pplus.ml" Pplus. 








(* 10.1.2 Extraction Mechanism *) 

(* Extracting Non-Dependent types *) 

Inductive positive : Set := 
    | xI : positive -> positive 
    | xO : positive -> positive 
    | xH : positive .

Extraction "extract/positive.ml" positive. 

(* ==> see positive.ml  

type positive =
| XI of positive
| XO of positive
| XH
 *)




Fixpoint Psucc x := 
  match x with 
  | xI x' => xO (Psucc x') 
  | xO x' => xI x'
  | xH    => xO xH      end. 

Extraction "extract/psucc.ml" Psucc. 


(* 
let rec psucc = function
| XI x' -> XO (psucc x')
| XO x' -> XI x'
| XH -> XO XH
 *)







(* Extracting Polymorphism *) 


Inductive list (A:Set) : Set := 
  | nil : list A 
  | cons : A -> list A -> list A. 

Extraction "extract/list.ml" list. 
(*
type 'a list =
| Nil
| Cons of 'a * 'a list
*)


Fixpoint app (A:Set)(l m:list A) := 
  match l with 
  | nil _ => m
  | cons _ x xs => cons A x (app A xs m) end. 

Extraction "extract/app.ml" app. 
(*
let rec app l m =
  match l with
  | Nil -> m
  | Cons (x, xs) -> Cons (x, (app xs m))
*)








(* ex. 10.1 *) 
Inductive option (A:Set) : Set := 
  | Some : A -> option A
  | None : option A . 


Fixpoint nth' (A:Set) l n := 
  match l, n with 
  | nil _      , _    => None A
  | cons _ a tl, O    => Some A a
  | cons _ a tl, S p  => nth' A tl p end. 

Extraction "extract/ex10_1.ml" option nth'. 
(* ==> see extract-polymorphism.ml *) 
(* end ex. 10.1 *) 










(* Discarding Proofs *) 


Inductive sumbool {A B:Prop} : Set := 
  | left  : A -> sumbool  
  | right : B -> sumbool . 

Extraction "extract/sumbool.ml" sumbool. 
(* 
type sumbool =
| Left
| Right
 *)



Lemma eq_xI : forall p q, p = q -> xI p = xI q. 
Proof. intros. rewrite H. reflexivity. Qed. 
Lemma eq_xO : forall p q, p = q -> xO p = xO q. 
Proof. intros. rewrite H. reflexivity. Qed. 
Lemma not_eq_xI : forall p q, p <> q -> xI p <> xI q. 
Proof. red. intros. apply H. injection H0. intros. rewrite H1. reflexivity. Qed.  
Lemma not_eq_xO : forall p q, p <> q -> xO p <> xO q. 
Proof. red. intros. apply H. injection H0. intros. rewrite H1. reflexivity. Qed.  
Lemma sym_not_equal : forall (p q:positive), p <> q -> q <> p. 
Proof. red. intros. apply H. rewrite H0. reflexivity. Qed.   
Lemma xI_xO : forall p q, xI p <> xO q. 
Proof. inversion 1.   Qed. 
Lemma xH_xI : forall p, xH <> xI p. 
Proof. inversion 1.   Qed. 
Lemma xH_xO : forall p, xH <> xO p. 
Proof. inversion 1.   Qed. 

Fixpoint eq_positive_dec n m {struct m} := 
  match n with
  | xI p  => match m with 
             | xI q   => match eq_positive_dec p q with 
                         | left heq   => left  (eq_xI p q heq) 
                         | right hneq => right  (not_eq_xI p q hneq) end 
             | xO q   => right  (xI_xO p q) 
             | xH     => right  (sym_not_equal _ _ (xH_xI p)) end
  | xO p  => match m with 
             | xI q   => right  (sym_not_equal _ _ (xI_xO q p))
             | xO q   => match eq_positive_dec p q with 
                         | left   heq => left    (eq_xO p q heq)
                         | right hneq => right   (not_eq_xO p q hneq) end
             | xH     => right  (sym_not_equal _ _ (xH_xO p)) end
  | xH    => match m with 
             | xI q   => right  (xH_xI q)
             | xO q   => right  (xH_xO q)
             | xH     => left   (refl_equal xH) end end. 

Extraction "extract/eq_positive_dec.ml" eq_positive_dec . 
(** val eq_positive_dec : positive -> positive -> sumbool
let rec eq_positive_dec n m =
  match n with
  | XI p -> (match m with
             | XI q -> eq_positive_dec p q
             | _ -> Right)
  | XO p -> (match m with
             | XO q -> eq_positive_dec p q
             | _ -> Right)
  | XH -> (match m with
           | XH -> Left
           | _ -> Right)
*)




(* False_rec becomes assert false == error *) 
Definition pred' n : n <> 0 -> nat := 
  match n with 
  | O   => fun h : 0   <> 0 => False_rec nat (h (refl_equal 0))
  | S p => fun h : S p <> 0 => p        end. 

(** val pred' : nat -> nat 
let pred' = function
| O -> assert false (* absurd case *)
| S p -> p
 *) 


(* adding Unit for laziness *) 
Definition pred'_on_O := pred' 0. 
(* if this function is extracted naturally, 
    let pred'_on_O := pred' 0. 
   which returns error when loading this ml file *) 

(* so, we add Unit as the argument *)
(** val pred'_on_O : __ -> nat 
let pred'_on_O _ =
  pred' O
*) 


Extraction "extract/pred.ml" pred' pred'_on_O. 










(*  ** Well-founded Recursion and Extraction *) 


Inductive Acc {A} (R:A->A->Prop) : A -> Prop :=
  | Acc_intro : forall x, (forall y, R y x -> Acc R y) -> Acc R x. 


Definition Acc_inv {A}(R:A->A->Prop) x Hacc : forall y, R y x -> Acc R y :=
  match Hacc as H in (Acc _ x) return forall y, R y x -> Acc R y with 
  | Acc_intro _ x f => f end. 

Fixpoint Acc_iter {A}(R:A->A->Prop)(P:A->Type)
  (f:forall x, (forall y, R y x -> P y) -> P x) x (Hacc:Acc R x) {struct Hacc} : P x := 
  f x (fun y (Hlt:R y x) => Acc_iter R P f y (Acc_inv R x Hacc y Hlt)) . 


Definition well_founded_induction {A}(R:A->A->Prop)
  (Rwf : forall x, Acc R x) (P:A->Type) 
  (F   : forall x, (forall y, R y x -> P y) -> P x) x : P x :=
  Acc_iter R P F x (Rwf x). 


Fixpoint div2 n := 
  match n with 
  | S(S p)  => S(div2 p) 
  | _       => 0          end. 
       
Lemma div2_lt : forall p, div2 (S p) < S p. 
Proof. intros.    
  cut (div2 (S p) < S p /\ div2 (S(S p)) < S (S p)). 
  - intuition. 
  - induction p; intuition. 
Qed. 

Definition log2_aux_F x : (forall y, y < x -> nat) -> nat :=
  match x with 
  | O     => fun _ => O 
  | S p   => fun f => S(f (div2(S p))(div2_lt p)) end.  

Lemma lt_wf : forall x, Acc lt x. 
Proof. 
induction x.  
- constructor. inversion 1.    
- constructor.  
  intros. 
  inversion IHx. 
  inversion H.  
  + assumption. 
  + auto with zarith.   
Qed. 

Definition log2_aux := 
  well_founded_induction _ lt_wf (fun _:nat => nat) log2_aux_F. 

Definition log2 x (h:x<>0) := log2_aux (pred x). 

Extraction "extract/wellfounded.ml" Acc_iter well_founded_induction log2. 

(** val acc_iter : ('a1 -> ('a1 -> __ -> 'a2) -> 'a2) -> 'a1 -> 'a2 
type __ = Obj.t

let rec acc_iter f x =
  f x (fun y _ -> acc_iter f y)
*)
(** val well_founded_induction :
    ('a1 -> ('a1 -> __ -> 'a2) -> 'a2) -> 'a1 -> 'a2 

let well_founded_induction =
  acc_iter
*) 








(* 10.1.3 Prop, Set, and Extraction *) 

(* Pattern Matching on Proofs *) 

(* the following definition is forbidden. 
Definition or_to_nat (A B:Prop) (H : A\/B) : nat := 
  match H with 
  | or_introl _ => S O 
  | or_intror _ => O    end. 
 *) 



(* Choosing Inductive Type *)
Reset sumbool. 

Definition sumbool_to_nat (A B:Prop) (v : {A}+{B}) : A \/ B := 
  match v with 
  | left  Ha  => or_introl B Ha
  | right Hb  => or_intror A Hb end.  

Extraction "extract/downgrading.ml" sumbool_to_nat. 





















(* Describing Imperative Programs *) 

(* 10.2.1 The "Why" Tool *)

(* 10.2.2 The Inner Workings of Why *) 

(* 10.2.2.1 Representing the State            *)
(* 10.2.2.2 Assignment                        *)
(* 10.2.2.3 Sequence                          *)
(* 10.2.2.4 Conditional Instructions          *)
(* 10.2.2.5 Loops                             *)
(* 10.2.2.6 Arrays                            *)
(* 10.2.2.7 An Elaborated Example: Insertion  *)
(* 10.2.2.8 Loop Invariants                   *)

Require Import ZArith. 

(* 10.2.2.1 Representing the State            *)
Record tuple : Set := mk_tuple { b:bool; x:Z }. 

(* 10.2.2.2 Assignment                        *)
(* ASSIGNMENT  x := e    ( e : tuple -> Z ) *) 

(*      fun t:tuple => mk_tuple t.(b)(e t).  *)



(* 10.2.2.3 Sequence                          *)
(* SEQUENCE    (f1; f2)  *) 

(*      fun t:tuple => f2 (f1 t) *) 



(* e.g.      b := false; x := 1         *)

Definition b_false_seq_x_1 := 
    fun t:tuple => 
        (fun t':tuple => mk_tuple (b t') 1) 
        ((fun t'':tuple => mk_tuple false (x t'')) t) . 



(* 10.2.2.4 Conditional Instructions          *)
(* IF e THEN f1 ELSE f2    *) 

(*      fun t:tuple => if e then f1 t else f2 t  *)  

(*      more precisely, assume there is e'' s.t.; *) 
(*      Variable e'' : forall t:tuple, {e t = true}+{e t = false}.
 *
 *      fun t:tuple => 
            match e'' t with left h => f1 t | right h' => f2 t end.  *) 


(* 10.2.2.5 Loops                             *)
Check Zgt_bool  .  (* Check Z.gtb. *)
Check Zgt_cases .  

Definition Zgt_bool' : forall x y:Z, {Zgt_bool x y =true} + {Zgt_bool x y = false}. 
Proof. intros x0 y0; case (Zgt_bool x0 y0); auto . Defined. 

Require Import Wellfounded (* Wf *) Zwf.  
Open Scope Z. 
Print Zwf. 
Check Zwf_well_founded. 
Check wf_inverse_image. 

Definition loop1' : 
    forall t : tuple, (forall t1:tuple, Zwf 0(x t1)(x t) -> tuple) -> tuple. 
Proof. 
  refine (fun (t:tuple) (loop:forall t', Zwf 0 (x t')(x t) -> tuple) => 
    match Zgt_bool' (x t) 0 with 
    | left  h   => loop (mk_tuple (b t)((x t) -1)) _ 
    | right h   => t                                  end ). 
  generalize (Zgt_cases (x t) 0); rewrite h; intros; simpl. 
  unfold Zwf; auto with zarith. 
Qed. 

Definition loop1 : tuple -> tuple :=
  well_founded_induction 
  (wf_inverse_image tuple Z (Zwf 0) x (Zwf_well_founded 0))
  (fun _ => tuple) loop1'. 




(* 10.2.2.6 Arrays                            *)
Parameter array   : Z -> Set -> Set . 


Parameter new     : forall  n {T:Set}, T -> array n T. 
Parameter access  : forall {n}{T:Set}, array n T -> Z -> T. 
Parameter store   : forall {n}{T:Set}, array n T -> Z -> T -> array n T. 

Axiom new_def     : forall n {T:Set}(v:T)i,           0<=i<n -> access (new n v) i = v.
Axiom store_def_1 : forall n {T:Set}(t:array n T)v i, 0<=i<n -> access (store t i v) i = v.
Axiom store_def_2 : forall n {T:Set}(t:array n T)v i j, 0<=i<n -> 0<=j<n -> 
                                                      access(store t i v)j = access t j. 

Parameter l : Z . 
Record tuple' : Set := mk_tuple' { a:array l Z; y:Z; z:Z}. 

Definition arrassign a i e := (fun (t:tuple') (h : 0<=i t<1) => 
  mk_tuple' (store (a t) (i t) (e t)) (y t)(z t)) (* p *) . 



(* 10.2.2.7 An Elaborated Example: Insertion  *)


(* 
  while z<l do 
    if y > z then 
      begin a[z-1] := a[z]; z:=z+1 end 
    else 
      begin a[z-1] := y; z = l end 
*)

Definition insert_loop : tuple' -> tuple'. 
Proof. 
  refine 
  (well_founded_induction
    (wf_inverse_image _ _ _ (fun t => l - z t) (Zwf_well_founded 0)) 
    _ 
    ( fun t (loop : forall t', Zwf 0 (l - z t')(l - z t) -> tuple') => 
          match Z_gt_le_dec l (z t) with 
          | left  Hloop  => match Z_gt_le_dec (y t)(z t) with 
                            | left  _ => 
                                (fun (h1 : 0 <= z t - 1 < l) 
                                     (h2 : 0 <= z t < l)   
                                  => loop ( mk_tuple' 
                                      ( store(a t)(z t-1)(access (a t)(z t)) )
                                      ( y t ) 
                                      ( z t + 1 )  ) _ ) _ _ 
                            | right _ => 
                                (fun (h1 : 0 <= z t < l) 
                                  => loop ( mk_tuple'
                                      ( store(a t)(z t-1)(y t))
                                      ( y t )
                                      ( l   ) ) _ ) _ end 
          | right Hbreak => t   end )
  ). 
  (* 5 Goals cannot be solved without the condition the values of Z are positive *)  
Abort. 


(* 10.2.2.8 Loop Invariants                   *)


Definition insert_loop : forall t:tuple', 0 < z t -> tuple'. 
Proof. 
  refine 
  (well_founded_induction
    (wf_inverse_image _ _ _ (fun t => l - z t) (Zwf_well_founded 0)) 
    _ 
    ( fun ( t : tuple')  
          ( loop : forall t', Zwf 0 (l - z t')(l - z t) -> 0 < z t' -> tuple') 
          ( h4 : 0 < z t ) => 
          match Z_gt_le_dec l (z t) with 
          | left  Hloop  => match Z_gt_le_dec (y t)(z t) with 
                            | left  _ => 
                                (fun (h1 : 0 <= z t - 1 < l) 
                                     (h2 : 0 <= z t < l)   
                                  => loop ( mk_tuple' 
                                      ( store(a t)(z t-1)(access (a t)(z t)) )
                                      ( y t ) 
                                      ( z t + 1 )  ) _ _ ) _ _ 
                            | right _ => 
                                (fun (h1 : 0 <= z t < l) 
                                  => loop ( mk_tuple'
                                      ( store(a t)(z t-1)(y t))
                                      ( y t )
                                      ( l   ) ) _ _ ) _ end 
          | right Hbreak => t   end )
  ). 
Admitted. 











