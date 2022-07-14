
(********************************************) 
(*        eq_ind                            *)  
(********************************************) 
Theorem t' : 0 = 1 -> False.  Proof. discriminate. Qed. 
Definition refl_0 : 0 = 0 .   Proof. trivial. Defined.  

Print I . 
Print eq_ind. 

Compute eq_ind O (fun x => 0 = x) eq_refl O refl_0 . 
Compute eq_ind O (fun x => 0 = x) eq_refl O eq_refl . 

Definition eq_sym' : forall {A} (x y:A) (p:x=y), y=x. 
Proof. intros A x y p; rewrite p; reflexivity.  Defined. 

Definition eq_sym'' {A} (x y:A) (p:x=y) := eq_ind x (fun y=> y=x) eq_refl y p.

Theorem sym_correct : forall A x y p, eq_sym' (A:=A) x y p = eq_sym'' x y p.       
Proof. intros A x y p.  now rewrite p. Qed. 

Print eq_ind_r. 
Print eq_sym . 



