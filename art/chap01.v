Require Import List ZArith. 
Open Scope Z_scope.

Inductive sorted : list Z -> Prop := 
  | sorted0 : sorted nil 
  | sorted1 : forall z:Z, sorted (z :: nil) 
  | sorted2 : forall (z1 z2:Z)(l:list Z), z1 <= z2 -> sorted (z2::l) -> sorted(z1 ::z2 :: l).

Hint Resolve sorted0 sorted1 sorted2 : sort.


Example sort_2357 :  sorted (2::3::5::7::nil).  
Proof. auto with sort zarith. Qed.

Theorem sorted_inv : forall (z:Z) l, sorted (z::l) -> sorted l.
Proof. inversion 1; auto with sort. Qed.


(* Number of occurence of z in l *)
Fixpoint nb_occ (z:Z) (l:list Z) {struct l} : nat :=
  match l with 
  | nil         => 0%nat
  | (z' :: l')  => match Z.eq_dec z z' with 
                    | left _    => S (nb_occ z l') 
                    | right _   => nb_occ z l'     end end.

Compute (nb_occ  3 (3::7::3::nil)).
Compute (nb_occ 36 (3::7::3::nil)).


