From mathcomp
  Require Import ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. 

Section Logic. 

Lemma contrap : forall A B : Prop, (A -> B) -> (~B -> ~A).

Proof.
rewrite /not.
move => AO BO AtoB notB. (* assign the proposition types to variables *)
by move /AtoB. (* move AO ↦ BO then the top is Bo -> False , this is notB *) 
Qed.



Variables A B C : Prop .

Lemma AndOrDistL : (A /\ B) \/ (B /\ C) <-> (A \/ B) /\ C.

Proof. 
rewrite /iff.
apply: conj.
-case.
 +case => AisTrue BisTrue. 
by apply: conj; [apply  or_introl  | ].
 +case=> BisTrue CisTrue.
  by apply: conj; ]apply: or_intror | ].






