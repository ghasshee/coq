From mathcomp
Require Import ssreflect.

Section ModusPonens.
Variable X Y : Prop.

Hypothesis X_to_Y_is_true : X -> Y.
Hypothesis X_is_true : X.

Theorem MP : Y.
Proof.
move : X_is_true.
by [].
Qed.

End ModusPonens.

Section HilbertSAxiom.
Variables A B C : Prop.

Theorem HS1 : (A->(B->C))->((A->B)->(A->C)).
Proof.
move => AtoBtoC_is_true.
move => AtoB_is_true.
move => A_is_true.

apply: (MP B C).

apply: (MP A (B->C)).
by [].
by [].

apply: (MP A B).
by [].
by [].
Qed.

End HilbertSAxiom.




