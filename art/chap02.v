Require Import ZArith.
Open Scope Z_scope.


Section binomial_def.
    Variables   a b : Z .
    Definition  binomial z := a*z + b .
    Section trinomial_def.
        Variables c d : Z.
        Definition trinomial z := binomial z * z + c + d * 0.
    End trinomial_def.
End binomial_def. 

Print binomial. 
Print trinomial.




Definition Zsqr z         := z * z .
Definition double f (z:Z) := f (f z). 

Eval cbv delta            [double Zsqr] in double Zsqr . 
Eval cbv beta delta       [double Zsqr] in double Zsqr . 
Eval cbv zeta beta delta  [double Zsqr] in double Zsqr . 


Section h_def.
    Variables a b : Z.
    Let s := a + b . 
    Let d := a - b .
    Definition h := s * s + d * d .
End h_def.
Print h.

Eval cbv beta delta       [h]     in h 56 78 .
Eval cbv zeta beta delta  [h]     in h 56 78 .
Eval cbv zeta beta delta iota     in h 56 78 . 
Eval compute                      in h 56 78 . 
Compute                              h 56 78 .  

