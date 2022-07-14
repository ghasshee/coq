Require Import Arith ZArith Bool.


Open Scope Z_scope.

Locate "_ * _".

Print Scope Z_scope.

Check 33%nat.
Check  0%nat.
Check  0.

Open Scope nat_scope.

Check 33.
Check 0.
Check 33%Z.
Check (-12)%Z.

Reset Initial.

Require Import Arith ZArith Bool.

Open Scope Z_scope.

Check (-12).
Check (33%nat).
Check true.
Check false.
Check ifb.

Check plus.
Check Zplus.
Check negb.
Check orb.
Check andb.
Check S.
Check O.

Check negb.
Check (negb true).
Check (negb (negb true)).
Check (ifb (negb false) false true).

Open Scope nat_scope.

Check (S(S(S O))).
Check (mult (mult 5 (minus 5 3)) 7).
Check (5*(5-3)*7).

Unset Printing Notations.

Check 4.
Check (5*(5-3)*7).

Set Printing Notations.

Open Scope Z_scope.
Check (Zopp (Zmult 3 (Zminus (-5)(-8)))).

Open Scope nat_scope.

Check (plus 3).
Check (Zmult (-5)).
Check Zabs_nat.
Check (5 + Zabs_nat (5 - 19)).
Check (Zmult 3 (-45))%Z.

Check fun n:nat => (n*n*n)%nat.
Check fun (n p:nat)(z:Z) => (Z_of_nat(n+p)+z)%Z.

Check fun a b c:Z => (b*b-4*a*c)%Z.

Check fun (f g:nat->nat)(n:nat) => g (f n).