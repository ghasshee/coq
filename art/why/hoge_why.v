(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)
Require Export Why.

(* Why obligation from file "sum.mlw", line 10, characters 13-26: *)
(*Why goal*) Lemma sum_po_1 : 
  forall (x: Z),
  forall (HW_1: 0 <= x),
  forall (HW_2: x = 0),
  forall (v: Z),
  forall (HW_3: v = 0),
  (3 * v) = (x * (x + 1)).
Proof.

(* FILL PROOF HERE *)
Save.

(* Why obligation from file "sum.mlw", line 8, characters 13-22: *)
(*Why goal*) Lemma sum_po_2 : 
  forall (x: Z),
  forall (HW_1: 0 <= x),
  forall (HW_4: x <> 0),
  (Zwf 0 (x - 1) x).
Proof.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "sum.mlw", line 8, characters 13-22: *)
(*Why goal*) Lemma sum_po_3 : 
  forall (x: Z),
  forall (HW_1: 0 <= x),
  forall (HW_4: x <> 0),
  forall (HW_5: (Zwf 0 (x - 1) x)),
  0 <= (x - 1).
Proof.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "sum.mlw", line 10, characters 13-26: *)
(*Why goal*) Lemma sum_po_4 : 
  forall (x: Z),
  forall (HW_1: 0 <= x),
  forall (HW_4: x <> 0),
  forall (HW_5: (Zwf 0 (x - 1) x)),
  forall (HW_6: 0 <= (x - 1)),
  forall (v: Z),
  forall (HW_7: (3 * v) = ((x - 1) * (x - 1 + 1))),
  forall (v0: Z),
  forall (HW_8: v0 = (x + v)),
  (3 * v0) = (x * (x + 1)).
Proof.
(* FILL PROOF HERE *)
Save.
