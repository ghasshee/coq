Require Import Arith. 

Parameters (prime_divisor : nat -> nat)
            (prime : nat -> Prop) 
            (divides : nat -> nat -> Prop). 

Open Scope nat_scope. 

Parameter binary_word : nat -> Set . 

Definition short : Set := binary_word 32. 
Definition long  : Set := binary_word 64. 



