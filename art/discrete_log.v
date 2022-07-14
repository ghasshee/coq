

(* ex. 6.26 *) 
Fixpoint discrete_log (n:positive) : nat := 
    match n with 
    | xH    => 0 
    | xI n' => 1 + discrete_log n' 
    | xO n' => 1 + discrete_log n'          end. 

Compute discrete_log 1024 . 



