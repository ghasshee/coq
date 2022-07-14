Require Import Extraction ZArith . 


Extraction "pplus.ml" Pplus. 



Inductive positive : Set := 
    | xI : positive -> positive 
    | xO : positive -> positive 
    | xH : positive .

Extraction "positive.ml" positive. 






