Require Import HoTT. 


Open Scope surreal_scope.  

Compute 1 + 1 . 

Locate "_ < _". 
Locate "1". 

Print Surreals.  
Print transport. 

Print Univalence.    
Print HoTT. 

Print Nat. 
Print Z. 

Compute 1 . 

Compute 1 < 2 . 
Print lt. 


Compute lt 1 2 .
Print lt. 
Open Scope nat_scope. 

Lemma hoge : 1 < 2 .  
Proof.  
    compute. trivial. 
Restart. 
    simpl. trivial.   
Restart. 
    Locate "_ < _". 
    unfold Nat.lt . 
    Locate "_ <= _". 
    Print leq. 
    unfold leq. 
    reflexivity.  
    Locate " =n ". 
    Print code_nat. 
Restart. 
    now simpl. 
Restart. 
    unfold Nat.lt. 
    unfold leq. 
    simpl. 
    Check Unit. 
    Print Unit. 
    exact tt.  
Defined.  

Print hoge. 

Print DHProp. 
Print hProp. (* (-1) - Type *)  
Print Decidable. 
Print dhprop_hprop. 


Compute leq 0 3. 
Compute leq 3 0. 

