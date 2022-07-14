Require Import ZArith. 

Record tuple : Set := mk_tuple { b:bool; x:Z }. 

(* ASSIGNMENT  x := e    ( e : tuple -> Z ) *) 

(*      fun t:tuple => mk_tuple t.(b)(e t).  *)



(* SEQUENCE    (f1; f2)  *) 

(*      fun t:tuple => f2 (f1 t) *) 



(* e.g.      b := false; x := 1         *)

Definition b_false_seq_x_1 := 
    fun t:tuple => 
        (fun t':tuple => mk_tuple (b t') 1) 
        ((fun t'':tuple => mk_tuple false (x t'')) t) . 



(* IF e THEN f1 ELSE f2    *) 

(*      fun t:tuple => if e then f1 t else f2 t  *)  

(*      more precisely, assume there is e'' s.t.; *) 
(*      Variable e'' : forall t:tuple, {e t = true}+{e t = false}.
 *
 *      fun t:tuple => 
            match e'' t with left h => f1 t | right h' => f2 t end.  *) 


Check Zgt_bool  .  (* Check Z.gtb. *)
Check Zgt_cases .  

Definition Zgt_bool' : forall x y:Z, {Zgt_bool x y =true} + {Zgt_bool x y = false}. 
    intros x0 y0; case (Zgt_bool x0 y0); auto . 
Defined. 

Require Import Wellfounded (* Wf *) Zwf.  
Open Scope Z. 
Print Zwf. 
Check Zwf_well_founded. 
Check wf_inverse_image. 


Definition loop1' : 
    forall t : tuple, (forall t1:tuple, Zwf 0(x t1)(x t) -> tuple) -> tuple. 
refine (fun (t:tuple) (loop:forall t', Zwf 0 (x t')(x t) -> tuple) => 
    match 











