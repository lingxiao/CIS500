(* ---------------------------------------------------------------------------------------
------------------------------------------------------------------------------------------
-- | 
-- | Module : Play
-- | Creator: Xiao Ling
-- | Date   : 1/13/2016
-- | Source : https://coq.inria.fr/tutorial-nahas
-- | Emacs  : C-c C-n to advance the proof
-- |          C-x C-number to tile windows
-- |          
-- |
----------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------*)

(*
  Trivial proof, introduce concept of `intros` and `exact`
  proposition: for all things you can prove,
               if you a proof of it, then you have a proof of it

  note the tactics:

  intros - takes forall off the front of the subgoal, binds forall X to some
           X? how do you know X exist? exist by hypothesis
           is X or A in this case a set or a term?
           in plain english, intros introduce hypothesis
           but what is proof_of_A? does it proof A? it doesn't seem to matter
           when I do proof_of_B vs proof_of_A?
  exact  - solves the subgoal

*)
Theorem my_first_proof : (forall A : Prop, A -> A).
Proof.
  intros A.
  intros proof_of_A.
  exact  proof_of_A.
Qed.


(*
  Forward Proof: introduce `pose`
  pose: used in forward proof, ie before pose (proof_of_B ...)
        the subgoal is B
        pose assigns result of (A implies B) and proof of A
        to new hypothesis proof of B
        so if A, and A => B, then B

        pose assigns logical implication between two arguments?
        but the logic exist outside of coq correct?
  
*)
Theorem forward_small : (forall A B : Prop, A -> (A -> B) -> B).
Proof.
  intros A.
  intros B.
  intros proof_of_A.
  intros A_implies_B.
  pose  (proof_of_B := A_implies_B proof_of_A).
  exact proof_of_B.
Qed.



(*
  Backwards proof: introduce `refine`
  refine: create proof of B without speifying the argument of A
          thus solving the current subgoal of type B and `_`
          becomes the new child subgoal
   
*)
Theorem backward_small : (forall A B : Prop, A -> (A -> B) -> B).
Proof.
  intros A B.
  intros proof_of_A A_implies_B.
  refine (A_implies_B _).
  exact  proof_of_A.
Qed.  


(*
  backwards proof
  goal: 
*)
Theorem backward_huge : (forall A B C : Prop, A -> (A -> B) -> (A -> B -> C) -> C).
Proof.
   intros A B C.
   intros proof_of_A A_imp_B A_imp_B_imp_C.
   refine (A_imp_B_imp_C _ _).
     exact proof_of_A.
     refine (A_imp_B _).
       exact proof_of_A.
Qed.  
















