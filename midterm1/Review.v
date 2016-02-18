(** * Review: Midterm I  *)

Require Import Coq.omega.Omega.
Require Export Logic.

(* ####################################################### *)
(** 

Questions:

1.  Check (nat -> list nat)    :: Set
2.  are forall and exists necesary and sufficient to enclose
    a Prop? what type of expression are allowed to be inside a prop?
     Set, Prop or Type ??


    {Set | Prop } << Type << ... << Type_{n+1} << ..

*)


Check (nat -> list nat).

(* Check (forall n : nat, n). not ok since n in nat *)
Check (forall n:Type, n).     (* ok since n in type *)
Check (forall n:nat, n = n).  (* ok since [n=n] in prop *)

Inductive le : nat -> nat -> Prop :=
  | le_n : forall n, le n n
  | le_S : forall n m, (le n m) -> (le n (S m)).

Check (le 4).
Check (le_S 5 5).
Check (forall m : nat, le 5 m -> le 5 (S m)).


(* list a = nil | cons a (list a) *)

Inductive lists (X : Type) : Type :=
  | nils  : lists X
  | conss : X -> lists X -> lists X.          

Check (conss).             (* forall X : Type, X -> lists X -> lists X *)
Check (conss nat 12).      (* lists nat -> lists nat*)

Inductive or (P Q : Prop) : Prop :=
  | or_l :  P -> or P Q
  | or_r :  Q -> or P Q.

Check (or_l True).
                    