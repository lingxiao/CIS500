(** * Maps: Total and Partial Maps *)

(** _A lot of text needs written here_... *)

(** Maps (aka dictionaries) are ubiquitous data structures in software
    construction in general and, in particular, in the theory of
    programming languages.  We're going to need them in many places in
    the coming chapters.  They also make a nice case study using
    several of the ideas we've seen in previous chapters, including
    building data structures out of higher-order functions (from
    [Basics] and [Poly]) and the use of reflection in proofs (from
    [IndProp]).

    We'll define two flavors of maps: _total_ maps, which include a
    "default" element to be returned when a key being looked up
    doesn't exist in the map, and _partial_ maps, which return an
    [option].  The latter is defined in terms of the former (using
    [None] as the default element). *)

(* ###################################################################### *)
(** * Coq's Standard Library *)

(** One small digression before we start.  Unlike the chapters we have
    seen so far, this one is not going to [Import] the chapter before
    it (and, transitively, all the earlier chapters).  Instead, in
    this chapter and from now, on we're going to import the
    definitions and theorems we need directly from Coq's standard
    library stuff.  You should not notice much difference, though,
    because we've been careful to name our own definitions and
    theorems consistently with their counterparts in the standard
    library. *)

Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Logic.FunctionalExtensionality.

(** Documentation for the standard library can be found at
    http://coq.inria.fr/library/. *)
(**  What's the best way to search for things in the library?  
 *)

(* ###################################################################### *)
(** * Identifiers *)

(** First, we need a type of keys for our maps.  We repeat the
    definition of [id]s from the [Lists] chapter, plus the equality
    comparison function for [id]s and its fundamental property: *)

Inductive id : Type :=
  | Id : nat -> id.

Definition beq_id id1 id2 :=
  match id1,id2 with
    | Id n1, Id n2 => beq_nat n1 n2
  end.

Theorem beq_id_refl : forall id, true = beq_id id id.
Proof.
  intros [n]. simpl. rewrite <- beq_nat_refl.
  reflexivity. Qed.

Check ((Id 1) = (Id 2)).

(** The following useful property of [beq_id] follows from a similar
    lemma about numbers: *)

Theorem beq_id_true_iff : forall id1 id2 : id,
  beq_id id1 id2 = true <-> id1 = id2.
Proof.
   intros [n1] [n2].
   unfold beq_id.
   rewrite beq_nat_true_iff.
   split.
   - (* -> *) intros H. rewrite H. reflexivity.
   - (* <- *) intros H. inversion H. reflexivity.
Qed.

(** (Note that [beq_nat_true_iff] was not proved above; it can be
    found in the standard library.) *)

(** Similarly: *)

Theorem beq_id_false_iff : forall x y : id,
  beq_id x y = false <-> x <> y.
Proof.
  intros x y. rewrite <- beq_id_true_iff.
  rewrite not_true_iff_false. reflexivity. Qed.

(** Now this useful variant follows just by rewriting: *)

Theorem false_beq_id : forall x y : id,
   x <> y  -> beq_id x y = false.
Proof.
  intros x y. rewrite beq_id_false_iff.
  intros H. apply H. Qed.


(* ###################################################################### *)
(** * Total Maps *)

(** Our main job in this chapter is to build a definition of partial
    maps that is similar in behavior to the one we saw in the [Poly]
    chapter, plus accompanying lemmas about their behavior.  This time
    around, though, we're going to use _functions_ rather than lists
    of key-value pairs to build maps.  The advantage of this
    representation is that it offers a more _extensional_ view of
    maps, where two maps that respond to queries in the same way will
    be represented as literally the same thing (the same function),
    rather than just "equivalent" data structures.  This, in turn,
    simplifies proofs that use maps.

    We build partial maps in two steps.  First, we define a type of
    _total maps_ that return a default value when we look up a key
    that is not present in the map. *)

Definition total_map (A:Type) := id -> A.

(** Intuitively, a total map over an element type [A] _is_ just a
    function that can be used to look up [id]s, yielding [A]s.

    The function [t_empty] yields an empty total map, given a default
    element, which always returns the default element when applied to
    any id. *)

Definition t_empty {A:Type} (v : A) : total_map A :=
  (fun _ => v).


Compute ((t_empty false) (Id 1)).
Compute (total_map nat).


(** More interesting is the [update] function, which (as before) takes
    a map [m], a key [x], and a value [v] and returns a new map that
    takes [x] to [v] and takes every other key to whatever [m] does. *)

Definition t_update {A:Type} (m : total_map A)
                    (x : id) (v : A) :=
  fun x' => if beq_id x x' then v else m x'.

(** This definition is a nice example of higher-order programming.
    The [t_update] function takes a _function_ [m] and yields a new
    function [fun x' => ...] that behaves like the desired map.

    For example, we can build a map taking [id]s to [bool]s, where [Id
    3] is mapped to [true] and every other key is mapped to [false],
    like this: *)

Definition m0 := t_empty 0.
Definition m1 := t_update m0 (Id 1) 1.
Definition m2 := t_update m1 (Id 2) 2.
Definition m3 := t_update m2 (Id 2) 20.
Compute (m0 (Id 1)).
Compute (m1 (Id 1)).
Compute (m2 (Id 1)).
Compute (m2 (Id 2)).
Compute (m3 (Id 2)).


Definition examplemap :=
  t_update (t_update (t_empty false) (Id 1) false)
           (Id 3) true.

(** This completes the definition of total maps.  Note that we don't
    need to define a [find] operation because it is just function
    application! *)

Example update_example1 : examplemap (Id 0) = false.
Proof. reflexivity. Qed.

Example update_example2 : examplemap (Id 1) = false.
Proof. reflexivity. Qed.

Example update_example3 : examplemap (Id 2) = false.
Proof. reflexivity. Qed.

Example update_example4 : examplemap (Id 3) = true.
Proof. reflexivity. Qed.

(** To reason about maps in later chapters, we need to establish
    several fundamental facts about how they behave.  (Even if you
    don't work the following exercises, make sure you thoroughly
    understand the statements of the lemmas!)  Some of the proofs will
    require the functional extensionality axiom discussed in the
    [Logic] chapter. *)

(** **** Exercise: 2 stars, optional (t_update_eq)  *)
(** First, if we update a map [m] at a key [x] with a new value [v]
    and then look up [x] in the map resulting from the [update], we
    get back [v]: *)

Lemma t_update_eq : forall A (m: total_map A) x v,
  (t_update m x v) x = v.
Proof.
  intros. unfold t_update. destruct (beq_id x x).
    + reflexivity.
    + admit.
Qed.      
  
  

(** **** Exercise: 2 stars, optional (t_update_neq)  *)
(** On the other hand, if we update a map [m] at a key [x1] and then
    look up a _different_ key [x2] in the resulting map, we get the
    same result that [m] would have given: *)

Theorem t_update_neq : forall (X:Type) v x1 x2
                         (m : total_map X),
  x1 <> x2 ->
  (t_update m x1 v) x2 = m x2.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, optional (t_update_shadow)  *)
(** If we update a map [m] at a key [x1] with a value [v1] and then
    update again with the same key [x1] and another value [x2], then
    the resulting map behaves the same (i.e., it gives the same result
    whwn applied to any key [x2]) as the simpler map obtained by
    performing just the second [update] on [m]: *)

Lemma t_update_shadow : forall A (m: total_map A) v1 v2 x,
    t_update (t_update m x v1) x v2
  = t_update m x v2.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** For the final two lemmas about total maps, it is convenient to use
    the reflection idioms that we introduced in chapter [IndProp].  We
    begin by proving a fundamental _reflection lemma_ relating the
    equality proposition on [id]s with the boolean function
    [beq_id]. *)

(** **** Exercise: 2 stars (beq_idP)  *)
(** Use the proof of [beq_natP] in chapter [IndProp] as a template to
    prove the following: *)

Lemma beq_idP : forall x y, reflect (x = y) (beq_id x y).
Proof. 
  intros x y. apply iff_reflect. rewrite beq_id_true_iff. reflexivity.
Qed.  
                                                                 
(** Now, given [id]s [x1] and [x2], we can use the [destruct (beq_idP
    x1 x2)] to simultaneously perform case analysis on the result of
    [beq_id x1 x2] and generate hypotheses about the equality (in the
    sense of [=]) of [x1] and [x2]. *)

(** **** Exercise: 2 stars (t_update_same)  *)
(** Using the example in chapter [IndProp] as a template, use
    [beq_idP] to prove the following theorem, which states that if we
    update a map to assign key [x] the same value as it already has in
    [m], then the result is equal to [m]: *)

Definition n0 := t_empty 0.
Definition n1 := t_update n0 (Id 1) 12.
Definition n2 := t_update n1 (Id 1) (n1 (Id 1)).
Compute (n2 (Id 1)).


Theorem t_update_same : forall (X : Type)  (x : id) (m : total_map X),
  t_update m x (m x) = m.
Proof.
  intros. apply functional_extensionality.
  intros x'. unfold t_update. destruct (beq_id x x') eqn: Hb.
    + apply beq_id_true_iff in Hb. rewrite Hb. reflexivity.
    + reflexivity.
Qed.      

(*
Axiom functional_extensionality : ∀ {X Y: Type} {f g : X → Y},
  (∀(x:X), f x = g x) → f = g.
*)

(** **** Exercise: 3 stars, recommended (t_update_permute)  *)
(** Use [beq_idP] to prove one final property of the [update]
    function: If we update a map [m] at two distinct keys, it doesn't
    matter in which order we do the updates. *)

Theorem t_update_permute : forall (X:Type) v1 v2 x1 x2
                             (m : total_map X),
  x2 <> x1 ->
    (t_update (t_update m x2 v2) x1 v1)
  = (t_update (t_update m x1 v1) x2 v2).
Proof.
  intros. apply functional_extensionality. intros x.
  unfold t_update. destruct (beq_id x1 x) eqn: Hb1.
    + destruct (beq_id x2 x) eqn: Hb2.
        - apply beq_id_true_iff in Hb1. apply beq_id_true_iff in Hb2.
          subst. exfalso. apply H. reflexivity.
        - reflexivity.
    + destruct (beq_id x2 x) eqn: Hb2.
        - reflexivity.
        - reflexivity.
Qed.    


(* ###################################################################### *)
(** * Partial maps *)

(** Finally, we can define _partial maps_ on top of total maps.  A
    partial map with elements of type [A] is simply a total map with
    elements of type [option A] and default element [None]. *)

Definition partial_map (A:Type) := total_map (option A).

Definition empty {A:Type} : partial_map A :=
  t_empty None.

Definition update {A:Type} (m : partial_map A)
                  (x : id) (v : A) :=
  t_update m x (Some v).

(** We can now lift all of the basic lemmas about total maps to
    partial maps.  *)

Lemma update_eq : forall A (m: partial_map A) x v,
  (update m x v) x = Some v.
Proof.
  intros. unfold update. rewrite t_update_eq.
  reflexivity.
Qed.

Theorem update_neq : forall (X:Type) v x1 x2
                       (m : partial_map X),
  x2 <> x1 ->
  (update m x2 v) x1 = m x1.
Proof.
  intros X v x1 x2 m H.
  unfold update. rewrite t_update_neq. reflexivity.
  apply H. Qed.

Lemma update_shadow : forall A (m: partial_map A) v1 v2 x,
  update (update m x v1) x v2 = update m x v2.
Proof.
  intros A m v1 v2 x1. unfold update. rewrite t_update_shadow.
  reflexivity.
Qed.

Theorem update_same : forall X v x (m : partial_map X),
  m x = Some v ->
  update m x v = m.
Proof.
  intros X v x m H. unfold update. rewrite <- H.
  apply t_update_same.
Qed.

Theorem update_permute : forall (X:Type) v1 v2 x1 x2
                                (m : partial_map X),
  x2 <> x1 ->
    (update (update m x2 v2) x1 v1)
  = (update (update m x1 v1) x2 v2).
Proof.
  intros X v1 v2 x1 x2 m. unfold update.
  apply t_update_permute.
Qed.

(** $Date: 2015-12-11 17:17:29 -0500 (Fri, 11 Dec 2015) $ *)
