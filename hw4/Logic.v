(** * Logic: Logic in Coq *)

Require Export Tactics.

(** In previous chapters, we have seen many examples of factual
    claims (_propositions_) and ways of presenting evidence of their
    truth (_proofs_).  In particular, we have worked extensively with
    _equality propositions_ of the form [e1 = e2], with
    implications ([P -> Q]), and with quantified propositions ([forall
    x, P]).  In this chapter, we will see how Coq can be used to carry
    out other familiar forms of logical reasoning.

    Before diving into details, let's talk a bit about the status of
    mathematical statements in Coq.  Recall that Coq is a _typed_
    language, which means that every sensible expression in its world
    has an associated type.  Logical claims are no exception: any
    statement we might try to prove in Coq has a type, namely [Prop],
    the type of _propositions_.  We can see this with the [Check]
    command: *)

Check 3 = 3.
(* ===> Prop *)


Check forall n m : nat, n + m = m + n.
(* ===> Prop *)

(** Note that all well-formed propositions have type [Prop] in Coq,
    regardless of whether they are true or not. Simply _being_ a
    proposition is one thing; being _provable_ is something else! *)

Check forall n : nat, n = 2.
(* ===> Prop *)

Check 3 = 4.
(* ===> Prop *)

(** Indeed, propositions don't just have types: they are _first-class
    objects_ that can be manipulated in the same ways as the other
    entities in Coq's world.  So far, we've seen one primary place
    that propositions can appear: in [Theorem] (and [Lemma] and
    [Example]) declarations. *)

Theorem plus_2_2_is_4 :
  2 + 2 = 4.
Proof. reflexivity.  Qed.

(** But propositions can be used in many other ways.  For example, we
    can give a name to a proposition using a [Definition], just as we
    have given names to expressions of other sorts. *)

Definition plus_fact : Prop  :=  2 + 2 = 4.
Check plus_fact.
(* ===> plus_fact : Prop *)

(** We can later use this name in any situation where a proposition is
    expected -- for example, as the claim in a [Theorem] declaration. *)

Theorem plus_fact_is_true :
  plus_fact.
Proof. reflexivity.  Qed.

(** We can also write _parameterized_ propositions -- that is,
    functions that take arguments of some type and return a
    proposition. For instance, the following function takes a number
    and returns a proposition asserting that this number is equal to
    three: *)

Definition is_three (n : nat) : Prop :=
  n = 3.
Check is_three.
(* ===> nat -> Prop *)

(** In Coq, functions that return propositions are said to define
    _properties_ of their arguments.  For instance, here's a
    polymorphic property defining the familiar notion of an _injective
    function_. *)

(* read: f is injective if forall x y. f x = f y -> x = y *)
Definition injective {A B} (f : A -> B) :=
  forall x y : A, f x = f y -> x = y.

Lemma succ_inj : injective S.
Proof.
  intros n m H. inversion H. reflexivity.
Qed.

(** The equality operator [=] that we have been using so far is also
    just a function that returns a [Prop]. The expression [n = m] is
    just syntactic sugar for [eq n m], defined using Coq's [Notation]
    mechanism. Because [=] can be used with elements of any type, it
    is also polymorphic: *)

Check @eq.
(* ===> forall A : Type, A -> A -> Prop *)

(** (Notice that we wrote [@eq] instead of [eq]: The type argument [A]
    to [eq] is declared as implicit, so we need to turn off implicit
    arguments to see the full type of [eq].) *)


(* #################################################################### *)
(** * Logical Connectives *)

(** ** Conjunction *)

(** The _conjunction_ or _logical and_ of propositions [A] and [B] is
    written [A /\ B], denoting the claim that both [A] and [B] are
    true. *)

Example and_example : 3 + 4 = 7 /\ 2 * 2 = 4.

(** To prove a conjunction, use the [split] tactic.  Its effect is to
    generate two subgoals, one for each part of the statement: *)

Proof.
  split.
  - (* 3 + 4 = 7 *) reflexivity.
  - (* 2 + 2 = 4 *) reflexivity.
Qed.

(** More generally, the following principle works for any two
    propositions [A] and [B]: *)

Lemma and_intro : forall A B : Prop, A -> B -> A /\ B.
Proof.
  intros A B HA HB. split.
  - apply HA.
  - apply HB.
Qed.

(** A logical statement with multiple arrows is just a theorem with
    has several hypotheses.  Here, [and_intro] says that, for any
    propositions [A] and [B], if we assume that [A] is true and we
    assume that [B] is true, then [A /\ B] is also true.

    Since applying a theorem with hypotheses to some goal has the
    effect of generating as many subgoals as there are hypotheses for
    that theorem, we can, apply [and_intro] to achieve the same effect
    as [split].
*)

Example and_example' : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  (* suppose and_intro is true *)
  apply and_intro.
  (* now it suffices to show [3 + 4 = 6] and [2 * 2 = 4] are true *)
  - (* 3 + 4 = 7 *) reflexivity.
  - (* 2 + 2 = 4 *) reflexivity.
Qed.

(** **** Exercise: 2 stars (and_exercise)  *)
Example and_exercise :
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros n m. induction n.
    + intros H. split.
        - reflexivity.
        - simpl in H. apply H.
    + intros contra. inversion contra.
Qed.      

(** So much for proving conjunctive statements.  To go in the other
    direction -- i.e., to _use_ a conjunctive hypothesis to prove
    something else -- we employ the [destruct] tactic.

    If the proof context contains a hypothesis [H] of the form [A /\
    B], writing [destruct H as [HA HB]] will remove [H] from the
    context and add two new hypotheses: [HA], stating that [A] is
    true, and [HB], stating that [B] is true.  For instance: *)

Lemma and_example2 :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m H.
  destruct H as [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

(** As usual, we can also destruct [H] when we introduce it instead of
    introducing and then destructing it: *)

Lemma and_example2' :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m [Hn Hm].   (* pattern match in intro directly *)
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

(** You may wonder why we bothered packing the two hypotheses [n = 0]
    and [m = 0] into a single conjunction, since we could have also
    stated the theorem with two separate premises: *)

Lemma and_example2'' :
  forall n m : nat, n = 0 -> m = 0 -> n + m = 0.
Proof.
  intros n m Hn Hm.
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

(** In this case, there is not much difference between the two
    theorems.  But it is often necessary to explicitly decompose
    conjunctions that arise from intermediate steps in proofs,
    especially in bigger developments.  Here's a simplified
    example: *)

Lemma and_example3 :
  forall n m : nat, n + m = 0 -> n * m = 0.
Proof.
  intros n m H.
  assert (H' : n = 0 /\ m = 0).
  { apply and_exercise. apply H. }  (*   forall n m : nat, n + m = 0 -> n = 0 /\ m = 0 *)
  destruct H' as [Hn Hm].
  rewrite Hn. reflexivity.
Qed.

(** Another common situation with conjunctions is that we know [A /\
    B] but in some context we need just [A] (or just [B]).  The
    following lemmas are useful in such cases: *)

Lemma proj1 : forall P Q : Prop,
  P /\ Q -> P.
Proof.
  intros P Q [HP HQ].
  apply HP.
Qed.

(** **** Exercise: 1 star, optional (proj2)  *)
Lemma proj2 : forall P Q : Prop,
  P /\ Q -> Q.
Proof.
  intros P Q [_ HQ].
  apply HQ.
Qed.  

(** Finally, we sometimes need to rearrange the order of conjunctions
    and/or the grouping of conjuncts in multi-way conjunctions.  The
    following commutativity and associativity theorems come in handy
    in such cases. *)

Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  (* WORKED IN CLASS *)
  intros P Q [HP HQ].
  split.
    - (* left *) apply HQ.
    - (* right *) apply HP.
Qed.
  
(** **** Exercise: 2 stars (and_assoc)  *)
(** (In the following proof of associativity, notice how the _nested_
    intro pattern breaks the hypothesis [H : P /\ (Q /\ R)] down into
    [HP : P], [HQ : Q], and [HR : R].  Finish the proof from
    there.) *)

Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]].
  split. split.
  apply HP. apply HQ. apply HR.
Qed.


(** By the way, the infix notation [/\] is actually just syntactic
    sugar for [and A B].  That is, [and] is a Coq operator that takes
    two propositions as arguments and yields a proposition. *)

Check and.
Check or.
(* ===> and : Prop -> Prop -> Prop *)
(* ===> or  : Prop -> Prop -> Prop *)

(** ** Disjunction *)

(** Another important connective is the _disjunction_, or _logical or_
    of two propositions: [A \/ B] is true when either [A] or [B]
    is.  (Alternatively, we can write [or A B], where [or : Prop ->
    Prop -> Prop].)

    To use a disjunctive hypothesis in a proof, we proceed by case
    analysis, which, as for [nat] or other data types, can be done
    with [destruct] or [intros].  Here is an example: *)

Lemma or_example :
  forall n m : nat, n = 0 \/ m = 0 -> n * m = 0.
Proof.
  (* This pattern implicitly does case analysis on
     [n = 0 \/ m = 0] *)
  intros n m [Hn | Hm].
  - (* Here, [n = 0] *)
    rewrite Hn. reflexivity.
  - (* Here, [m = 0] *)
    rewrite Hm. rewrite <- mult_n_O.
    reflexivity.
Qed.

(** We can see in this example that, when we perform case analysis on
    a disjunction [A \/ B], we must satisfy two proof obligations,
    each showing that the conclusion holds under a different
    assumption -- [A] in the first subgoal and [B] in the second.
    Note that the case analysis pattern ([Hn | Hm]) allows us to name
    the hypothesis that is generated in each subgoal.

    Conversely, to show that a disjunction holds, we need to show that
    one of its sides does. This is done via two tactics, [left] and
    [right].  As their names imply, the first one requires proving the
    left side of the disjunction, while the second requires proving
    its right side.  Here is a trivial use... *)

Lemma or_intro : forall A B : Prop, A -> A \/ B.
Proof.
  intros A B HA.
  left.
  apply HA.
Qed.

(** ... and a slightly more interesting example requiring the use of
    both [left] and [right]: *)

Lemma zero_or_succ :
  forall n : nat, n = 0 \/ n = S (pred n).
Proof.
  intros [|n].
  - left. reflexivity.
  - right. reflexivity.
Qed.


(* to ask: why doesn't this work? 
Lemma blah: forall n m, n = 0 \/ m = 0.
Proof.
  (*apply or_intro.*)
*)


(*Lemma or_example :
  forall n m : nat, n = 0 \/ m = 0 -> n * m = 0.*)

(** **** Exercise: 1 star (mult_eq_0)  *)
Lemma mult_eq_0 :
  forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n m. destruct n as [|n']. 
    + intros _. left. reflexivity.
    + destruct m as [|m'].
        - intros _. right. reflexivity.
        - intros contra. inversion contra.
Qed.      

(** **** Exercise: 1 star (or_commut)  *)
Theorem or_commut : forall P Q : Prop,
  P \/ Q  -> Q \/ P.
Proof.
  intros P Q [HP | HQ].
    - right. apply HP.
    - left.  apply HQ.
Qed.

(** ** Falsehood and Negation *)

(** So far, we have mostly been concerned with proving that certain
    things are _true_ -- addition is commutative, appending lists is
    associative, etc.  Of course, we may also be interested in
    _negative_ results, showing that certain propositions are _not_
    true. In Coq, such negative statements are expressed with the
    negation operator [~].

    To see how negation works, recall the discussion of the _principle
    of explosion_ from the [Tactics] chapter; it asserts that, if we
    assume a contradiction, then any other proposition can be derived.
    Following this intuition, we could define [~ P] ("not [P]") as
    [forall Q, P -> Q].  Coq actually makes a slightly different
    choice, defining [~ P] as [P -> False], where [False] is a
    _particular_ contradictory proposition defined in the standard
    library. *)

Module MyNot.

  Definition not (P:Prop) := P -> False.

  Notation "~ x" := (not x) : type_scope.

  Check not.
  (* ===> Prop -> Prop *)

End MyNot.

(** Since [False] is a contradictory proposition, the principle of
    explosion also applies to it. If we get [False] into the proof
    context, we can [destruct] it to complete any goal: *)

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  (* WORKED IN CLASS *)
  intros P contra.
  (* also [inversion contra] *)
  destruct contra.
Qed.

(** The Latin _ex falso quodlibet_ means, literally, "from falsehood
    follows whatever you like"; this is another common name for the
    principle of explosion. *)

(** **** Exercise: 2 stars, optional (not_implies_our_not)  *)
(** Show that Coq's definition of negation implies the intuitive one
    mentioned above: *)

(* to ask: what is the logic here?  *)
Fact not_implies_our_not : forall (P:Prop),
  ~ P -> (forall (Q:Prop), P -> Q).
Proof.
  intros P h Q p.
  (* and we are left with P, contradicting ~P*)
  destruct h.
  apply p.
Qed.
  

(** This is how we use [not] to state that [0] and [1] are different
    elements of [nat]: *)

Theorem zero_not_one : ~(0 = 1).
Proof.
  unfold not. intros contra. inversion contra.
  (* intros contra. inversion contra.*)
Qed.

(** Such inequality statements are frequent enough to warrant a
    special notation, [x <> y]: *)

Check (0 <> 1).
(* ===> Prop *)

Theorem zero_not_one' : 0 <> 1.
Proof.
  (* unfold not. intros H. inversion H.*)
  intros H. inversion H.
Qed.

(** It takes a little practice to get used to working with negation in
    Coq.  Even though you can see perfectly well why a statement
    involving negation is true, it can be a little tricky at first to
    get things into the right configuration so that Coq can understand
    it!  Here are proofs of a few familiar facts to get you warmed
    up. *)

Theorem not_False :
  ~ False.
Proof.
  unfold not. intros H. destruct H.
Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
  (* WORKED IN CLASS *)
  intros P Q [HP HNA]. unfold not in HNA.
  apply HNA in HP. inversion HP.
Qed.

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  (* WORKED IN CLASS *)
  intros P H. unfold not. intros G.
  (* apply G in H. inversion H.*)
  apply G. 
  apply H.
Qed.

(** **** class quiz 
Theorem class_quiz : forall (X : Type) (a b : X),
  a = b /\ a /= b -> false.                       
Proof.
*)
  
(** **** Exercise: 2 stars, advanced, recommended (double_neg_inf)  *)
(** Write an informal proof of [double_neg]:

   _Theorem_: [P] implies [~~P], for any proposition [P].

   _Proof_:   By  definition of ~ we have
                   P ==> ~~ P  :=   P ==> (P ==> False) ==> False

              Suppose we have some P, let P implies False as hypothesized.
              But since we know P and we know P ==> False, we
              may conclude False. Since False leads to any conclusion,
              we are done.
   []
*)

(** **** Exercise: 2 stars, recommended (contrapositive)  *)
Theorem contrapositive : forall P Q : Prop,
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q H G.
  unfold not in G. unfold not. intros P1.
  apply H in P1. apply G in P1. inversion P1.
Qed.  


(** **** Exercise: 1 star (not_both_true_and_false)  *)
Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof.
  intros P. unfold not. intros [H1 H2].
  apply H2 in H1. inversion H1.
Qed. 

(** **** Exercise: 1 star, advanced (informal_not_PNP)  *)
(** Write an informal proof (in English) of the proposition [forall P
    : Prop, ~(P /\ ~P)]. *)

(*
    Proof.
    By definition of [~] we have:
         forall P. (P /\ (P ==> False)) ==> False

    So suppose we have some P, as well as:  P and (P -> False), then we
    have to show this premise implies False.
    But if we have P and P implies False then we are left with False as desired.
    
    []      


*)

(** Similarly, since inequality involves a negation, it requires a
    little practice to be able to work with it fluently.  Here is one
    useful trick.  If you are trying to prove a goal that is
    nonsensical (e.g., the goal state is [false = true]), apply
    [ex_falso_quodlibet] to change the goal to [False].  This makes it
    easier to use assumptions of the form [~P] that may be available
    in the context -- in particular, assumptions of the form
    [x<>y]. *)

Theorem not_true_is_false : forall b : bool,
  b <> true -> b = false.
Proof.
  intros [] H.
  - (* b = true *)
    unfold not in H.
    apply ex_falso_quodlibet.
    apply H. reflexivity.
  - (* b = false *)
    reflexivity.
Qed.

(** Since reasoning with [ex_falso_quodlibet] is quite common, Coq
    provides a built-in tactic, [exfalso], for applying it. *)

Theorem not_true_is_false' : forall b : bool,
  b <> true -> b = false.
Proof.
  (*intros b H. destruct b.*)
  intros [] H.
  - (* b = false *)
    unfold not in H.
    exfalso.                (* <=== *)
    apply H. reflexivity.
  - (* b = true *) reflexivity.
Qed.





(** ** Truth *)

(** Besides [False], Coq's standard library also defines [True], a
    proposition that is trivially true. To prove it, we use the
    predefined constant [I : True]: *)

Lemma True_is_true : True.
Proof. apply I. Qed.

(** Unlike [False], which is used extensively, [True] is used quite
    rarely, since it is trivial (and therefore uninteresting) to prove
    as a goal, and it carries no useful information as a hypothesis.
    But it can be quite useful when defining complex [Prop]s using
    conditionals or as a parameter to higher-order [Prop]s.  We will
    see some examples such uses of [True] later on. *)

(** ** Logical Equivalence *)

(** The handy "if and only if" connective, which asserts that two
    propositions have the same truth value, is just the conjunction of
    two implications. *)

Module MyIff.

  Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

  Notation "P <-> Q" := (iff P Q)
                      (at level 95, no associativity)
                      : type_scope.

End MyIff.

Theorem iff_sym : forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).
Proof.
  (* WORKED IN CLASS *)
  intros P Q [HAB HBA].
  split.
  - (* -> *) apply HBA.
  - (* <- *) apply HAB.
Qed.

Lemma not_true_iff_false : forall b,
  b <> true <-> b = false.
Proof.
  (* WORKED IN CLASS *)
  intros b. split.
  - (* -> *) apply not_true_is_false.
  - (* <- *)
    intros H. rewrite H. intros H'. inversion H'.
Qed.

(** **** Exercise: 1 star, optional (iff_properties)  *)
(** Using the above proof that [<->] is symmetric ([iff_sym]) as
    a guide, prove that it is also reflexive and transitive. *)

Theorem iff_refl : forall P : Prop,
  P <-> P.
Proof.
  intros P. split.
    + intros P1. apply P1.
    + intros P1. apply P1.
Qed.  


Theorem iff_trans : forall P Q R : Prop,
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  intros P Q R [H1a H1b] [H2a H2b]. split.
    + intros H. apply H1a in H. apply H2a in H. apply H.
    + intros H. apply H2b in H. apply H1b in H. apply H.
Qed.      
   

(** **** Exercise: 3 stars (or_distributes_over_and)  *)
Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros. split.
    + intros [Hp | [Hq Hr]].
        - split.
            * left. apply Hp.
            * left. apply Hp.
        - split.
            * right. apply Hq.
            * right. apply Hr.
   + intros [[Hp | Hq] [Hp1 | Hr]].
        - left. apply Hp.
        - left. apply Hp.
        - left. apply Hp1.
        - right. split.
            * apply Hq.
            * apply Hr.
Qed.
 
  

(** Some of Coq's tactics treat [iff] statements specially, avoiding
    the need for some low-level proof-state manipulation.  In
    particular, [rewrite] and [reflexivity] can be used with [iff]
    statements, not just equalities.  To enable this behavior, we need
    to import a special Coq library that allows rewriting with other
    formulas besides equality: *)

(* to ask: understand this section, some more how to use coq stuff *)
Require Import Coq.Setoids.Setoid.

(** Here is a simple example demonstrating how these tactics work with
    [iff].  First, let's prove a couple of basic iff equivalences: *)

Lemma mult_0 : forall n m, n * m = 0 <-> n = 0 \/ m = 0.
Proof.
  split.
  - apply mult_eq_0.
  - apply or_example.
Qed.

Lemma or_assoc :
  forall P Q R : Prop, P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  intros P Q R. split.
  - intros [H | [H | H]].
    + left. left. apply H.
    + left. right. apply H.
    + right. apply H.
  - intros [[H | H] | H].
    + left. apply H.
    + right. left. apply H.
    + right. right. apply H.
Qed.

(** We can now use these facts with [rewrite] and [reflexivity] to
    give smooth proofs of statements involving equivalences.  Here is
    a ternary version of the previous [mult_0] result: *)

Lemma mult_0_3 :
  forall n m p, n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
  intros n m p.
  rewrite mult_0. rewrite mult_0. rewrite or_assoc.
  reflexivity.
Qed.

(** The [apply] tactic can also be used with [<->]. When given an
    equivalence as its argument, [apply] tries to guess which side of
    the equivalence to use. *)

Lemma apply_iff_example :
  forall n m : nat, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n m H. apply mult_0. apply H.
Qed.

(* ############################################################ *)
(** ** Existential Quantification *)

(** Another important logical connective is _existential
    quantification_.  To say that there is some [x] of type [T] such
    that some property [P] holds of [x], we write [exists x : T,
    P]. As with [forall], the type annotation [: T] can be omitted if
    Coq is able to infer from the context what the type of [x] should
    be.

    To prove a statement of the form [exists x, P], we must show that
    [P] holds for some specific choice of value for [x], known as the
    _witness_ of the existential.  This is done in two steps: First,
    we explicitly tell Coq which witness [t] we have in mind by
    invoking the tactic [exists t]; then we prove that [P] holds after
    all occurrences of [x] are replaced by [t].  Here is an example: *)

Lemma four_is_even : exists n : nat, 4 = n + n.
Proof.
  exists 2. reflexivity.
Qed.

(** Conversely, if we have an existential hypothesis [exists x, P] in
    the context, we can destruct it to obtain a witness [x] and a
    hypothesis stating that [P] holds of [x]. *)

Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o). 
Proof.
  intros n [m Hm]. 
  exists (2 + m). 
  apply Hm.
Qed.

(** **** Exercise: 1 star (dist_not_exists)  *)
(** Prove that "[P] holds for all [x]" implies "there is no [x] for
    which [P] does not hold." *)

Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  intros X P H1.
  unfold not. intros [x Hx].
  apply Hx. apply H1.
Qed.  


(** **** Exercise: 2 stars (dist_exists_or)  *)
(** Prove that existential quantification distributes over
    disjunction. *)

Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros X P Q. split.
    + intros [x [Px | Qx]].
        - left. exists x. apply Px.
        - right. exists x. apply Qx.
    + intros [[x Px] | [x Qx]].  
        - exists x.  left.  apply Px.
        - exists x. right. apply Qx.
Qed.                 

(* #################################################################### *)
(** * Programming with Propositions *)

(** The logical connectives that we have seen provide a rich
    vocabulary for defining complex propositions from simpler ones.
    To illustrate, let's look at how to express the claim that an
    element [x] occurs in a list [l].  Notice that this property has a
    simple recursive structure:

    - If [l] is the empty list, then [x] cannot occur on it, so the
      property "[x] appears in [l]" is simply false.

    - Otherwise, [l] has the form [x' :: l'].  In this case, [x]
      occurs in [l] if either it is equal to [x'] or it occurs in
      [l']. *)

(** We can translate this directly into a straightforward Coq
    function, [In].  (It can also be found in the Coq standard
    library.) *)

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | []       => False
  | x' :: l' => x' = x \/ In x l'
  end.


(** When [In] is applied to a concrete list, it expands into a
    concrete sequence of nested conjunctions. *)

Example In_example_1 : In 4 [3; 4; 5].
Proof.
  simpl. (*  3 = 4 \/ 4 = 4 \/ 5 = 4 \/ False *)
  right. left. reflexivity.
Qed.

Example In_example_2 :
  forall n, In n [2; 4] ->
  exists n', n = 2 * n'.
Proof.
  simpl.
  intros n [H | [H | []]].
  - exists 1. rewrite <- H. reflexivity.
  - exists 2. rewrite <- H. reflexivity.
Qed.

(** (Notice the use of the empty pattern to discharge the last case
    _en passant_.) *)

(** We can also prove more generic, higher-level lemmas about [In].
    Note, in the next, how [In] starts out applied to a variable and
    only gets expanded when we do case analysis on this variable: *)

(*
  forall ...
  if x in l  then   f x  in  (f <$> l)
*)

Lemma In_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
    In x l ->
    In (f x) (map f l).
Proof.
  intros A B f l x.
  induction l as [|x' l' IHl'].
  - (* l = nil, contradiction *)
    simpl. intros [].
  - (* l = x' :: l' *)
    (*
            x' = x   \/  In x l'
       -> f x' = f x \/  In (f x) (map f l')
    *)
    simpl. intros [H1 | H2].
      + rewrite H1. left. reflexivity.
      + right. apply IHl'. apply H2.
Qed.

(** This way of defining propositions, though convenient in some
    cases, also has some drawbacks.  In particular, it is subject to
    Coq's usual restrictions regarding the definition of recursive
    functions, e.g., the requirement that they be "obviously
    terminating."  In the next chapter, we will see how to define
    propositions _inductively_, a different technique with its own set
    of strengths and limitations. *)

(** **** Exercise: 2 stars (In_map_iff)  *)
(*
   forall ...
   y is in (map f l)   <==>   there exists x so that f x = y  and x is in l
*)
Lemma In_map_iff :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
    In y (map f l) <->
    exists x, f x = y /\ In x l.
Proof.
  intros A B f l y. split.

  + intros H. induction l as [|x' l'].
      - simpl in H. inversion H.
      - destruct H. exists x'. split.
          * apply H.
          * simpl. left. reflexivity.
          * apply IHl' in H. destruct H. exists x. split.
              { apply H. }
              { simpl. right. destruct H. apply H0.}

   + intros [x [H1 H2]]. induction l as [|x' l'].
       - simpl in H2. inversion H2.
       - simpl. destruct H2 as [H2l | H2r].
           * rewrite H2l in *. left. apply H1.
           * right. apply IHl'. apply H2r.
Qed.

  	

(** **** Exercise: 2 stars (in_app_iff)  *)
Lemma in_app_iff : forall A (l : list A) (l' : list A) (a:A),
  In a (l++l') <-> In a l \/ In a l'.
Proof.
  intros A l l' a. split.
    + induction l as [|x ls].
        - simpl. intros H. right. apply H.
        - simpl. intros [H1 | H2].
            * left. left. apply H1.
            * rewrite <- or_assoc. right. apply IHls. apply H2.
    + induction l as [|x' ls].
        - simpl. intros [H1 | H2].
            * inversion H1.
            * apply H2.
        - simpl. intros [[H1 | H2] | H3].
            * left. apply H1.
            * right. apply IHls. left. apply H2.
            * right. apply IHls. right. apply H3.
Qed.


(** **** Exercise: 3 stars (All)  *)
(** Recall that functions returning propositions can be seen as
    _properties_ of their arguments. For instance, if [P] has type
    [nat -> Prop], then [P n] states that property [P] holds of [n].

    Drawing inspiration from [In], write a recursive function [All]
    stating that some property [P] holds of all elements of a list
    [l]. To make sure your definition is correct, prove the [All_In]
    lemma below.  (Of course, your definition should _not_ just
    restate the left-hand side of [All_In].) *)


Fixpoint All {T} (P : T -> Prop) (l : list T) : Prop :=
  match l with
  | []       => True
  | x :: l'  => P x /\ All P l'
  end.                


(* recall In x (x' ::l') ==> x' \/ In x l' *)
Lemma All_In:
  forall (T : Type) (P : T -> Prop) (l : list T),
  (forall x, In x l -> P x)  <->  All P l.
Proof.
  intros T P l. split.
  
  (* first we consider the forward direction *)
  * intros H. induction l as [|x' l'].
      + simpl. apply I.  (* All P [] is true by def *)
      + simpl. split.    (* now we show All P ( x' :: l') => P x' /\ All P l' *)
         (* first we show P x' *)
        - apply H. simpl. left. reflexivity.     
         (* now we show All P l' *)
        - apply IHl'. intros x H2. apply H. simpl. right. apply H2.
          
  (* Now we consider the reverse direction
     All P l   ==> forall x. In x l -> P x
  *)
  * intros H x H2. induction l as [|x' l'].
      (* let l = [], then In x l = false *)
      + simpl in H2. inversion H2.
        (* now we have to show forall x. In x (x' :: l') -> P x *)
      + destruct H as [Hl Hr]. destruct H2 as [H2l | H2r].
        rewrite H2l in *.  apply Hl. apply IHl'. apply Hr. apply H2r.
Qed.      
    


          
(** **** Exercise: 3 stars (combine_odd_even)  *)
(** Complete the definition of the [combine_odd_even] function below.
    It takes as arguments two properties of numbers, [Podd] and
    [Peven], and it should return a property [P] such that [P n] is
    equivalent to [Podd n] when [n] is odd and equivalent to [Peven n]
    otherwise. *)

Definition combine_odd_even (Podd Peven : nat -> Prop) : nat -> Prop :=
  fun (n : nat)  => match (oddb n) with
  | true =>  Podd n
  | _    =>  Peven n
  end.                

(** To test your definition, prove the following facts: *)

Theorem combine_odd_even_intro :
  forall (Podd Peven : nat -> Prop) (n : nat),
    (oddb n = true -> Podd n) ->
    (oddb n = false -> Peven n) ->
    combine_odd_even Podd Peven n.
Proof.
  intros Podd Peven n H1 H2. induction n as [|n'].
    + apply H2. reflexivity.
    + unfold combine_odd_even. destruct (oddb (S n')).
        - apply H1. reflexivity.
        - apply H2. reflexivity.
Qed.


Theorem combine_odd_even_elim_odd :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = true ->
    Podd n.
Proof.
  intros Podd Peven n. unfold combine_odd_even. destruct (oddb n).
    + intros H _. apply H.
    + intros _ contra. inversion contra.
Qed.


Theorem combine_odd_even_elim_even :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = false ->
    Peven n.
Proof.
  intros Podd Peven n. unfold combine_odd_even. destruct (oddb n).
    + intros _ contra. inversion contra.
    + intros H _. apply H.
Qed.      


(* #################################################################### *)
(** * Applying Theorems to Arguments *)

(** One feature of Coq that distinguishes it from many other proof
    assistants is that it treats _proofs_ as first-class objects.

    There is a great deal to be said about this, but it is not
    necessary to understand it in detail in order to use Coq.  This
    section gives just a taste, while a deeper exploration can be
    found in the optional chapters [ProofObjects] and
    [IndPrinciples]. *)

(** We have seen that we can use the [Check] command to ask Coq to
    print the type of an expression.  We can also use [Check] to ask
    what theorem a particular identifier refers to. *)

Check plus_comm.
(* ===> forall n m : nat, n + m = m + n *)

(** Coq prints the _statement_ of the [plus_comm] theorem in the same
    way that it prints the _type_ of any term that we ask it to
    [Check].  Why?

    The reason is that the identifier [plus_comm] actually refers to a
    _proof object_ -- a data structure that represents a logical
    derivation establishing of the truth of the statement [forall n m
    : nat, n + m = m + n].  The type of this object _is_ the statement
    of the theorem that it is a proof of.

    Intuitively, this makes sense because the statement of a theorem
    tells us what we can use that theorem for, just as the type of a
    computational object tells us what we can do with that object --
    e.g., if we have a term of type [nat -> nat -> nat], we can give
    it two [nat]s as arguments and get a [nat] back.  Similarly, if we
    have an object of type [n = m -> n + n = m + m] and we provide it
    an "argument" of type [n = m], we can derive [n + n = m + m].

    Operationally, this analogy goes even further: by applying a
    theorem, as if it were a function, to hypotheses with matching
    types, we can specialize its result without having to resort to
    intermediate assertions.  For example, suppose we wanted to prove
    the following result: *)

Lemma plus_comm3 :
  forall n m p, n + (m + p) = (p + m) + n.

(** It appears at first sight that we ought to be able to prove this
    by rewriting with [plus_comm] twice to make the two sides match.
    The problem, however, is that the second [rewrite] will undo the
    effect of the first. *)

Proof.
  intros n m p.
  rewrite plus_comm.
  rewrite plus_comm.
  (* We are back where we started... *)

(** One simple way of fixing this problem, using only tools that we
    already know, is to use [assert] to derive a specialized version
    of [plus_comm] that can be used to rewrite exactly where we
    want. *)

  rewrite plus_comm.
  assert (H : m + p = p + m).
  { rewrite plus_comm. reflexivity. }
  rewrite H.
  reflexivity.
Qed.

(** A more elegant alternative is to apply [plus_comm] directly to the
    arguments we want to instantiate it with, in much the same way as
    we apply a polymorphic function to a type argument. *)

(* plus_comm : forall n m : nat, n + m = m + n *)
Lemma plus_comm3_take2 :
  forall n m p, n + (m + p) = (p + m) + n.
Proof.
  intros n m p.
  rewrite plus_comm.
  rewrite (plus_comm m).
  reflexivity.
Qed.

(** You can "use theorems as functions" in this way with almost all
    tactics that take a theorem name as an argument.  Note also that
    theorem application uses the same inference mechanisms as function
    application; thus, it is possible, for example, to supply
    wildcards as arguments to be inferred, or to declare some
    hypotheses to a theorem as implicit by default.  These features
    are illustrated in the proof below. *)


(*
 proj1      :  forall P Q : Prop, P /\ Q -> P. 
 In_map_iff :  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
    In y (map f l) <->
    exists x, f x = y /\ In x l.
*)
Example lemma_application_ex :
  forall {n : nat} {ns : list nat},
    In n (map (fun m => m * 0) ns) ->
    n = 0.
Proof.
  intros n ns H.
  destruct (proj1 _ _ (In_map_iff _ _ _ _ _) H)
           as [m [Hm _]].
  rewrite mult_0_r in Hm. rewrite <- Hm. reflexivity.
Qed.

(** We will see many more examples of the idioms from this section in
    later chapters. *)

(* #################################################################### *)
(** * Coq vs. Set Theory *)

(** Coq's logical core, the _Calculus of Inductive Constructions_,
    differs in some important ways from other formal systems that are
    used by mathematicians for writing down precise and rigorous
    proofs.  For example, in the most popular foundation for
    mainstream paper-and-pencil mathematics, Zermelo-Fraenkel Set
    Theory (ZFC), a mathematical object can potentially be a member of
    many different sets; a term in Coq's logic, on the other hand, is
    a member of at most one type.  This difference often leads to
    slightly different ways of capturing informal mathematical
    concepts, though these are by and large quite natural and easy to
    work with.  For example, instead of saying that a natural number
    [n] belongs to the set of even numbers, we would say in Coq that
    [ev n] holds, where [ev : nat -> Prop] is a property describing
    even numbers.

    However, there are some cases where translating standard
    mathematical reasoning into Coq can be either cumbersome or
    sometimes even impossible, unless we enrich the core logic with
    additional axioms.  We conclude this chapter with a brief
    discussion of some of the most significant differences between the
    two worlds. *)

(** ** Functional Extensionality

    The equality assertions that we have seen so far mostly have
    concerned elements of inductive types ([nat], [bool], etc.).  But
    since Coq's equality operator is polymorphic, these are not the
    only possibilities -- in particular, we can write propositions
    claiming that two _functions_ are equal to each other: *)

Example function_equality_ex : plus 3 = plus (pred 4).
Proof. reflexivity. Qed.

(** In common mathematical practice, two functions [f] and [g] are
    considered equal if they produce the same outputs:
    (forall x, f x = g x) -> f = g
    This is known as the principle of _functional extensionality_.

    Informally speaking, an "extensional property" is one that
    pertains to an object's observable behavior.  Thus, functional
    extensionality simply means that a function's identity is
    completely determined by what we can observe from it -- i.e., in
    Coq terms, the results we obtain after applying it.

    Functional extensionality is not part of Coq's basic axioms: the
    only way to show that two functions are equal is by
    simplification (as we did in the proof of [function_equality_ex]).
    But we can add it to Coq's core logic using the [Axiom]
    command. *)

(*
   note f and g might have different complexities thus
   their computational behavior might differ
*)
Axiom functional_extensionality : forall {X Y: Type}
                                    {f g : X -> Y},
  (forall (x:X), f x = g x) -> f = g.

(** Using [Axiom] has the same effect as stating a theorem and
    skipping its proof using [Admitted], but it alerts the reader that
    this isn't just something we're going to come back and fill in
    later!

    We can now invoke functional extensionality in proofs: *)

Lemma plus_comm_ext : plus = fun n m => m + n.
Proof.
  apply functional_extensionality. intros n.
  apply functional_extensionality. intros m.
  apply plus_comm.
Qed.

(** Naturally, we must be careful when adding new axioms into Coq's
    logic, as they may render it inconsistent -- that is, it may
    become possible to prove every proposition, including [False]!
    Unfortunately, there is no simple way of telling whether an axiom
    is safe: hard work is generally required to establish the
    consistency of any particular combination of axioms.  Fortunately,
    it is known that adding functional extensionality, in particular,
    _is_ consistent.

    Note that it is possible to check whether a particular proof
    relies on any additional axioms, using the [Print Assumptions]
    command. For instance, if we run it on [plus_comm_ext], we see
    that it uses [functional_extensionality]: *)

Print Assumptions plus_comm_ext.
(* ===>
     Axioms:
     functional_extensionality :
         forall (X Y : Type) (f g : X -> Y),
                (forall x : X, f x = g x) -> f = g *)

(** **** Exercise: 5 stars (tr_rev)  *)
(** One problem with the definition of the list-reversing function
    [rev] that we have is that it performs a call to [app] on each
    step; running [app] takes time asymptotically linear in the size
    of the list, which means that [rev] has quadratic running time.
    We can improve this with the following definition: *)

Fixpoint rev_append {X} (l1 l2 : list X) : list X :=
  match l1 with
  | []       => l2
  | x :: l1' => rev_append l1' (x :: l2)
  end.

Definition tr_rev {X} (l : list X) : list X :=
  rev_append l [].

(** This version is said to be _tail-recursive_, because the recursive
    call to the function is the last operation that needs to be
    performed (i.e., we don't have to execute [++] after the recursive
    call); a decent compiler will generate very efficient code in this
    case.  Prove that both definitions are indeed equivalent. *)

Lemma rev_append_empty_r : forall (X : Type) (l1 l2 : list X),
  rev_append l1 l2 = rev_append l1 [] ++ l2.
Proof.
  intros X l1. induction l1.
  - intros l2. destruct l2.
    + simpl. reflexivity.
    + simpl. reflexivity.
  - intros l2. induction l2.
    + simpl. rewrite -> app_nil_r. reflexivity.
    + simpl. rewrite -> IHl1.
      replace (rev_append l1 [x]) with (rev_append l1 [] ++ [x]).
      rewrite <- app_assoc. simpl. reflexivity.
      rewrite <- IHl1. reflexivity.
Qed.


Lemma rev_append_empty : forall (X : Type) (l1 l2 : list X),
  rev_append l1 l2 = rev_append l1 [] ++ l2.
Proof.
  intros X l1. induction l1 as [|x l1'].
    + intros l2. simpl. reflexivity.
    + intros l2. simpl. destruct l2 as [|y l2'].
        - rewrite app_nil_r. reflexivity.
        - replace (rev_append l1' [x]) with (rev_append l1' [] ++ [x]).
          rewrite <- app_assoc. simpl. apply IHl1'.
            * symmetry. apply IHl1'.
Qed.              

Lemma tr_rev_correct : forall X, @tr_rev X = @rev X.
Proof.
  intros X. apply functional_extensionality. 
  intros l. induction l as [|x l'].
    + unfold tr_rev. simpl. reflexivity.
    + simpl. rewrite <- IHl'. unfold tr_rev. simpl.
      apply rev_append_empty.
Qed.      
  

(** ** Propositions and Booleans *)

(**  AAA: I'm anticipating some of the discussion on evenness from
   the next chapter here. We can remove/adapt some of the material in
   IndProp.v soon. 
 *)
(*
    key: cannot write a boolean value function that does not terminate
         since function would not be total (ie does TM terminate)

         but can write Proposition that does not terminate. though
         it does not have proof.
*)


(** We've seen that Coq has two different ways of encoding logical
    facts: with _booleans_ (of type [bool]), and with
    _propositions_ (of type [Prop]). For instance, to claim that a
    number [n] is even, we can say either (1) that [evenb n] returns
    [true] or (2) that there exists some [k] such that [n = double k].
    Indeed, these two notions of evenness are equivalent, as can
    easily be shown with a couple of auxiliary lemmas (one of which is
    left as an exercise).

    We often say that the boolean [evenb n] _reflects_ the proposition
    [exists k, n = double k].  *)

Theorem evenb_double : forall k, evenb (double k) = true.
Proof.
  intros k. induction k as [|k' IHk'].
  - reflexivity.
  - simpl. apply IHk'.
Qed.

(** **** Exercise: 3 stars (evenb_double_conv)  *)

(*
  for every n, there is some k so that either
      - if n is even then n = 2k
      - or n is odd and   n = 1 + 2k

  Hint: Use the [evenb_S] lemma from [Induction.v].

  evenb_S : forall n : nat, evenb (S n) = negb (evenb n).

*)
Theorem evenb_double_conv : forall n,
  exists k, n = if evenb n then double k
                else S (double k).
Proof.
  intros n. induction n as [|n'].
    + exists 0. simpl. reflexivity.
    (* IHn' : exists k.  n' = if evenb n' then double k else S (double k) *)
    + rewrite evenb_S. destruct  (evenb n').
        (* case even n. IHn': exist k. n' = 2k, goal: S n' = 2k + 1  *)
        - destruct IHn'. simpl. exists x. rewrite H. reflexivity.
        (* case odd n. IHn': exist k. n' = 2k + 1, goal: S n' = 2k *)
        - destruct IHn'. simpl. exists (S x). rewrite H. simpl. reflexivity.
Qed.          
 

Theorem even_bool_prop : forall n,
  evenb n = true <-> exists k, n = double k.
Proof.
  intros n. split.
  - intros H. destruct (evenb_double_conv n) as [k Hk].
    rewrite Hk. rewrite H. exists k. reflexivity.
  - intros [k Hk]. rewrite Hk. apply evenb_double.
Qed.

(** Similarly, to state that two numbers [n] and [m] are equal, we can
    say either (1) that [beq_nat n m] returns [true] or (2) that [n =
    m].  These two notions are equivalent. *)


(*
   bool express computable property, and can use [simpl]
   to compute.
*)
Theorem beq_nat_true_iff : forall n1 n2 : nat,
  beq_nat n1 n2 = true <-> n1 = n2.
Proof.
  intros n1 n2. split.
  - apply beq_nat_true.
  - intros H. rewrite H. rewrite <- beq_nat_refl. reflexivity.
Qed.

(** However, while the boolean and propositional formulations of a
    claim are equivalent from a purely logical perspective, we have
    also seen that they need not be equivalent _operationally_.
    Equality provides an extreme example: knowing that [beq_nat n m =
    true] is generally of little help in the middle of a proof
    involving [n] and [m]; however, if we convert the statement to the
    equivalent form [n = m], we can rewrite with it.

    The case of even numbers is also interesting.  Recall that, when
    proving the backwards direction of
    [even_bool_prop] ([evenb_double], going from the propositional to
    the boolean claim), we used a simple induction on [k]).  On the
    other hand, the converse (the [evenb_double_conv] exercise)
    required a clever generalization, since we can't directly prove
    [(exists k, n = double k) -> evenb n = true].

    For these examples, the propositional claims were more useful than
    their boolean counterparts, but this is not always the case.  For
    instance, we cannot test whether a general proposition is true or
    not in a function definition; as a consequence, the following code
    fragment is rejected: *)

Fail Definition is_even_prime n :=
  if n = 2 then true
  else false.

(** Coq complains that [n = 2] has type [Prop], while it expects an
    elements of [bool] (or some other inductive type with two
    elements).  The reason for this error message has to do with the
    _computational_ nature of Coq's core language, which is designed
    so that every function that it can express is computable and
    total.  One reason for this is to allow the extraction of
    executable programs from Coq developments.  As a consequence,
    [Prop] in Coq does _not_ have a universal case analysis operation
    telling whether any given proposition is true or false, since such
    an operation would allow us to write non-computable functions.

    Although general non-computable properties cannot be phrased as
    boolean computations, it is worth noting that even many
    _computable_ properties are easier to express using [Prop] than
    [bool], since recursive function definitions are subject to
    significant restrictions in Coq.  For instance, the next chapter
    shows how to define the property that a regular expression matches
    a given string using [Prop].  Doing the same with [bool] would
    amount to writing a regular expression matcher, which would be
    more complicated, harder to understand, and harder to reason
    about.

    Conversely, an important side benefit of stating facts using
    booleans is enabling some proof automation through computation
    with Coq terms, a technique known as _proof by
    reflection_. Consider the following statement: *)

Example even_1000 : exists k, 1000 = double k.

(** The most direct proof of this fact is to give the value of [k]
    explicitly. *)
Proof. exists 500. reflexivity. Qed.

(** On the other hand, the proof of the corresponding boolean
    statement is even simpler: *)

Example even_1000' : evenb 1000 = true.
Proof. reflexivity. Qed.

(** What is interesting is that, since the two notions are equivalent,
    we can use the boolean formulation to prove the other one without
    mentioning 500 explicitly: *)

Example even_1000'' : exists k, 1000 = double k.
Proof. apply even_bool_prop. reflexivity. Qed.

(** Although we haven't gained much in terms of proof size in this
    case, larger proofs can often be made considerably simpler by the
    use of reflection.  As an extreme example, the Coq proof of the
    famous _4-color theorem_ uses reflection to reduce the analysis of
    hundreds of different cases to a boolean computation.  We won't
    cover reflection in great detail, but it serves as a good example
    showing the complementary strengths of booleans and general
    propositions. *)

(** **** Exercise: 2 stars (logical_connectives)  *)
(** The following lemmas relate the propositional connectives studied
    in this chapter to the corresponding boolean operations. *)

Lemma andb_true_iff : forall b1 b2:bool,
  b1 && b2 = true <-> b1 = true /\ b2 = true.
Proof.
  intros b1 b2. split.

  (* forward direction *)
  * destruct b1.
     + destruct b2.
        - intros _. split. reflexivity. reflexivity.
        - simpl. intros H. inversion H.
     + destruct b2.
        - simpl. intros H. inversion H.
        - simpl. intros H. inversion H.

  (* reverse direction *)
  * destruct b1.
      + destruct b2.
          - intros _. reflexivity.
          - simpl. intros H. destruct H. inversion H0.
      + destruct b2.
          - simpl. intros H. destruct H. inversion H.
          - simpl. intros H. destruct H. inversion H.
Qed.

  

Lemma orb_true_iff : forall b1 b2,
  b1 || b2 = true <-> b1 = true \/ b2 = true.
Proof.
  intros b1 b2. split.
  * destruct b1.
      + destruct b2.
          - simpl. intros _. left. reflexivity.
          - simpl. intros _. left. reflexivity.
      + destruct b2.
          - simpl. intros _. right. reflexivity.
          - simpl. intros. inversion H.

  * destruct b1.
      + destruct b2.
          - simpl. intros. reflexivity.
          - simpl. intros [H1|  H2]. reflexivity. inversion H2.
      + destruct b2.
          - simpl. intros [H1 | H2]. reflexivity. reflexivity.
          - intros [H1 | H2]. inversion H1. inversion H2.
Qed.             
            

(** **** Exercise: 1 star (beq_nat_false_iff)  *)
(** The following theorem is an alternate "negative" formulation of
    [beq_nat_true_iff] that is more convenient in certain
    situations (we'll see examples in later chapters). *)

Theorem f_equal : forall (A B : Type) (f: A -> B) (x y: A),
  x = y -> f x = f y.
Proof. intros A B f x y eq. rewrite eq.  reflexivity.  Qed.


Theorem beq_nat_false_iff : forall x y : nat,
  beq_nat x y = false <-> x <> y.
Proof.
  intros x. split.

  + generalize dependent y. induction x as [|x'].
      - destruct y as [|y'].
          * simpl. intros H. inversion H.
          * simpl. intros _. unfold not. intros H. inversion H.
      - destruct y as [|y'].
          * simpl. intros _. unfold not. intros H. inversion H.
          * simpl. intros H. apply IHx' in H. intro Hs.
            injection Hs. apply H.

  + generalize dependent y. induction x as [|x'].
      - destruct y as [|y'].
          * unfold not. simpl. intros H. exfalso. apply H. reflexivity.
          * simpl. intros _. reflexivity.
      - destruct y as [|y'].
          * simpl. intros _. reflexivity.
          * simpl. intros H. apply IHx'. intros Hs.
            unfold not in H. apply H. apply f_equal.
            apply Hs.
Qed.    


(** **** Exercise: 3 stars (beq_list)  *)
(** Given a boolean operator [beq] for testing equality of elements of
    some type [A], we can define a function [beq_list beq] for testing
    equality of lists with elements in [A].  Complete the definition
    of the [beq_list] function below.  To make sure that your
    definition is correct, prove the lemma [beq_list_true_iff]. *)

Check (forall (X : Type) (x y : X), x = y).


(* note: using a && b is much easier to prove than
         if then statement
*)
Fixpoint beq_list {A} (beq : A -> A -> bool)
                  (l1 l2 : list A) : bool :=
  match l1,l2 with
  | []      , []       => true
  | x :: l1', y :: l2' => beq x y && beq_list beq l1' l2' 
  | _       , _        => false                    
  end.                          


(*
   andb_true_iff forall b1 b2.  b1 && b2 = true <-> b1 = true /\ b2 = true.
*)
Lemma beq_list_true_iff :
  forall A (beq : A -> A -> bool),
    (forall a1 a2, beq a1 a2 = true <-> a1 = a2) ->
    forall l1 l2, beq_list beq l1 l2 = true <-> l1 = l2.
Proof.
  intros A. split.

    + generalize dependent l2. induction l1 as [|a1 l1'].
        - destruct l2.
            * reflexivity.
            * simpl. intros Hc. inversion Hc.
        - destruct l2 as [|a2 l2'].
            * simpl. intros Hc. inversion Hc.
            * simpl. intros Hl. apply andb_true_iff  in Hl.
              inversion Hl. apply H in H0. rewrite H0.
              apply IHl1' in H1. rewrite H1. reflexivity.

   + generalize dependent l2. induction l1 as [|a1 l1'].
        - destruct l2.
            * reflexivity.
            * simpl. intros Hc. inversion Hc.
        - destruct l2 as [|a2 l2'].
            * simpl. intros Hc. inversion Hc.
            * simpl. intros Hl. apply andb_true_iff. split.
                { inversion Hl. apply H. reflexivity.     }
                { apply IHl1'. inversion Hl. reflexivity. }
Qed. 


(*

Alternate proof that destructs l2 before split the iff.

Proof.
  intros A beq H1. intros l1. induction l1 as [|a1 l1'].
  + intros l2. destruct l2.
      - split.
          * simpl. intros _. reflexivity.
          * intros _. reflexivity.
      - split.
          * intros Hc. inversion Hc.
          * intros Hc. inversion Hc.
  + intros l2. destruct l2 as [|a2 l2'].
      - split.
          * intros Hc. inversion Hc.
          * intros Hc. inversion Hc.
      - split.
          * simpl. intros H2. apply andb_true_iff in H2.
            destruct H2 as [H2l H2r].
            apply IHl1' in H2r. apply H1 in H2l.
            rewrite H2l. rewrite H2r. reflexivity.
          * simpl. intros H2. apply andb_true_iff. split.
              { inversion H2. apply H1. reflexivity. }
              { apply IHl1'. inversion H2. reflexivity. }
Qed.              
*)


(** **** Exercise: 2 stars, recommended (All_forallb)  *)
(** Recall the function [forallb], from the exercise
    [forall_exists_challenge] in chapter [Tactics]: *)

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
  | []      => true
  | x :: l' => test x && forallb test l'
  end.

(** Prove the theorem below, which relates [forallb] to the [All]
    property of the above exercise. *)

Theorem andb_split : forall (b1 b2 : bool),
  b1 && b2 = true <-> b1 = true /\ b2 = true.
Proof.
  intros b1 b2. split.
    * destruct b1.
      + destruct b2.
         - intros _. split. reflexivity. reflexivity.
         - intros H. inversion H.
      + destruct b2.
         - intros H. inversion H.
         - intros H. inversion H. 
    * intros [H1 H2]. rewrite H1. rewrite H2. reflexivity.
Qed.          

Theorem forallb_true_iff : forall X test (l : list X),
   forallb test l = true <-> All (fun x => test x = true) l.
Proof.
  intros X test l. split.
    + induction l as [|x l'].
        - simpl. intros _. apply I.
        - simpl. intros H1. apply andb_split in H1. destruct H1. split.
          apply H. apply IHl' in H0. apply H0.

    + induction l as [|x l'].
        - simpl. intros _. reflexivity.
        - simpl. intros [H1 H2]. apply IHl' in H2.
          rewrite andb_split. split. apply H1. apply H2.
Qed.          

      
(** Are there any important properties of the function [forallb] which
    are not captured by your specification?

   No. [forallb] is total and [forallb_true_iff] specify its correctness.
   Since we are not concerned with time/space complexities of a function,
   there are no other properties we are interested in.
     

 *)


(** ** Classical vs. Constructive Logic *)

(** We have seen that it is not possible to test whether or not a
    proposition [P] holds while defining a Coq function.  You may be
    surprised to learn that a similar restriction applies to _proofs_!
    In other words, the following intuitive reasoning principle is not
    derivable in Coq: *)

Definition excluded_middle := forall P : Prop,
  P \/ ~ P.

(** To understand operationally why this is the case, recall that, to
    prove a statement of the form [P \/ Q], we use the [left] and
    [right] tactics, which effectively require knowing which side of
    the disjunction holds.  However, the universally quantified [P] in
    [excluded_middle] is an _arbitrary_ proposition, which we know
    nothing about.  We don't have enough information to choose which
    of [left] or [right] to apply, just as Coq doesn't have enough
    information to mechanically decide whether [P] holds or not inside
    a function.  On the other hand, if we happen to know that [P] is
    reflected in some boolean term [b], then knowing whether it holds
    or not is trivial: we just have to check the value of [b].  This
    leads to the following theorem: *)

(*
   any decidable proposition can have excluded middle
*)
Theorem restricted_excluded_middle : forall P (b : bool),
  (P <-> b = true) -> P \/ ~ P.
Proof.
  intros P [] H.
  - left. rewrite H. reflexivity.
  - right. rewrite H. intros contra. inversion contra.
Qed.

(** In particular, the excluded middle is valid for equations [n = m],
    between natural numbers [n] and [m].

    You may find it strange that the general excluded middle is not
    available by default in Coq; after all, any given claim must be
    either true or false.  Nonetheless, there is an advantage in not
    assuming the excluded middle: statements in Coq can make stronger
    claims than the analogous statements in standard mathematics.
    Notably, if there is a Coq proof of [exists x, P x], it is
    possible to explicitly exhibit a value of [x] for which we can
    prove [P x] -- in other words, every proof of existence is
    necessarily _constructive_.  Because of this, logics like Coq's,
    which do not assume the excluded middle, are referred to as
    _constructive logics_.  More conventional logical systems such as
    ZFC, in which the excluded middle does hold for arbitrary
    propositions, are referred to as _classical_.

    The following example illustrates why assuming the excluded middle
    may lead to non-constructive proofs: *)

(** _Claim_: There exist irrational numbers [a] and [b] such that [a ^
    b] is rational.

    _Proof_: It is not difficult to show that [sqrt 2] is irrational.
    If [sqrt 2 ^ sqrt 2] is rational, it suffices to take [a = b =
    sqrt 2] and we are done.  Otherwise, [sqrt 2 ^ sqrt 2] is
    irrational.  In this case, we can take [a = sqrt 2 ^ sqrt 2] and
    [b = sqrt 2], since [a ^ b = sqrt 2 ^ (sqrt 2 * sqrt 2) = sqrt 2 ^
    2 = 2].  []

    Do you see what happened here?  We used the excluded middle to
    consider separately the cases where [sqrt 2 ^ sqrt 2] is rational
    and where it is not, without knowing which one actually holds!
    Because of that, we wind up knowing that such [a] and [b] exist
    but we cannot determine what their actual values are (at least,
    using this line of argument).

    As useful as constructive logic is, it does have its limitations:
    There are many statements that can easily be proven in classical
    logic but that have much more complicated constructive proofs, and
    there are some that are known to have no constructive proof at
    all!  Fortunately, like functional extensionality, the excluded
    middle is known to be compatible with Coq's logic, allowing us to
    add it safely as an axiom.  However, we will not need to do so in
    this book: the results that we cover can be developed entirely
    within constructive logic at negligible extra cost.

    It takes some practice to understand which proof techniques must
    be avoided in constructive reasoning, but arguments by
    contradiction, in particular, are infamous for leading to
    non-constructive proofs.  Here's a typical example: suppose that
    we want to show that there exists [x] with some property [P],
    i.e., such that [P x].  We start by assuming that our conclusion
    is false; that is, [~ exists x, P x]. From this premise, it is not
    hard to derive [forall x, ~ P x].  If we manage to show that this
    intermediate fact results in a contradiction, we arrive at an
    existence proof without ever exhibiting a value of [x] for which
    [P x] holds!

    The technical flaw here, from a constructive standpoint, is that
    we claimed to prove [exists x, P x] using a proof of [~ ~ exists
    x, P x]. However, allowing ourselves to remove double negations
    from arbitrary statements is equivalent to assuming the excluded
    middle, as shown in one of the exercises below.  Thus, this line
    of reasoning cannot be encoded in Coq without assuming additional
    axioms. *)

(** **** Exercise: 3 stars (excluded_middle_irrefutable)  *)
(** The consistency of Coq with the general excluded middle axiom
    requires complicated reasoning that cannot be carried out within
    Coq itself.  However, the following theorem implies that it is
    always safe to assume a decidability axiom (i.e., an instance of
    excluded middle) for any _particular_ Prop [P].  Why? Because we
    cannot prove the negation of such an axiom; if we could, we would
    have both [~ (P \/ ~P)] and [~ ~ (P \/ ~P)], a contradiction. *)

Theorem excluded_middle_irrefutable:  forall (P:Prop),
  ~ ~ (P \/ ~ P).
Proof.
  intros P. unfold not.
  (* we want to show:  (P \/ (P -> False) -> False) -> False  *)
  intros H. apply H.
  right. intros p. apply H. left. apply p.
Qed.
  
  



(** **** Exercise: 3 stars, optional (not_exists_dist)  *)
(** It is a theorem of classical logic that the following two
    assertions are equivalent:
    ~ (exists x, ~ P x)
    forall x, P x
    The [dist_not_exists] theorem above proves one side of this
    equivalence. Interestingly, the other direction cannot be proved
    in constructive logic. Your job is to show that it is implied by
    the excluded middle.
*)

Theorem not_exists_dist :
  excluded_middle ->
  forall (X:Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 5 stars, advanced, optional (classical_axioms)  *)
(** For those who like a challenge, here is an exercise taken from the
    Coq'Art book by Bertot and Casteran (p. 123).  Each of the
    following four statements, together with [excluded_middle], can be
    considered as characterizing classical logic.  We can't prove any
    of them in Coq, but we can consistently add any one of them as an
    axiom if we wish to work in classical logic.

    Prove that all five propositions (these four plus
    [excluded_middle]) are equivalent. *)

Definition peirce := forall P Q: Prop,
  ((P->Q)->P)->P.
Definition double_negation_elimination := forall P:Prop,
  ~~P -> P.
Definition de_morgan_not_and_not := forall P Q:Prop,
  ~(~P /\ ~Q) -> P\/Q.
Definition implies_to_or := forall P Q:Prop,
  (P->Q) -> (~P\/Q).

(* FILL IN HERE *)
(** [] *)

(** $Date: 2015-08-11 12:03:04 -0400 (Tue, 11 Aug 2015) $ *)