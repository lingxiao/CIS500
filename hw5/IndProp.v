(** * IndProp: Inductively Defined Propositions *)

Require Import Coq.omega.Omega.
Require Export Logic.

(* ####################################################### *)
(** * Inductively Defined Propositions *)

(** In the [Logic] chapter we looked at several ways of writing
    propositions, including conjunction, disjunction, and quantifiers.
    In this chapter, we bring a new tool into the mix: _inductive
    definitions_.

    Recall that we have seen two ways of stating that a number [n] is
    even: We can say (1) [evenb n = true], or (2) [exists k, n =
    double k].  Yet another possibility is to say that [n] is even if
    we can establish its evenness from the following rules:

       - Rule [ev_0]: The number [0] is even.
       - Rule [ev_SS]: If [n] is even, then [S (S n)] is even.

    To illustrate how this new definition of evenness works, let's use
    its rules to show that [4] is even. By rule [ev_SS], it suffices
    to show that [2] is even. This, in turn, is again guaranteed by
    rule [ev_SS], as long as we can show that [0] is even. But this
    last fact follows directly from the [ev_0] rule. *)

(** We will see many definitions like this one during the rest
    of the course.  For purposes of informal discussions, it is
    helpful to have a lightweight notation that makes them easy to
    read and write.  _Inference rules_ are one such notation: *)
(**
                              ------------                        (ev_0)
                                 ev 0

                                  ev n
                             --------------                      (ev_SS)
                              ev (S (S n))

*)

(** Each of the textual rules above is reformatted here as an
    inference rule; the intended reading is that, if the _premises_
    above the line all hold, then the _conclusion_ below the line
    follows.  For example, the rule [ev_SS] says that, if [n]
    satisfies [ev], then [S (S n)] also does.  If a rule has no
    premises above the line, then its conclusion holds
    unconditionally.

    We can represent a proof using these rules by combining rule
    applications into a _proof tree_. Here's how we might transcribe
    the above proof that [4] is even: *)
(**
                ------  (ev_0)
                 ev 0
                ------ (ev_SS)
                 ev 2
                ------ (ev_SS)
                 ev 4
*)
(** Why call this a "tree" (rather than a "stack", for example)?
    Because, in general, inference rules can have multiple premises.
    We will see examples of this below. *)

(** Putting all of this together, we can translate the definition of
    evenness into a formal Coq definition using an [Inductive]
    declaration, where each constructor corresponds to an inference
    rule: *)

(* enumerate of all direct proofs *)
Inductive ev : nat -> Prop :=
| ev_0  : ev 0
| ev_SS : forall n : nat, ev n -> ev (S (S n)).




Check (ev_0).
Check (ev_SS 12).
Check (ev_SS 1).  (* note this proposition does not reduce to ev 0 !*)

(*

 compare: 
  Inductive lists (X : Type) : Type :=
    | Nil  : lists X
    | cons : X -> lists X -> lists X.
*)


(** This definition is different in one crucial respect from
    previous uses of [Inductive]: its result is not a [Type], but
    rather a function from [nat] to [Prop] -- that is, a property of
    numbers.  Note that we've already seen other inductive definitions
    that result in functions, such as [list], whose type is [Type ->
    Type].  What is new here is that, because the [nat] argument of
    [ev] appears to the _right_ of the colon, it is allowed to take
    different values in the types of different constructors: [0] in
    the type of [ev_0] and [S (S n)] in the type of [ev_SS].

         -> depdendent type?

    In contrast, the definition of [list] puts the [X] parameter
    _globally_, to the _left_ of the colon, forcing the result of
    [nil] and [cons] to be the same ([list X]).  Had we tried to bring
    [nat] to the left in defining [ev], we would have seen an
    error:
*)


Fail Inductive wrong_ev (n : nat) : Prop :=
| wrong_ev_0 : wrong_ev 0
| wrong_ev_SS : forall n, wrong_ev n -> wrong_ev (S (S n)).
(* ===> Error: A parameter of an inductive type n is not
        allowed to be used as a bound variable in the type
        of its constructor. *)

(** ("Parameter" here is Coq jargon for an argument on the left of the
    colon in an [Inductive] definition; "index" is used to refer to
    arguments on the right of the colon.) *)

(** We can think of the definition of [ev] as defining a Coq property
    [ev : nat -> Prop], together with theorems [ev_0 : ev 0] and
    [ev_SS : forall n, ev n -> ev (S (S n))].  Such "constructor
    theorems" have the same status as proven theorems.  In particular,
    we can use Coq's [apply] tactic with the rule names to prove [ev]
    for particular numbers... *)

Theorem ev_2 : ev 2.
Proof. apply ev_SS. apply ev_0. Qed.

Theorem ev_4 : ev 4.
Proof. apply ev_SS. (* backward proof: ev 4 is true if ev 2 is true *)
       apply ev_SS. apply ev_0. Qed.

(** ... or we can use function application syntax: *)

Theorem ev_4' : ev 4.
Proof. apply (ev_SS 2 (ev_SS 0 ev_0)). Qed.

(** We can also prove theorems that have hypotheses involving [ev]. *)

Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof.
  intros n. simpl. intros Hn.
  apply ev_SS. apply ev_SS. apply Hn.
Qed.


(** More generally, we can show that any number multiplied by 2 is even: *)

(** **** Exercise: 1 star (ev_double)  *)
Theorem ev_double : forall n,
  ev (double n).
Proof.
  intros n. induction n.
    + simpl. apply ev_0.
    + simpl. apply ev_SS. apply IHn.
Qed.     


(* ####################################################### *)
(** * Using Evidence in Proofs *)

(** Besides _constructing_ evidence that numbers are even, we can also
    _reason about_ such evidence.

    Introducing [ev] with an [Inductive] declaration tells Coq not
    only that the constructors [ev_0] and [ev_SS] are valid ways to
    build evidence that some number is even, but also that these two
    constructors are the _only_ ways to build evidence that numbers
    are even (in the sense of [ev]). *)
(** In other words, if someone gives us evidence [E] for the assertion
    [ev n], then we know that [E] must have one of two shapes:

      - [E] is [ev_0] (and [n] is [O]), or
      - [E] is [ev_SS n' E'] (and [n] is [S (S n')], where [E'] is
        evidence for [ev n']). *)

(** This suggests that it should be possible to analyze a hypothesis
    of the form [ev n] much as we do inductively defined data
    structures; in particular, it should be possible to argue by
    _induction_ and _case analysis_ on such evidence.  Let's look at a
    few examples to see what this means in practice. *)

(** ** Inversion on Evidence *)

(** Subtracting two from an even number yields another even number.
    We can easily prove this claim with the techniques that we've
    already seen, provided that we phrase it in the right way.  If we
    state it in terms of [evenb], for instance, we can proceed by a
    simple case analysis on [n]: *)

Theorem evenb_minus2: forall n,
  evenb n = true -> evenb (pred (pred n)) = true.
Proof.
  intros [ | [ | n' ] ].  (* <- what does this destruction pattern do? *)
  - (* n = 0 *) reflexivity.
  - (* n = 1; contradiction *) intros H. inversion H.
  - (* n = n' + 2 *) simpl. intros H. apply H.
Qed.

(** We can state the same claim in terms of [ev], but this quickly
    leads us to an obstacle: Since [ev] is defined inductively --
    rather than as a function -- Coq doesn't know how to simplify a
    goal involving [ev n] after case analysis on [n].  As a
    consequence, the same proof strategy fails: *)

Theorem ev_minus2: forall n,
  ev n -> ev (pred (pred n)).
Proof.
  intros [ | [ | n' ] ].
  - (* n = 0 *) simpl. intros _. apply ev_0.
  - (* n = 1; we're stuck! *) simpl. 
Abort.

(** The solution is to perform case analysis on the evidence that [ev
    n] _directly_. By the definition of [ev], there are two cases to
    consider:

    - If that evidence is of the form [ev_0], we know that [n = 0].
      Therefore, it suffices to show that [ev (pred (pred 0))] holds.
      By the definition of [pred], this is equivalent to showing that
      [ev 0] holds, which directly follows from [ev_0].

    - Otherwise, that evidence must have the form [ev_SS n' E'], where
      [n = S (S n')] and [E'] is evidence for [ev n'].  We must then
      show that [ev (pred (pred (S (S n'))))] holds, which, after
      simplification, follows directly from [E']. *)

(** We can invoke this kind of argument in Coq using the [inversion]
    tactic.  Besides allowing us to reason about equalities involving
    constructors, [inversion] provides a case-analysis principle for
    inductively defined propositions.  When used in this way, its
    syntax is similar to [destruct]: We pass it a list of identifiers
    separated by [|] characters to name the arguments to each of the
    possible constructors.  For instance: *)

Theorem ev_minus2 : forall n,
  ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  inversion E as [| n' E'].  (* do case analysis on possible proofs *)
  - (* E = ev_0 *) simpl. apply ev_0.
  - (* E = ev_SS n' E' *) simpl. apply E'.
Qed.

(**  AAA: I'm finding it a bit awkward to discuss [inversion] here
    instead of [destruct], especially given that we are using
    [destruct] to talk about [reflect] below... Would it be too crazy
    to use [inversion] only where it is actually needed? 
 *)
(**  BCP: I have never been satisfied with our discussion of
    destruct vs. inversion.  What's here now is much better than we've
    ever had before.  But if you have a clear idea for how to clean it
    up further, I'm all ears.

    One possibility -- perhaps easy enough to do now -- would be to
    replace inversion by destruct in this discussion and move the
    inversion vs. destruct discussion into the following
    subsection.  (In fact, I favor trying this.  The next section also
    needs some help, and consolidating the discussion would be a good
    beginning.) 
 *)

(** Note that, in this particular case, it is also possible to replace
    [inversion] by [destruct]: *)

Theorem ev_minus2' : forall n,
  ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  destruct E as [| n' E'].
  - (* E = ev_0 *) simpl. apply ev_0.
  - (* E = ev_SS n' E' *) simpl. apply E'.
Qed.

(** The difference between the two forms is that [inversion] is more
    convenient when used on a hypothesis that consists of an inductive
    property applied to a complex expression (as opposed to a single
    variable).  Here's is a concrete example.  Suppose that we wanted
    to prove the following variation of [ev_minus2]: *)

Theorem evSS_ev : forall n,
  ev (S (S n)) -> ev n.

(** Intuitively, we know that evidence for the hypothesis cannot
    consist just of the [ev_0] constructor, since [O] and [S] are
    different constructors of the type [nat]; hence, [ev_SS] is the
    only case that applies.  Unfortunately, [destruct] is not smart
    enough to realize this, and it still generates two subgoals.  Even
    worse, in doing so, it keeps the final goal unchanged, failing to
    provide any useful information for completing the proof.  *)

Proof.
  intros n E.
  destruct E as [| n' E'].
  - (* E = ev_0. *)
    (* We must prove that [n] is even from no assumptions! *)
Abort.

(** What happened, exactly?  Calling [destruct] has the effect of
    replacing all occurrences of the property argument by the values
    that correspond to each constructor.  This is enough in the case
    of [ev_minus2'] because that argument, [n], is mentioned directly
    in the final goal. However, it doesn't help in the case of
    [evSS_ev] since the term that gets replaced ([S (S n)]) is not
    mentioned anywhere. *)

(** The [inversion] tactic, on the other hand, can detect (1) that the
    first case does not apply, and (2) that the [n'] that appears on
    the [ev_SS] case must be the same as [n].  This allows us to
    complete the proof: *)

Theorem evSS_ev : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E.
  inversion E as [| n' E'].  (* ev (S S n) implies n is even and n' = n *) 
  (* We are in the [E = ev_SS n' E'] case now. *)
    + apply E'.
Qed.

(** By using [inversion], we can also apply the principle of explosion
    to "obviously contradictory" hypotheses involving inductive
    properties. For example: *)
Theorem one_not_even : ~ ev 1.
Proof.
  unfold not.
  intros H. inversion H.
Qed.

(** **** Exercise: 1 star (inversion_practice)  *)
(** Prove the following results using [inversion]. *)

Theorem SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  (* ev (n + 4) ==> ev (n' + 2) where n' = n + 2*)
  intros n E. inversion E as [| n' E'].
      (* but ev (n' + 2) ==> ev n' *)
    + inversion E'. apply H1.
Qed.      


Theorem even5_nonsense :
  ev 5 -> 2 + 2 = 9.
Proof.
  intros H. inversion H. inversion H1. inversion H3.
Qed.

(** ** The Inversion Tactic Revisited *)

(** These uses of [inversion] may seem a bit mysterious at first.
    Until now, we've only used [inversion] on equality
    propositions, to utilize injectivity of constructors or to
    discriminate between different constructors.  But we see here
    that [inversion] can also be applied to analyzing evidence
    for inductively defined propositions.

    (You might also expect that [destruct] would be a more suitable
    tactic to use here. Indeed, it is possible to use [destruct], but
    it often throws away useful information, and the [eqn:] qualifier
    doesn't help much in this case.)

    Here's how [inversion] works in general.  Suppose the name
    [I] refers to an assumption [P] in the current context, where
    [P] has been defined by an [Inductive] declaration.  Then,
    for each of the constructors of [P], [inversion I] generates
    a subgoal in which [I] has been replaced by the exact,
    specific conditions under which this constructor could have
    been used to prove [P].  Some of these subgoals will be
    self-contradictory; [inversion] throws these away.  The ones
    that are left represent the cases that must be proved to
    establish the original goal.

    In this particular case, the [inversion] analyzed the construction
    [ev (S (S n))], determined that this could only have been
    constructed using [ev_SS], and generated a new subgoal with the
    arguments of that constructor as new hypotheses.  (It also
    produced an auxiliary equality, which happens to be useless here.)
    We'll begin exploring this more general behavior of inversion in
    what follows. *)

(* ####################################################### *)
(** ** Induction over Evidence *)

(** The [ev_double] exercise above shows that our new notion of
    evenness is implied by the two earlier ones (since, by
    [even_bool_prop], we already know that those are equivalent to
    each other). To show that all three coincide, we still need the
    following lemma: *)

Lemma ev_even : forall n,
  ev n -> exists k, n = double k.
Proof.

(** We could try to proceed by case analysis or induction on [n].  But
    since [ev] is mentioned in a premise, this strategy would probably
    lead to a dead end, as in the previous section.  Thus, it seems
    better to first try inversion on the evidence for [ev].  Indeed,
    the first case can be solved trivially. *)

  intros n E. inversion E as [| n' E'].
  - (* E = ev_0 *)
    exists 0. reflexivity.
  - (* E = ev_SS n' E' *) simpl.

(** Unfortunately, the second case is harder.  We need to show [exists
    k, S (S n') = double k], but the only available assumption is
    [E'], which states that [ev n'] holds.  Since this isn't directly
    useful, it seems that we are stuck and that performing case
    analysis on [E] was a waste of time.

    If we look more closely at our second goal, however, we can see
    that something interesting happened: By performing case analysis
    on [E], we were able to reduce the original result to an similar
    one that involves a _different_ piece of evidence for [ev]: [E'].
    More formally, we can finish our proof by showing that
    exists k', n' = double k',
    which is the same as the original statement, but with [n'] instead
    of [n].  Indeed, it is not difficult to convince Coq that this
    intermediate result suffices. *)

    assert (I : (exists k', n' = double k') ->
                (exists k, S (S n') = double k)).
    { intros [k' Hk']. rewrite Hk'. exists (S k'). simpl.
      reflexivity. }
    apply I. (* reduce the original goal to the new one *)

(** If this looks familiar, it is no coincidence: We've encountered
    similar problems in the [Induction] chapter, when trying to use
    case analysis to prove results that required induction.  And once
    again the solution is... induction!

    The behavior of [induction] on evidence is the same as its
    behavior on data: It causes Coq to generate one subgoal for each
    constructor that could have used to build that evidence, while
    providing an induction hypotheses for each recursive occurrence of
    the property in question.  

    Let's try our current lemma again: *)

Abort.

Lemma ev_even : forall n,
  ev n -> exists k, n = double k.
Proof.
  intros n E.
  induction E as [|n' E' IH].
  - (* E = ev_0 *)
    exists 0. reflexivity.
  - (* E = ev_SS n' E'
       with IH : exists k', n' = double k' *)
    destruct IH as [k Hk].
    rewrite Hk. exists (S k). reflexivity.
Qed.

(** Here, we can see that Coq produced an [IH] that corresponds to
    [E'], the single recursive occurrence of [ev] in its own
    definition.  Since [E'] mentions [n'], the induction hypothesis
    talks about [n'], as opposed to [n] or some other number. *)

(** The equivalence between the second and third definitions of
    evenness now follows. *)

Theorem ev_even_iff : forall n,
  ev n <-> exists k, n = double k.
Proof.
  intros n. split.
  - (* -> *) apply ev_even.
  - (* <- *) intros [k Hk]. rewrite Hk. apply ev_double.
Qed.


(** As we will see in later chapters, induction on evidence is a
    recurring technique when studying the semantics of programming
    languages, where many properties of interest are defined
    inductively.  The following exercises provide simple examples of
    this technique, to help you familiarize yourself with it. *)

(** **** Exercise: 2 stars (ev_sum)  *)
Theorem ev_sum : forall n m, ev n -> ev m -> ev (n + m).
Proof.
  intros n m H1 H2. induction H1 as [n' | H1'].
    + apply H2.
    + simpl. apply ev_SS. apply IHev.
Qed.      
  


(** **** Exercise: 4 stars, advanced (ev_alternate)  *)
(** In general, there may be multiple ways of defining a
    property inductively.  For example, here's a (slightly contrived)
    alternative definition for [ev]: *)

Inductive ev' : nat -> Prop :=
| ev'_0 : ev' 0
| ev'_2 : ev' 2
| ev'_sum : forall n m, ev' n -> ev' m -> ev' (n + m).

(** Prove that this definition is logically equivalent to
    the old one. *)
Theorem ev'_ev : forall n, ev' n <-> ev n.
Proof.
  intros n. split.
  (* -> *)
  - intros H. induction H.
      + apply ev_0.
      + apply ev_SS. apply ev_0.
      + apply ev_sum. apply IHev'1. apply IHev'2.
  (* <- *)
  - intros H. induction H.
      + apply ev'_0.
      + destruct IHev.  (*todo: ev' n implies what? why does this make sense??? *)
          * apply ev'_2.
          * apply (ev'_sum 2). apply ev'_2. apply ev'_2.
          * apply (ev'_sum 2 (n+m)). apply ev'_2. apply (ev'_sum n m).
            apply IHev1. apply IHev2.
Qed.            
            
  

(** **** Exercise: 3 stars, advanced, recommended (ev_ev__ev)  *)
(** Finding the appropriate thing to do induction on is a
    bit tricky here: *)

Theorem ev_ev__ev : forall n m,
  ev (n+m) -> ev n -> ev m.
Proof.
  intros n m Hnm Hn. induction Hn.
    + simpl in Hnm. apply Hnm.
    + simpl in Hnm. apply evSS_ev in Hnm.
      apply IHHn. apply Hnm.
Qed.

(** **** Exercise: 3 stars, optional (ev_plus_plus)  *)
(** This exercise just requires applying existing lemmas.  No
    induction or even case analysis is needed, though some of the
    rewriting may be tedious. *)

Theorem ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ############################################################ *)
(** * Case Study: Regular Expressions *)

(** The [ev] property provides a simple example for illustrating
    inductive definitions and the basic techniques for reasoning about
    them, but it is not terribly exciting -- after all, it is
    equivalent to the two non-inductive of evenness that we had
    already seen, and does not seem to offer any concrete benefit over
    them.  To give a better sense of the power of inductive
    definitions, we now show how to use them to model a classic
    concept in computer science: _regular expressions_. *)

(** Regular expressions are a simple language for describing strings,
    defined as elements of the following inductive type.  (The names
    of the constructors should become clear once we explain their
    meaning below.)  *)

Inductive reg_exp (T : Type) : Type :=
| EmptySet : reg_exp T
| EmptyStr : reg_exp T
| Char     : T -> reg_exp T
| App      : reg_exp T -> reg_exp T -> reg_exp T
| Union    : reg_exp T -> reg_exp T -> reg_exp T
| Star     : reg_exp T -> reg_exp T.

Arguments EmptySet {T}.
Arguments EmptyStr {T}.
Arguments Char {T}  _.
Arguments App {T}   _ _.
Arguments Union {T} _ _.
Arguments Star {T}  _.

(** Note that this definition is _polymorphic_: Regular expressions in
    [reg_exp T] describe strings with characters drawn from [T] --
    that is, lists of elements of [T].  (We depart slightly from
    standard practice in that we do not require the type [T] to be
    finite.  This results in a somewhat different theory of regular
    expressions, but the difference is not significant for our
    purposes.)

    We connect regular expressions and strings via the following
    rules, which define when a regular expression _matches_ some
    string:

    - The expression [EmptySet] does not match any string.

    - The expression [EmptyStr] matches the empty string [[]].

    - The expression [Char x] matches the one-character string [[x]].

    - If [re1] matches [s1], and [re2] matches [s2], then [App re1
      re2] matches [s1 ++ s2].

    - If at least one of [re1] and [re2] matches [s], then [Union re1
      re2] matches [s].

    - Finally, if we can write some string [s] as the concatenation of
      a sequence of strings [s = s_1 ++ ... ++ s_k], and the
      expression [re] matches each one of the strings [s_i], then
      [Star re] matches [s].  (As a special case, the sequence of
      strings may be empty, so [Star re] always matches the empty
      string [[]] no matter what [re] is.) *)

(** We can easily translate this informal definition into an
    [Inductive] one as follows: *)

Inductive exp_match {T} : list T -> reg_exp T -> Prop :=
| MEmpty : exp_match [] EmptyStr
| MChar  : forall x, exp_match [x] (Char x)
| MApp   : forall s1 re1 s2 re2,
           exp_match s1 re1 ->
           exp_match s2 re2 ->
           exp_match (s1 ++ s2) (App re1 re2)
| MUnionL : forall s1 re1 re2,
              exp_match s1 re1 ->
              exp_match s1 (Union re1 re2)
| MUnionR : forall re1 s2 re2,
              exp_match s2 re2 ->
              exp_match s2 (Union re1 re2)
| MStar0  : forall re, exp_match [] (Star re)
| MStarApp : forall s1 s2 re,
               exp_match s1 re ->
               exp_match s2 (Star re) ->
               exp_match (s1 ++ s2) (Star re).

(** Once again, for readability, we can also display this definition
    using inference-rule notation.  At the same time, let's introduce
    a more readable infix notation. *)

Notation "s =~ re" := (exp_match s re) (at level 80).

(**
                          ----------------                    (MEmpty)
                           [] =~ EmptyStr

                          ---------------                      (MChar)
                           [x] =~ Char x

                       s1 =~ re1    s2 =~ re2
                      -------------------------                 (MApp)
                       s1 ++ s2 =~ App re1 re2

                              s1 =~ re1
                        ---------------------                (MUnionL)
                         s1 =~ Union re1 re2

                              s2 =~ re2
                        ---------------------                (MUnionR)
                         s2 =~ Union re1 re2

                          ---------------                     (MStar0)
                           [] =~ Star re

                      s1 =~ re    s2 =~ Star re
                     ---------------------------            (MStarApp)
                        s1 ++ s2 =~ Star re

*)

(** Notice that these rules are not _quite_ the same as the informal
    ones that we gave at the beginning of the section.  First, we
    don't need to include a rule explicitly stating that no string
    matches [EmptySet]; we just don't happen to include any rule that
    would have the effect of some string matching
    [EmptySet].  (Indeed, the syntax of inductive definitions doesn't
    even _allow_ us to give such a "negative rule.")

    Furthermore, the informal rules for [Union] and [Star] correspond
    to two constructors each: [MUnionL] / [MUnionR], and [MStar0] /
    [MStarApp].  The result is logically equivalent to the original
    rules, but more convenient to use in Coq, since the recursive
    occurrences of [exp_match] are given as direct arguments to the
    constructors, making it easier to perform induction on
    evidence.  (The [exp_match_eq] exercise below asks you to prove
    that the constructors given in the inductive declaration and the
    ones that would arise from a more literal transcription of the
    informal rules are indeed equivalent.) *)

(* ############################################################ *)

(** Let's illustrate these rules with a few examples. *)

Example reg_exp_ex1 : [1] =~ Char 1.
Proof.
  apply MChar.
Qed.

Example reg_exp_ex2 : [1; 2] =~ App (Char 1) (Char 2).
Proof.
  apply (MApp [1] _ [2]).
  - apply MChar.
  - apply MChar.
Qed.

(** (Notice how the last example applies [MApp] to the strings [[1]]
    and [[2]] directly.  Since the goal mentions [[1; 2]] instead of
    [[1] ++ [2]], Coq wouldn't be able to figure out how to split the
    string on its own.)

    Using [inversion], we can also show that certain strings do _not_
    match a regular expression: *)

Example reg_exp_ex3 : ~ ([1; 2] =~ Char 1).
Proof.
  intros H. inversion H.
Qed.

(** We can define helper functions to help write down regular
    expressions. The [reg_exp_of_list] function constructs a regular
    expression that matches exactly the list that it receives as an
    argument: *)

Fixpoint reg_exp_of_list {T} (l : list T) :=
  match l with
  | []      => EmptyStr
  | x :: l' => App (Char x) (reg_exp_of_list l')
  end.

Example reg_exp_ex4 : [1; 2; 3] =~ reg_exp_of_list [1; 2; 3].
Proof.
  simpl. apply (MApp [1]).
  { apply MChar. }
  apply (MApp [2]).
  { apply MChar. }
  apply (MApp [3]).
  { apply MChar. }
  apply MEmpty.
Qed.

(** We can also prove general facts about [exp_match].  For instance,
    the following lemma shows that every string [s] that matches [re]
    also matches [Star re]. *)

Lemma MStar1 :
  forall T s (re : reg_exp T) ,
    s =~ re ->
    s =~ Star re.
Proof.
  intros T s re H.
  rewrite <- (app_nil_r _ s).
  apply (MStarApp s [] re).
  - apply H.
  - apply MStar0.
Qed.

(** (Note the use of [app_nil_r] to change the goal of the theorem to
    exactly the same shape expected by [MStarApp].) *)

(** **** Exercise: 3 stars (exp_match_ex)  *)
(** The following lemmas show that the informal matching rules given
    first can be obtained from the formal inductive definition. *)

Lemma empty_is_empty : forall T (s : list T),
  ~ (s =~ EmptySet).
Proof.
  intros T s. unfold not.
  intros H. inversion H.
Qed.

Lemma MUnion' : forall T (s : list T) (re1 re2 : reg_exp T),
  s =~ re1 \/ s =~ re2 ->
  s =~ Union re1 re2.
Proof.
  intros T s re1 re2. intros [H1 | H2].
    + apply MUnionL. apply H1.
    + apply MUnionR. apply H2.
Qed.  


(** The next lemma is stated in terms of the [fold] function from the
    [Poly] chapter: If [ss : list (list T)] represents a sequence of
    strings [s1, ..., sn], then [fold app ss []] is the result of
    concatenating them all together. *)

(*
   eg: fold (++) ["hello","world"] []   =~ star re
       where re matches the strings
*)
Lemma MStar' : forall T (ss : list (list T)) (re : reg_exp T),
  (forall s, In s ss -> s =~ re) ->
  fold app ss [] =~ Star re.
Proof.
  intros T ss re H. induction ss as [|s' ss'].
    + simpl. apply MStar0.
    + simpl. apply MStarApp.
        - apply H. simpl. left. reflexivity.
        - apply IHss'. intros s H1.
          apply H. simpl. right. apply H1.
Qed.          
  

(** **** Exercise: 4 stars (reg_exp_of_list)  *)
(** Prove that [reg_exp_of_list] satisfies the following
    specification: *)

(*
   suppose s1,s2 are lists, then
   s1 matches regex(s2)   if and only if   s1 = s2
*)
Lemma reg_exp_of_list_spec : forall T (s1 s2 : list T),
  s1 =~ reg_exp_of_list s2 <-> s1 = s2.
Proof.
  intros T s1 s2. split.
  (* -> *)
  + generalize dependent s1. induction s2 as [|s s2'].
      - intros s1 H. inversion H. reflexivity.
      - intros s1 H. inversion H. subst.
        apply IHs2' in H4. rewrite H4. inversion H3. reflexivity.
  (* <- *)
  +  generalize dependent s1. induction s2 as [|s s2'].
      - intros s1 H. simpl. rewrite H. apply MEmpty.
      - intros s1 H. rewrite H. simpl. apply (MApp [s]).
          * apply MChar.
          * apply IHs2'. reflexivity.
Qed.
                     


(** ** Rule Induction *)

(** Suppose that we wanted to prove the following intuitive result: if
    a regular expression [re] matches some string [s], then all
    elements of [s] must occur somewhere in [re]. We begin by defining
    a function [re_chars] that lists all single-character elements
    that occur anywhere in a regular expression:
*)

Fixpoint re_chars {T} (re : reg_exp T) : list T :=
  match re with
  | EmptySet      => []
  | EmptyStr      => []
  | Char x        => [x]
  | App re1 re2   => re_chars re1 ++ re_chars re2
  | Union re1 re2 => re_chars re1 ++ re_chars re2
  | Star re       => re_chars re
  end.

Lemma in_re_match :
  forall T (s : list T) (re : reg_exp T) (x : T),
    s =~ re ->
    In x s ->
    In x (re_chars re).
Proof.
  intros T s re x Hmatch Hin.

(** When doing induction on [Hmatch], we can name the arguments given
    to each of the rules in the same way we can name arguments given
    to data type constructors. Whenever one of these arguments is a
    premise of the same type as the one we are doing induction on (in
    this case, [exp_match]), we additionally give a name to the
    induction hypothesis that is generated for that premise. *)

  induction Hmatch
    as [
        |x'
        |s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2 re2 Hmatch IH
        |re|s1 s2 re Hmatch1 IH1 Hmatch2 IH2].

(** Most cases of the proof are straightforward.  Notice how doing
    induction directly over [Hmatch] has the benefit of not requiring
    an explicit inversion on a hypothesis, since that step is
    performed automatically by the [induction]. *)

  - (* MEmpty *)
    apply Hin.
  - (* MChar *)
    apply Hin.
  - simpl. rewrite in_app_iff in *.
    destruct Hin as [Hin | Hin].
    + (* In x s1 *)
      left. apply (IH1 Hin).
    + (* In x s2 *)
      right. apply (IH2 Hin).
  - (* MUnionL *)
    simpl. rewrite in_app_iff.
    left. apply (IH Hin).
  - (* MUnionR *)
    simpl. rewrite in_app_iff.
    right. apply (IH Hin).
  - (* MStar0 *)
    destruct Hin.

(** In the the [MStarApp] case, notice that we now have an induction
    hypothesis that we can apply when [x] is a member of [s2]. *)

  - (* MStarApp *)
    simpl. rewrite in_app_iff in Hin.
    destruct Hin as [Hin | Hin].
    + (* In x s1 *)
      apply (IH1 Hin).
    + (* In x s2 *)
      apply (IH2 Hin).

Qed.

(** **** Exercise: 4 stars (re_not_empty)  *)
(** Write a recursive function [re_not_empty] that tests whether a
    regular expression matches some string. Prove that your function
    is correct. *)

Fixpoint re_not_empty {T} (re : reg_exp T) : bool := match re with
  | EmptySet    => false
  | EmptyStr    => true
  | Char _      => true
  | App r1 r2   => re_not_empty r1 && re_not_empty r2
  | Union r1 r2 => re_not_empty r1 || re_not_empty r2
  | Star r      => true
  end.

Lemma re_not_empty_correct : forall T (re : reg_exp T),
  (exists s, s =~ re) <-> re_not_empty re = true.
Proof.
  intros T re. split.
  (* -> *)
  + intros [s  H]. induction H.
      - reflexivity.
      - reflexivity.
      - simpl. apply andb_true_iff. split.
          * apply IHexp_match1.
          * apply IHexp_match2.
      - simpl. apply orb_true_iff. left. apply IHexp_match.
      - simpl. apply orb_true_iff. right. apply IHexp_match.
      - simpl. reflexivity.
      - reflexivity.
 (* <- *)
 + induction re.
     - simpl. intros Hc. inversion Hc.
     - simpl. intros _.  exists []. apply MEmpty.
     - intros. exists [t]. apply MChar.
     - simpl. rewrite andb_true_iff. intros [H1 H2]. 
       apply IHre1 in H1. apply IHre2 in H2.
       destruct H1 as [x1 H1]. destruct H2 as [x2 H2].
       exists (x1 ++ x2). apply (MApp x1 re1 x2 re2 H1 H2).
     - simpl. rewrite orb_true_iff. intros [H1 | H2].
         * apply IHre1 in H1. destruct H1 as [s1 H1].
           exists s1. apply (MUnionL s1 re1 _ H1).
         * apply IHre2 in H2. destruct H2 as [s2 H2].
           exists s2. apply (MUnionR re1 s2 re2 H2).
     - simpl. intros _. exists []. apply MStar0.
Qed.       


(**  Text missing... (And: I'm not sure how much of this you (AAA)
   envision being presented in class, and how much is exercises...) 
 *)
(**  AAA: This exercise is using remember... Maybe we can add an
    explanation about it earlier? 
 *)
(**  Yes, it is needed in the rest of the book, and I think it's
   not explained anyplace right now!  I think it belongs with the
   explanation of generalize dependent in Tactics.v. 
 *)

Lemma star_app: forall T (s1 s2 : list T) (re : reg_exp T),
  s1 =~ Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.
  remember (Star re) as re'.
  generalize dependent s2.
  induction H1
    as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
        |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].
  - (* MEmpty *)  inversion Heqre'.
  - (* MChar *)    inversion Heqre'.
  - (* MApp *)    inversion Heqre'.
  - (* MUnionL *) inversion Heqre'.
  - (* MUnionR *) inversion Heqre'.
  - (* MStar0 *)
    inversion Heqre'. intros s H. apply H.
  - (* MStarApp *)
    inversion Heqre'. rewrite H0 in IH2, Hmatch1.
    intros s2 H1. rewrite <- app_assoc.
    apply MStarApp.
    + apply Hmatch1.
    + apply IH2.
      * reflexivity.
      * apply H1.
Qed.

(**  Here starts the pumping lemma! 
 *)
Fixpoint napp {T} (n : nat) (l : list T) : list T :=
  match n with
  | 0 => []
  | S n' => l ++ napp n' l
  end.

Lemma napp_plus: forall T (n m : nat) (l : list T),
  napp (n + m) l = napp n l ++ napp m l.
Proof.
  intros T n m l.
  induction n as [|n IHn].
  - reflexivity.
  - simpl. rewrite IHn, app_assoc. reflexivity.
Qed.

Fixpoint pumping_constant {T} (re : reg_exp T) : nat :=
  match re with
  | EmptySet => 0
  | EmptyStr => 1
  | Char _ => 2
  | App re1 re2 => pumping_constant re1 + pumping_constant re2
  | Union re1 re2 => pumping_constant re1 + pumping_constant re2
  | Star _ => 1
  end.

Require Coq.omega.Omega.

Lemma pumping : forall T (re : reg_exp T) s,
  s =~ re ->
  pumping_constant re <= length s ->
  exists s1 s2 s3,
    s = s1 ++ s2 ++ s3 /\
    s2 <> [] /\
    forall m, s1 ++ napp m s2 ++ s3 =~ re.
Proof.
  intros T re s Hmatch.
  induction Hmatch
    as [ | x | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
       | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
       | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2 ].
  - (* MEmpty *)
    simpl. omega.
  - (* MChar *)
    simpl. omega.
  - (* MApp *)
    simpl. intros Hlen.
    assert (H : pumping_constant re1 <= length s1 \/
                pumping_constant re2 <= length s2).
    { rewrite app_length in Hlen. omega. }
    destruct H as [H | H].
    + destruct (IH1 H) as [s11 [s12 [s13 [H1 [H2 H3]]]]].
      rewrite H1.
      exists s11. exists s12. exists (s13 ++ s2).
      rewrite <- app_assoc, <- app_assoc.
      split. { reflexivity. }
      split. { apply H2. }
      intros m.
      rewrite app_assoc, app_assoc. apply MApp.
      * rewrite <- app_assoc. apply H3.
      * apply Hmatch2.
    + destruct (IH2 H) as [s21 [s22 [s23 [H1 [H2 H3]]]]].
      rewrite H1.
      exists (s1 ++ s21). exists s22. exists s23.
      rewrite <- app_assoc. split. { reflexivity. }
      split. { apply H2. }
      intros m.
      rewrite <- app_assoc. apply MApp.
      * apply Hmatch1.
      * apply H3.
  - (* MUnionL *)
    simpl. intros Hlen.
    assert (H : pumping_constant re1 <= length s1) by omega.
    destruct (IH H) as [s11 [s12 [s13 [H1 [H2 H3]]]]].
    exists s11. exists s12. exists s13. split. { apply H1. }
    split. { apply H2. }
    intros m. apply MUnionL. apply H3.
  - (* MUnionR *)
    simpl. intros Hlen.
    assert (H : pumping_constant re2 <= length s2) by omega.
    destruct (IH H) as [s21 [s22 [s23 [H1 [H2 H3]]]]].
    exists s21. exists s22. exists s23. split. { apply H1. }
    split. { apply H2. }
    intros m. apply MUnionR. apply H3.
  - (* MStar0 *)
    simpl. omega.
  - (* MStarApp *)
    simpl. intros Hlen.
    exists []. exists (s1 ++ s2). exists [].
    simpl. rewrite app_nil_r. split. { reflexivity. }
    split.
    { destruct (s1 ++ s2).
      - simpl in Hlen. omega.
      - intros contra. inversion contra. }
    intros m.
    rewrite app_nil_r.
    induction m as [|m IHm].
    + simpl. apply MStar0.
    + simpl. apply star_app.
      * apply (MStarApp _ _ _ Hmatch1 Hmatch2).
      * apply IHm.
Qed.

(* ####################################################### *)
(** * Applications and Variations *)

(**  The difficulty with naming this section is probably a signal
   that the grouping / flow of topics doesn't make sense... 
 *)
(** ** Computational vs. Inductive Definitions *)

(**  Move earlier and compress 
 *)
(** We have seen that the proposition "[n] is even" can be
    phrased in two different ways -- indirectly, via a boolean testing
    function [evenb], or directly, by inductively describing what
    constitutes evidence for evenness.  These two ways of defining
    evenness are about equally easy to state and work with.  Which we
    choose is basically a question of taste.

    However, for many other properties of interest, the direct
    inductive definition is preferable, since writing a testing
    function may be awkward or even impossible.

    One such property is [beautiful].  This is a perfectly sensible
    definition of a set of numbers, but we cannot translate its
    definition directly into a Coq Fixpoint (or into a recursive
    function in any other common programming language).  We might be
    able to find a clever way of testing this property using a
    [Fixpoint] (indeed, it is not too hard to find one in this case),
    but in general this could require arbitrarily deep thinking.  In
    fact, if the property we are interested in is uncomputable, then
    we cannot define it as a [Fixpoint] no matter how hard we try,
    because Coq requires that all [Fixpoint]s correspond to
    terminating computations.

    On the other hand, writing an inductive definition of what it
    means to _give evidence_ for the property [beautiful] is
    straightforward. *)


(**  This discussion seems kind of homeless, and it's not clear why
   we're bothering to say it.  Maybe it could be combined with the
   reflection material? 
 *)
(* ####################################################### *)
(** ** Propositions about Data Structures *)

(** So far, we have only looked at propositions about natural numbers. However,
   we can define inductive predicates about any type of data. For example,
   suppose we would like to characterize lists of _even_ length. We can
   do that with the following definition.  *)

Inductive ev_list {X:Type} : list X -> Prop :=
  | el_nil : ev_list []
  | el_cc  : forall x y l, ev_list l -> ev_list (x :: y :: l).

(** Of course, this proposition is equivalent to just saying that the
length of the list is even. *)

Lemma ev_list__ev_length: forall X (l : list X), ev_list l -> ev (length l).
Proof.
    intros X l H. induction H.
    - (* el_nil *) simpl. apply ev_0.
    - (* el_cc *)  simpl.  apply ev_SS. apply IHev_list.
Qed.

(** However, because evidence for [ev] contains less information than
    evidence for [ev_list], the converse direction must be stated very
    carefully. *)

Lemma ev_length__ev_list: forall X n,
  ev n -> forall (l : list X), n = length l -> ev_list l.
Proof.
  intros X n H.
  induction H.
  - (* ev_0 *) intros l H. destruct l.
    + (* [] *) apply el_nil.
    + (* x::l *) inversion H.
  - (* ev_SS *) intros l H2. destruct l as [|x1 [| x2 l]].
    + (* [] *) inversion H2.
    + (* [x] *) inversion H2.
    + (* x :: x0 :: l *) apply el_cc. apply IHev. inversion H2. reflexivity.
Qed.

(**  Move exercises later; delete text above 
 *)
(** **** Exercise: 4 stars, recommended (palindromes)  *)
(** A palindrome is a sequence that reads the same backwards as
    forwards.

    - Define an inductive proposition [pal] on [list X] that
      captures what it means to be a palindrome. (Hint: You'll need
      three cases.  Your definition should be based on the structure
      of the list; just having a single constructor
        c : forall l, l = rev l -> pal l
      may seem obvious, but will not work very well.)

    - Prove [pal_app_rev] that
       forall l, pal (l ++ rev l).
    - Prove [pal_rev] that
       forall l, pal l -> l = rev l.
*)


Inductive pal {X} : list X -> Prop :=
  | pal_nil  : pal []
  | pal_one  : forall (x : X), pal [x]
  | pal_cons : forall (x : X) (l : list X), pal l -> pal ([x] ++ l ++ [x]).



   
Lemma list_manip : forall (X : Type) (x : X) (l :  list X),
  (x::l) ++ rev (x ::l) = [x] ++ (l ++ rev l) ++ [x].                     
Proof.
  intros X x l.
  replace (x :: l) with ([x] ++ l).
   + rewrite rev_app_distr. simpl (rev [x]). apply app_assoc.
   + reflexivity.
Qed.
  
  
Theorem pal_app_rev : forall (X : Type) (l : list X),
  pal (l ++ rev l).                        
Proof.
  intros X l. induction l.
    - simpl. apply pal_nil.
    - rewrite list_manip. apply (pal_cons x (l ++ rev l) IHl).
Qed.
      
  
Theorem pal_rev : forall (X: Type) (l : list X),
  pal l -> l = rev l.
Proof.
  intros X l H. induction H.
    + reflexivity.
    + reflexivity.
    + rewrite rev_app_distr. rewrite rev_app_distr. simpl.
      rewrite <- IHpal. reflexivity.
Qed.


(* Again, the converse direction is much more difficult, due to the
lack of evidence. *)

(** **** Exercise: 5 stars, optional (palindrome_converse)  *)
(** Using your definition of [pal] from the previous exercise, prove
    that
     forall l, l = rev l -> pal l.
*)

Theorem palindrome_converse : forall (X : Type) (l : list X),
  l = rev l -> pal l.                
Proof.
  intros X l. 



(* ####################################################### *)
(** * Inductive Relations *)

(**  bcp: belongs before regexps 
 *)
(** A proposition parameterized by a number (such as [ev] or
    [beautiful]) can be thought of as a _property_ -- i.e., it defines
    a subset of [nat], namely those numbers for which the proposition
    is provable.  In the same way, a two-argument proposition can be
    thought of as a _relation_ -- i.e., it defines a set of pairs for
    which the proposition is provable. *)

Module LeModule.


(** One useful example is the "less than or equal to"
    relation on numbers. *)

(** The following definition should be fairly intuitive.  It
    says that there are two ways to give evidence that one number is
    less than or equal to another: either observe that they are the
    same number, or give evidence that the first is less than or equal
    to the predecessor of the second. *)

Inductive le : nat -> nat -> Prop :=
  | le_n : forall n, le n n
  | le_S : forall n m, (le n m) -> (le n (S m)).

Notation "m <= n" := (le m n).


(** Proofs of facts about [<=] using the constructors [le_n] and
    [le_S] follow the same patterns as proofs about properties, like
    [ev] in chapter [Prop].  We can [apply] the constructors to prove [<=]
    goals (e.g., to show that [3<=3] or [3<=6]), and we can use
    tactics like [inversion] to extract information from [<=]
    hypotheses in the context (e.g., to prove that [(2 <= 1) -> 2+2=5].) *)

(** Here are some sanity checks on the definition.  (Notice that,
    although these are the same kind of simple "unit tests" as we gave
    for the testing functions we wrote in the first few lectures, we
    must construct their proofs explicitly -- [simpl] and
    [reflexivity] don't do the job, because the proofs aren't just a
    matter of simplifying computations.) *)

Theorem test_le1 :
  3 <= 3.
Proof.
  (* WORKED IN CLASS *)
  apply le_n.  Qed.

Theorem test_le2 :
  3 <= 6.
Proof.
  (* WORKED IN CLASS *)
  apply le_S. apply le_S. apply le_S. apply le_n.  Qed.

Theorem test_le3 :
  (2 <= 1) -> 2 + 2 = 5.
Proof.
  (* WORKED IN CLASS *)
  intros H. inversion H. inversion H2.  Qed.

(** The "strictly less than" relation [n < m] can now be defined
    in terms of [le]. *)

End LeModule.

Definition lt (n m:nat) := le (S n) m.

Notation "m < n" := (lt m n).

(** Here are a few more simple relations on numbers: *)

Inductive square_of : nat -> nat -> Prop :=
  sq : forall n:nat, square_of n (n * n).

Inductive next_nat : nat -> nat -> Prop :=
  | nn : forall n:nat, next_nat n (S n).

Inductive next_even : nat -> nat -> Prop :=
  | ne_1 : forall n, ev (S n) -> next_even n (S n)
  | ne_2 : forall n, ev (S (S n)) -> next_even n (S (S n)).

(** **** Exercise: 2 stars, recommended (total_relation)  *)
(** Define an inductive binary relation [total_relation] that holds
    between every pair of natural numbers. *)

(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 2 stars (empty_relation)  *)
(** Define an inductive binary relation [empty_relation] (on numbers)
    that never holds. *)

(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 2 stars, optional (le_exercises)  *)
(** Here are a number of facts about the [<=] and [<] relations that
    we are going to need later in the course.  The proofs make good
    practice exercises. *)

Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem O_le_n : forall n,
  0 <= n.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
  (* FILL IN HERE *) Admitted.


Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
  (* FILL IN HERE *) Admitted.


Theorem le_plus_l : forall a b,
  a <= a + b.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof.
 unfold lt.
 (* FILL IN HERE *) Admitted.

Theorem lt_S : forall n m,
  n < m ->
  n < S m.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem leb_complete : forall n m,
  leb n m = true -> n <= m.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem leb_correct : forall n m,
  n <= m ->
  leb n m = true.
Proof.
  (* Hint: This may be easiest to prove by induction on [m]. *)
  (* FILL IN HERE *) Admitted.

Theorem leb_true_trans : forall n m o,
  leb n m = true -> leb m o = true -> leb n o = true.
Proof.
  (* Hint: This theorem can be easily proved without using [induction]. *)
  (* FILL IN HERE *) Admitted.

(** **** Exercise: 2 stars, optional (leb_iff)  *)
Theorem leb_iff : forall n m,
  leb n m = true <-> n <= m.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

Module R.

(** **** Exercise: 3 stars, recommended (R_provability2)  *)
(** We can define three-place relations, four-place relations,
    etc., in just the same way as binary relations.  For example,
    consider the following three-place relation on numbers: *)

Inductive R : nat -> nat -> nat -> Prop :=
   | c1 : R 0 0 0
   | c2 : forall m n o, R m n o -> R (S m) n (S o)
   | c3 : forall m n o, R m n o -> R m (S n) (S o)
   | c4 : forall m n o, R (S m) (S n) (S (S o)) -> R m n o
   | c5 : forall m n o, R m n o -> R n m o.

(** - Which of the following propositions are provable?
      - [R 1 1 2]
      - [R 2 2 6]

    - If we dropped constructor [c5] from the definition of [R],
      would the set of provable propositions change?  Briefly (1
      sentence) explain your answer.

    - If we dropped constructor [c4] from the definition of [R],
      would the set of provable propositions change?  Briefly (1
      sentence) explain your answer.

(* FILL IN HERE *)
[]
*)

(** **** Exercise: 3 stars, optional (R_fact)  *)
(** Relation [R] actually encodes a familiar function.  State and prove two
    theorems that formally connects the relation and the function.
    That is, if [R m n o] is true, what can we say about [m],
    [n], and [o], and vice versa?
*)

(* FILL IN HERE *)
(** [] *)

End R.

(** **** Exercise: 4 stars, advanced (subsequence)  *)
(** A list is a _subsequence_ of another list if all of the elements
    in the first list occur in the same order in the second list,
    possibly with some extra elements in between. For example,
    [1;2;3]
    is a subsequence of each of the lists
    [1;2;3]
    [1;1;1;2;2;3]
    [1;2;7;3]
    [5;6;1;9;9;2;7;3;8]
    but it is _not_ a subsequence of any of the lists
    [1;2]
    [1;3]
    [5;6;2;1;7;3;8]

    - Define an inductive proposition [subseq] on [list nat] that
      captures what it means to be a subsequence. (Hint: You'll need
      three cases.)

    - Prove [subseq_refl] that subsequence is reflexive, that is,
      any list is a subsequence of itself.

    - Prove [subseq_app] that for any lists [l1], [l2], and [l3],
      if [l1] is a subsequence of [l2], then [l1] is also a subsequence
      of [l2 ++ l3].

    - (Optional, harder) Prove [subseq_trans] that subsequence is
      transitive -- that is, if [l1] is a subsequence of [l2] and [l2]
      is a subsequence of [l3], then [l1] is a subsequence of [l3].
      Hint: choose your induction carefully!
*)

(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 2 stars, optional (R_provability)  *)
(** Suppose we give Coq the following definition:
    Inductive R : nat -> list nat -> Prop :=
      | c1 : R 0 []
      | c2 : forall n l, R n l -> R (S n) (n :: l)
      | c3 : forall n l, R (S n) l -> R n l.
    Which of the following propositions are provable?

    - [R 2 [1;0]]
    - [R 1 [1;2;1;0]]
    - [R 6 [3;2;1;0]]
*)

(** [] *)


(* ####################################################### *)
(** * Improving Reflection *)

(**  AAA: Reflection is more general than just using [reflect]. We
   should explain the term in the previous chapter, when discussing
   [bool] vs. [Prop], and make it clear here that we are just
   developing infrastructure to make it more conveninent. 
 *)
(** We've seen in the previous chapter that it is often
    necessary to relate boolean computations to statements in
    [Prop]. Unfortunately, performing this conversion by hand can
    result in tedious proof scripts. Consider the proof of the
    following theorem: *)

Theorem filter_not_empty_In : forall n l,
  filter (beq_nat n) l <> [] ->
  In n l.
Proof.
  intros n l. induction l as [|m l' IHl'].
  - (* l = [] *)
    simpl. intros H. apply H. reflexivity.
  - (* l = m :: l' *)
    simpl. destruct (beq_nat n m) eqn:H.
    + (* beq_nat n m = true *)
      intros _. rewrite beq_nat_true_iff in H. rewrite H.
      left. reflexivity.
    + (* beq_nat n m = false *)
      intros H'. right. apply IHl'. apply H'.
Qed.

(** In the first branch of the [destruct], we must explicitly
    apply the [beq_nat_true_iff] lemma to the equation generated by
    destructing [beq_nat n m], to convert the assumption [beq_nat n m
    = true] into the assumption [n = m], which is what we need to
    complete this case.

    We can streamline this proof by defining an inductive proposition
    that yields a better case-analysis principle for [beq_nat n
    m]. Instead of generating an equation such as [beq_nat n m =
    true], which is not directly useful, this principle gives us right
    away the assumption we need: [n = m]. We'll actually define
    something a bit more general, which can be used with arbitrary
    properties (and not just equalities): *)

Inductive reflect (P : Prop) : bool -> Prop :=
| ReflectT : P -> reflect P true
| ReflectF : ~ P -> reflect P false.

(** The [reflect] property takes two arguments: a proposition
    [P] and a boolean [b]. Intuitively, it states that the property
    [P] is _reflected_ in (i.e., equivalent to) the boolean [b]: [P]
    holds if and only if [b = true]. To see this, notice that, by
    definition, the only way we can produce evidence that [reflect P
    true] holds is by showing that [P] is true and using the
    [ReflectT] constructor. If we invert this statement, this means
    that it should be possible to extract evidence for [P] from a
    proof of [reflect P true]. Conversely, the only way to show
    [reflect P false] is by combining evidence for [~ P] with the
    [ReflectF] constructor.

    It is easy to formalize this intuition and show that the two
    statements are indeed equivalent: *)

Theorem iff_reflect : forall P b, (P <-> b = true) -> reflect P b.
Proof.
  intros P [] H.
  - apply ReflectT. rewrite H. reflexivity.
  - apply ReflectF. rewrite H. intros H'. inversion H'.
Qed.

(** **** Exercise: 2 stars, recommended (reflect_iff)  *)
Theorem reflect_iff : forall P b, reflect P b -> (P <-> b = true).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** The advantage of [reflect] over the normal "if and only if"
    connective is that, by destructing a hypothesis or lemma of the
    form [reflect P b], we can perform case analysis on [b] while at
    the same time generating appropriate hypothesis in the two
    branches ([P] in the first subgoal and [~ P] in the second).

    To use [reflect] to produce a better proof of
    [filter_not_empty_In], we begin by recasting the
    [beq_nat_iff_true] lemma into a more convenient form in terms of
    [reflect]: *)

Lemma beq_natP : forall n m, reflect (n = m) (beq_nat n m).
Proof.
  intros n m.
  apply iff_reflect. rewrite beq_nat_true_iff. reflexivity.
Qed.

(** The new proof of [filter_not_empty_In] is now as
    follows. Notice how the calls to [destruct] and [apply] are
    combined into a single call to [destruct].  (To see this clearly,
    look at the two proofs of [filter_not_empty_In] in your Coq
    browser and observe the differences in proof state at the
    beginning of the first case of the [destruct].) *)

Theorem filter_not_empty_In' : forall n l,
  filter (beq_nat n) l <> [] ->
  In n l.
Proof.
  intros n l. induction l as [|m l' IHl'].
  - (* l = [] *)
    simpl. intros H. apply H. reflexivity.
  - (* l = m :: l' *)
    simpl. destruct (beq_natP n m) as [H | H].
    + (* n = m *)
      intros _. rewrite H. left. reflexivity.
    + (* n <> m *)
      intros H'. right. apply IHl'. apply H'.
Qed.

(** Although this arguably represents only a small gain in
    convenience for this particular proof, using [reflect]
    consistently often leads to shorter and clearer proofs. We'll see many
    more examples where [reflect] comes in handy in later chapters.

    Last, a historical note. The use of the [reflect] property was
    popularized by _SSReflect_, a Coq library that has been used to
    formalize important results in mathematics, such as the 4-color
    theorem or the Feit-Thompson theorem. The name stands for
    _small-scale reflection_, i.e., the pervasive use of reflection to
    simplify small proof steps with boolean computations. *)

(* ####################################################### *)
(** * Additional Exercises *)

(**  These are dumped here from the old MoreLogic.  Need editing... 
 *)
(** **** Exercise: 4 stars, advanced (filter_challenge)  *)
(** One of the main purposes of Coq is to prove that programs match
    their specifications.  To this end, let's prove that our
    definition of [filter] matches a specification.  Here is the
    specification, written out informally in English.

    Suppose we have a set [X], a function [test: X->bool], and a list
    [l] of type [list X].  Suppose further that [l] is an "in-order
    merge" of two lists, [l1] and [l2], such that every item in [l1]
    satisfies [test] and no item in [l2] satisfies test.  Then [filter
    test l = l1].

    A list [l] is an "in-order merge" of [l1] and [l2] if it contains
    all the same elements as [l1] and [l2], in the same order as [l1]
    and [l2], but possibly interleaved.  For example,
    [1;4;6;2;3]
    is an in-order merge of
    [1;6;2]
    and
    [4;3].
    Your job is to translate this specification into a Coq theorem and
    prove it.  (Hint: You'll need to begin by defining what it means
    for one list to be a merge of two others.  Do this with an
    inductive relation, not a [Fixpoint].)  *)

(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 5 stars, advanced, optional (filter_challenge_2)  *)
(** A different way to formally characterize the behavior of [filter]
    goes like this: Among all subsequences of [l] with the property
    that [test] evaluates to [true] on all their members, [filter test
    l] is the longest.  Express this claim formally and prove it. *)

(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 4 stars, advanced (NoDup)  *)
(** Recall the definition of the [In] property of the [Logic] chapter,
    which asserts that a value [x] appears at least once in a list
    [l]: *)

(* Fixpoint In (A : Type) (x : A) (l : list A) : Prop :=
   match l with
   | [] => False
   | x' :: l' => x' = x \/ In A x l'
   end *)

(** Your first task is to use [In] to define a proposition [disjoint X
    l1 l2], which should be provable exactly when [l1] and [l2] are
    lists (with elements of type X) that have no elements in
    common. *)

(* FILL IN HERE *)

(** Next, use [In] to define an inductive proposition [NoDup X
    l], which should be provable exactly when [l] is a list (with
    elements of type [X]) where every member is different from every
    other.  For example, [NoDup nat [1;2;3;4]] and [NoDup
    bool []] should be provable, while [NoDup nat [1;2;1]] and
    [NoDup bool [true;true]] should not be.  *)

(* FILL IN HERE *)

(** Finally, state and prove one or more interesting theorems relating
    [disjoint], [NoDup] and [++] (list append).  *)

(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 3 stars, recommended (nostutter)  *)
(** Formulating inductive definitions of properties is an important
    skill you'll need in this course.  Try to solve this exercise
    without any help at all.

    We say that a list "stutters" if it repeats the same element
    consecutively.  The property "[nostutter mylist]" means that
    [mylist] does not stutter.  Formulate an inductive definition for
    [nostutter].  (This is different from the [NoDup] property in the
    exercise above; the sequence [1;4;1] repeats but does not
    stutter.) *)

Inductive nostutter {X:Type} : list X -> Prop :=
 (* FILL IN HERE *)
.

(** Make sure each of these tests succeeds, but you are free
    to change the proof if the given one doesn't work for you.
    Your definition might be different from mine and still correct,
    in which case the examples might need a different proof.

    The suggested proofs for the examples (in comments) use a number
    of tactics we haven't talked about, to try to make them robust
    with respect to different possible ways of defining [nostutter].
    You should be able to just uncomment and use them as-is, but if
    you prefer you can also prove each example with more basic
    tactics.  *)

Example test_nostutter_1:      nostutter [3;1;4;1;5;6].
(* FILL IN HERE *) Admitted.
(* 
  Proof. repeat constructor; apply beq_nat_false_iff; auto.
  Qed.
*)

Example test_nostutter_2:  nostutter (@nil nat).
(* FILL IN HERE *) Admitted.
(* 
  Proof. repeat constructor; apply beq_nat_false_iff; auto.
  Qed.
*)

Example test_nostutter_3:  nostutter [5].
(* FILL IN HERE *) Admitted.
(* 
  Proof. repeat constructor; apply beq_nat_false; auto. Qed.
*)

Example test_nostutter_4:      not (nostutter [3;1;1;4]).
(* FILL IN HERE *) Admitted.
(* 
  Proof. intro.
  repeat match goal with
    h: nostutter _ |- _ => inversion h; clear h; subst
  end.
  contradiction H1; auto. Qed.
*)
(** [] *)

(** **** Exercise: 4 stars, advanced (pigeonhole principle)  *)
(** The "pigeonhole principle" states a basic fact about counting:
   if you distribute more than [n] items into [n] pigeonholes, some
   pigeonhole must contain at least two items.  As is often the case,
   this apparently trivial fact about numbers requires non-trivial
   machinery to prove, but we now have enough... *)

(** First a useful lemma (we already proved it for lists of naturals,
    but not for arbitrary lists). *)

Lemma in_split : forall (X:Type) (x:X) (l:list X),
  In x l ->
  exists l1 l2, l = l1 ++ x :: l2.
Proof.
  (* FILL IN HERE *) Admitted.

(** Now define a property [repeats] such that [repeats X l] asserts
    that [l] contains at least one repeated element (of type [X]).  *)

Inductive repeats {X:Type} : list X -> Prop :=
  (* FILL IN HERE *)
.

(** Now here's a way to formalize the pigeonhole principle. List [l2]
    represents a list of pigeonhole labels, and list [l1] represents
    the labels assigned to a list of items: if there are more items
    than labels, at least two items must have the same label.  This
    proof is much easier if you use the [excluded_middle] hypothesis
    to show that [In] is decidable, i.e. [forall x l, (In x l) \/ ~
    (In x l)].  However, it is also possible to make the proof go
    through _without_ assuming that [In] is decidable; if you can
    manage to do this, you will not need the [excluded_middle]
    hypothesis. *)

Theorem pigeonhole_principle: forall (X:Type) (l1  l2:list X),
   excluded_middle ->
   (forall x, In x l1 -> In x l2) ->
   length l2 < length l1 ->
   repeats l1.
Proof.
   intros X l1. induction l1 as [|x l1' IHl1'].
  (* FILL IN HERE *) Admitted.
(** [] *)

(* FILL IN HERE *)


(** $Date: 2015-08-11 12:03:04 -0400 (Tue, 11 Aug 2015) $ *no)