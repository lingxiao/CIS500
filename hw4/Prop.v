(** * Prop: Propositions and Evidence *)

Require Export Logic.
Require Export Basics.
Require Export Induction.

(* ####################################################### *)
(** * Inductively Defined Propositions *)

(** In chapter [Basics] we defined a _function_ [evenb] that tests a
    number for evenness, yielding [true] if so.  We can use this
    function to define the _proposition_ that some number [n] is
    even: *)

Definition even (n:nat) : Prop := 
  evenb n = true.

(** That is, we can define "[n] is even" to mean "the function [evenb]
    returns [true] when applied to [n]."  

    Note that here we have given a name

    to a proposition using a [Definition], just as we have
    given names to expressions of other sorts. This isn't a fundamentally
    new kind of proposition;  it is still just an equality. *)

(** Another alternative is to define the concept of evenness
    directly.  Instead of going via the [evenb] function ("a number is
    even if a certain computation yields [true]"), we can say what the
    concept of evenness means by giving two different ways of
    presenting _evidence_ that a number is even. *)

Inductive ev : nat -> Prop :=
  | ev_0  : ev O
  | ev_SS : forall n:nat, ev n -> ev (S (S n)).


(** The first line declares that [ev] is a proposition -- or,
    more formally, a family of propositions "indexed by" natural
    numbers.  (That is, for each number [n], the claim that "[n] is
    even" is a proposition.)  Such a family of propositions is
    often called a _property_ of numbers.  

    The last two lines declare the two ways to give evidence that a
    number [m] is even.  First, [0] is even, and [ev_0] is evidence
    for this.  Second, if [m = S (S n)] for some [n] and we can give
    evidence [e] that [n] is even, then [m] is also even, and [ev_SS n
    e] is the evidence.
*)


(** **** Exercise: 1 star (double_even)  *)

Theorem double_even : forall n,
  ev (double n).
Proof.
 intros n. induction n.
   + simpl. 
   + 


(* ##################################################### *)

(** For [ev], we had already defined [even] as a function (returning a
   boolean), and then defined an inductive relation that agreed with
   it. However, we don't necessarily need to think about propositions
   first as boolean functions, we can start off with the inductive
   definition.
*)

(** As another example of an inductively defined proposition, let's
    define a simple property of natural numbers -- we'll call it
    "[beautiful]." *)

(** Informally, a number is [beautiful] if it is [0], [3], [5], or the
    sum of two [beautiful] numbers.  

    More pedantically, we can define [beautiful] numbers by giving four
    rules:

       - Rule [b_0]: The number [0] is [beautiful].
       - Rule [b_3]: The number [3] is [beautiful]. 
       - Rule [b_5]: The number [5] is [beautiful]. 
       - Rule [b_sum]: If [n] and [m] are both [beautiful], then so is
         their sum. *)

(** We will see many definitions like this one during the rest
    of the course, and for purposes of informal discussions, it is
    helpful to have a lightweight notation that makes them easy to
    read and write.  _Inference rules_ are one such notation: *)
(**
                              -----------                               (b_0)
                              beautiful 0
                              
                              ------------                              (b_3)
                              beautiful 3

                              ------------                              (b_5)
                              beautiful 5    

                       beautiful n     beautiful m
                       ---------------------------                      (b_sum)
                              beautiful (n+m)   
*)

(** *** *)
(** Each of the textual rules above is reformatted here as an
    inference rule; the intended reading is that, if the _premises_
    above the line all hold, then the _conclusion_ below the line
    follows.  For example, the rule [b_sum] says that, if [n] and [m]
    are both [beautiful] numbers, then it follows that [n+m] is
    [beautiful] too.  If a rule has no premises above the line, then
    its conclusion holds unconditionally.

    These rules _define_ the property [beautiful].  That is, if we
    want to convince someone that some particular number is [beautiful],
    our argument must be based on these rules.  For a simple example,
    suppose we claim that the number [5] is [beautiful].  To support
    this claim, we just need to point out that rule [b_5] says so.
    Or, if we want to claim that [8] is [beautiful], we can support our
    claim by first observing that [3] and [5] are both [beautiful] (by
    rules [b_3] and [b_5]) and then pointing out that their sum, [8],
    is therefore [beautiful] by rule [b_sum].  This argument can be
    expressed graphically with the following _proof tree_: *)
(**
         ----------- (b_3)   ----------- (b_5)
         beautiful 3         beautiful 5
         ------------------------------- (b_sum)
                   beautiful 8   
*)
(** *** *)
(** 
    Of course, there are other ways of using these rules to argue that
    [8] is [beautiful], for instance:
         ----------- (b_5)   ----------- (b_3)
         beautiful 5         beautiful 3
         ------------------------------- (b_sum)
                   beautiful 8   
*)

(** **** Exercise: 1 star (varieties_of_beauty)  *)
(** How many different ways are there to show that [8] is [beautiful]? *)

(* FILL IN HERE *)
(** [] *)

(* ####################################################### *)
(** ** Constructing Evidence *)

(** In Coq, we can express the definition of [beautiful] as
    follows: *)

Inductive beautiful : nat -> Prop :=
  b_0   : beautiful 0
| b_3   : beautiful 3
| b_5   : beautiful 5
| b_sum : forall n m, beautiful n -> beautiful m -> beautiful (n+m).

(** *** *)
(** 
    The rules introduced this way have the same status as proven 
    theorems; that is, they are true axiomatically. 
    So we can use Coq's [apply] tactic with the rule names to prove 
    that particular numbers are [beautiful].  *)

Theorem three_is_beautiful: beautiful 3.
Proof.
   (* This simply follows from the rule [b_3]. *)
   apply b_3.
Qed.

Theorem eight_is_beautiful: beautiful 8.
Proof.
   (* First we use the rule [b_sum], telling Coq how to
      instantiate [n] and [m]. *)
   apply b_sum with (n:=3) (m:=5).
   (* To solve the subgoals generated by [b_sum], we must provide
      evidence of [beautiful 3] and [beautiful 5]. Fortunately we
      have rules for both. *)
   apply b_3.
   apply b_5.
Qed.

(** *** *)
(** As you would expect, we can also prove theorems that have
hypotheses about [beautiful]. *)

Theorem beautiful_plus_eight: forall n, beautiful n -> beautiful (8+n).
Proof.
  intros n B.
  apply b_sum with (n:=8) (m:=n).
  apply eight_is_beautiful.
  apply B.
Qed.

(** **** Exercise: 2 stars (b_times2)  *)
Theorem b_times2: forall n, beautiful n -> beautiful (2*n).
Proof.
    (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars (b_timesm)  *)
Theorem b_timesm: forall n m, beautiful n -> beautiful (m*n).
Proof.
   (* FILL IN HERE *) Admitted.
(** [] *)


(* ####################################################### *)
(** * Using Evidence in Proofs *)
(** ** Induction over Evidence *)

(** Besides _constructing_ evidence that numbers are beautiful, we can
    also _reason about_ such evidence. *)

(** The fact that we introduced [beautiful] with an [Inductive]
    declaration tells Coq not only that the constructors [b_0], [b_3],
    [b_5] and [b_sum] are ways to build evidence, but also that these
    four constructors are the _only_ ways to build evidence that
    numbers are beautiful. *)

(** In other words, if someone gives us evidence [E] for the assertion
    [beautiful n], then we know that [E] must have one of four shapes:

      - [E] is [b_0] (and [n] is [O]),
      - [E] is [b_3] (and [n] is [3]), 
      - [E] is [b_5] (and [n] is [5]), or 
      - [E] is [b_sum n1 n2 E1 E2] (and [n] is [n1+n2], where [E1] is
        evidence that [n1] is beautiful and [E2] is evidence that [n2]
        is beautiful). *)

(** *** *)    
(** This permits us to _analyze_ any hypothesis of the form [beautiful
    n] to see how it was constructed, using the tactics we already
    know.  In particular, we can use the [induction] tactic that we
    have already seen for reasoning about inductively defined _data_
    to reason about inductively defined _evidence_.

    To illustrate this, let's define another property of numbers: *)

Inductive gorgeous : nat -> Prop :=
  g_0 : gorgeous 0
| g_plus3 : forall n, gorgeous n -> gorgeous (3+n)
| g_plus5 : forall n, gorgeous n -> gorgeous (5+n).

(** **** Exercise: 1 star (gorgeous_tree)  *)
(** Write out the definition of [gorgeous] numbers using inference rule
    notation.
 
(* FILL IN HERE *)
[]
*)


(** **** Exercise: 1 star (gorgeous_plus13)  *)
Theorem gorgeous_plus13: forall n, 
  gorgeous n -> gorgeous (13+n).
Proof.
   (* FILL IN HERE *) Admitted.
(** [] *)

(** *** *)
(** It seems intuitively obvious that, although [gorgeous] and
    [beautiful] are presented using slightly different rules, they are
    actually the same property in the sense that they are true of the
    same numbers.  Indeed, we can prove this. *)


Theorem gorgeous__beautiful_FAILED : forall n, 
  gorgeous n -> beautiful n.
Proof.
   intros. induction n as [| n'].
   - (* n = 0 *) apply b_0.
   - (* n = S n' *) (* We are stuck! *)
Abort.

(** The problem here is that doing induction on [n] doesn't yield a
    useful induction hypothesis. Knowing how the property we are
    interested in behaves on the predecessor of [n] doesn't help us
    prove that it holds for [n]. Instead, we would like to be able to
    have induction hypotheses that mention other numbers, such as [n -
    3] and [n - 5]. This is given precisely by the shape of the
    constructors for [gorgeous]. *)


(** *** *)

(** Let's see what happens if we try to prove this by induction on the evidence [H]
   instead of on [n]. *)

Theorem gorgeous__beautiful : forall n, 
  gorgeous n -> beautiful n.
Proof.
   intros n H.
   induction H as [|n'|n'].
   - (* g_0 *)
       apply b_0.
   - (* g_plus3 *) 
       apply b_sum. apply b_3.
       apply IHgorgeous.
   - (* g_plus5 *)
       apply b_sum. apply b_5. apply IHgorgeous. 
Qed.


(* These exercises also require the use of induction on the evidence. *)

(** **** Exercise: 2 stars (gorgeous_sum)  *)
Theorem gorgeous_sum : forall n m,
  gorgeous n -> gorgeous m -> gorgeous (n + m).
Proof.
 (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, advanced (beautiful__gorgeous)  *)
Theorem beautiful__gorgeous : forall n, beautiful n -> gorgeous n.
Proof.
 (* FILL IN HERE *) Admitted.
(** [] *)




(** **** Exercise: 3 stars, optional (g_times2)  *)
(** Prove the [g_times2] theorem below without using [gorgeous__beautiful].
    You might find the following helper lemma useful. *)

Lemma helper_g_times2 : forall x y z, x + (z + y) = z + x + y.
Proof.
   (* FILL IN HERE *) Admitted.

Theorem g_times2: forall n, gorgeous n -> gorgeous (2*n).
Proof.
   intros n H. simpl. 
   induction H.
   (* FILL IN HERE *) Admitted.
(** [] *)



(** Here is a proof that the inductive definition of evenness implies
the computational one. *)

Theorem ev__even : forall n,
  ev n -> even n.
Proof.
  intros n E. induction E as [| n' E'].
  - (* E = ev_0 *) 
    unfold even. reflexivity.
  - (* E = ev_SS n' E' *)  
    unfold even. apply IHE'.  
Qed.

(** **** Exercise: 1 star (ev__even)  *) 
(** Could this proof also be carried out by induction on [n] instead
    of [E]?  If not, why not? *)

(* FILL IN HERE *)
(** [] *)

(** Intuitively, the induction principle for evidence [ev n] is
    similar to induction on [n], but restricts our attention to only
    those numbers for which evidence [ev n] could be generated. *)

(** **** Exercise: 1 star (l_fails)  *)
(** The following proof attempt will not succeed.
     Theorem l : forall n,
       ev n.
     Proof.
       intros n. induction n.
         - (* O *) simpl. apply ev_0.
         - (* S *)
           ...
   Intuitively, we expect the proof to fail because not every
   number is even. However, what exactly causes the proof to fail?

(* FILL IN HERE *)
*)
(** [] *)

(** Here's another exercise requiring induction on evidence. *)
(** **** Exercise: 2 stars (ev_sum)  *)

Theorem ev_sum : forall n m,
   ev n -> ev m -> ev (n+m).
Proof. 
  (* FILL IN HERE *) Admitted.
(** [] *)



(* ####################################################### *)
(** ** Inversion on Evidence *)


(** Having evidence for a proposition is useful while proving, because we 
   can _look_ at that evidence for more information. For example, consider 
    proving that, if [n] is even, then [pred (pred n)] is
    too.  In this case, we don't need to do an inductive proof.  Instead 
    the [inversion] tactic provides all of the information that we need.

 *)

Theorem ev_minus2: forall n,  ev n -> ev (pred (pred n)). 
Proof.
  intros n E.
  inversion E as [| n' E'].
  - (* E = ev_0 *) simpl. apply ev_0. 
  - (* E = ev_SS n' E' *) simpl. apply E'.  Qed.

(** **** Exercise: 1 star, optional (ev_minus2_n)  *)
(** What happens if we try to use [destruct] on [n] instead of [inversion] on [E]? *)

(* FILL IN HERE *)
(** [] *)

(** *** *)
(** Here is another example, in which [inversion] helps narrow down to
the relevant cases. *)

Theorem SSev__even : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E. 
  inversion E as [| n' E']. 
  apply E'. Qed.

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


(** **** Exercise: 1 star (inversion_practice)  *)
Theorem SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  (* FILL IN HERE *) Admitted.

(** The [inversion] tactic can also be used to derive goals by showing
    the absurdity of a hypothesis. *)

Theorem even5_nonsense : 
  ev 5 -> 2 + 2 = 9.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, advanced (ev_ev__ev)  *)
(** Finding the appropriate thing to do induction on is a
    bit tricky here: *)

Theorem ev_ev__ev : forall n m,
  ev (n+m) -> ev n -> ev m.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, optional (ev_plus_plus)  *)
(** Here's an exercise that just requires applying existing lemmas.  No
    induction or even case analysis is needed, but some of the rewriting
    may be tedious. *)

Theorem ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)


(* ####################################################### *)
(** * Discussion and Variations *)
(** ** Computational vs. Inductive Definitions *)

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
    means to give evidence for the property [beautiful] is
    straightforward. *)




(* ####################################################### *)
(** ** Parameterized Data Structures *)

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

Lemma ev_length__ev_list: forall X n, ev n -> forall (l : list X), n = length l -> ev_list l.
Proof.
  intros X n H. 
  induction H.
  - (* ev_0 *) intros l H. destruct l.
    + (* [] *) apply el_nil. 
    + (* x::l *) inversion H.
  - (* ev_SS *) intros l H2. destruct l as [| x [| x0 l]]. 
    + (* [] *) inversion H2. 
    + (* [x] *) inversion H2.
    + (* x :: x0 :: l *) apply el_cc. apply IHev. inversion H2. reflexivity.
Qed.
    

(** **** Exercise: 4 stars (palindromes)  *)
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

(* FILL IN HERE *)
(** [] *)

(* Again, the converse direction is much more difficult, due to the
lack of evidence. *)

(** **** Exercise: 5 stars, optional (palindrome_converse)  *)
(** Using your definition of [pal] from the previous exercise, prove
    that
     forall l, l = rev l -> pal l.
*)

(* FILL IN HERE *)
(** [] *)



(* ####################################################### *)
(** ** Relations *)

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

(** *** *)
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

(** *** *)
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

(** **** Exercise: 2 stars (total_relation)  *)
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

Theorem ble_nat_true : forall n m,
  ble_nat n m = true -> n <= m.
Proof. 
  (* FILL IN HERE *) Admitted.

Theorem le_ble_nat : forall n m,
  n <= m ->
  ble_nat n m = true.
Proof.
  (* Hint: This may be easiest to prove by induction on [m]. *)
  (* FILL IN HERE *) Admitted.

Theorem ble_nat_true_trans : forall n m o,
  ble_nat n m = true -> ble_nat m o = true -> ble_nat n o = true.                               
Proof.
  (* Hint: This theorem can be easily proved without using [induction]. *)
  (* FILL IN HERE *) Admitted.

(** **** Exercise: 2 stars, optional (ble_nat_false)  *)
Theorem ble_nat_false : forall n m,
  ble_nat n m = false -> ~(n <= m).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)


(** **** Exercise: 3 stars (R_provability2)  *)
Module R.
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


(* ##################################################### *)
(** * Programming with Propositions *)

(** As we have seen, a _proposition_ is a statement expressing a factual claim,
    like "two plus two equals four."  In Coq, propositions are written
    as expressions of type [Prop]. . *)

Check (2 + 2 = 4).
(* ===> 2 + 2 = 4 : Prop *)

Check (ble_nat 3 2 = false).
(* ===> ble_nat 3 2 = false : Prop *)

Check (beautiful 8).
(* ===> beautiful 8 : Prop *)

(** *** *)
(** Both provable and unprovable claims are perfectly good
    propositions.  Simply _being_ a proposition is one thing; being
    _provable_ is something else! *)

Check (2 + 2 = 5).
(* ===> 2 + 2 = 5 : Prop *)

Check (beautiful 4).
(* ===> beautiful 4 : Prop *)

(** Both [2 + 2 = 4] and [2 + 2 = 5] are legal expressions
    of type [Prop]. *)

(** *** *)
(** We've mainly seen one place that propositions can appear in Coq: in
    [Theorem] (and [Lemma] and [Example]) declarations. *)

Theorem plus_2_2_is_4 : 
  2 + 2 = 4.
Proof. reflexivity.  Qed.

(** But they can be used in many other ways.  For example, we have also seen that
    we can give a name to a proposition using a [Definition], just as we have
    given names to expressions of other sorts. *)

Definition plus_fact : Prop  :=  2 + 2 = 4.
Check plus_fact.
(* ===> plus_fact : Prop *)

(** We can later use this name in any situation where a proposition is
    expected -- for example, as the claim in a [Theorem] declaration. *)

Theorem plus_fact_is_true : 
  plus_fact.
Proof. reflexivity.  Qed.

(** *** *)
(** We've seen several ways of constructing propositions.  

       - We can define a new proposition primitively using [Inductive].

       - Given two expressions [e1] and [e2] of the same type, we can
         form the proposition [e1 = e2], which states that their
         values are equal.

       - We can combine propositions using implication and
         quantification. *)
(** *** *)
(** We have also seen _parameterized propositions_, such as [even] and
    [beautiful]. *)

Check (even 4).
(* ===> even 4 : Prop *)
Check (even 3).
(* ===> even 3 : Prop *)
Check even. 
(* ===> even : nat -> Prop *)

(** *** *)
(** The type of [even], i.e., [nat->Prop], can be pronounced in
    three equivalent ways: (1) "[even] is a _function_ from numbers to
    propositions," (2) "[even] is a _family_ of propositions, indexed
    by a number [n]," or (3) "[even] is a _property_ of numbers."  *)

(** Propositions -- including parameterized propositions -- are
    first-class citizens in Coq.  For example, we can define functions
    from numbers to propositions... *)

Definition between (n m o: nat) : Prop :=
  andb (ble_nat n o) (ble_nat o m) = true.

(** ... and then partially apply them: *)

Definition teen : nat->Prop := between 13 19.

(** We can even pass propositions -- including parameterized
    propositions -- as arguments to functions: *)

Definition true_for_zero (P:nat->Prop) : Prop :=
  P 0.

(** *** *)
(** Here are two more examples of passing parameterized propositions
    as arguments to a function.  

    The first function, [true_for_all_numbers], takes a proposition
    [P] as argument and builds the proposition that [P] is true for
    all natural numbers. *)

Definition true_for_all_numbers (P:nat->Prop) : Prop :=
  forall n, P n.

(** The second, [preserved_by_S], takes [P] and builds the proposition
    that, if [P] is true for some natural number [n'], then it is also
    true by the successor of [n'] -- i.e. that [P] is _preserved by
    successor_: *)

Definition preserved_by_S (P:nat->Prop) : Prop :=
  forall n', P n' -> P (S n').

(** *** *)
(** Finally, we can put these ingredients together to define
a proposition stating that induction is valid for natural numbers: *)

Definition natural_number_induction_valid : Prop :=
  forall (P:nat->Prop),
    true_for_zero P ->
    preserved_by_S P -> 
    true_for_all_numbers P. 





(** **** Exercise: 3 stars (combine_odd_even)  *)
(** Complete the definition of the [combine_odd_even] function
    below. It takes as arguments two properties of numbers [Podd] and
    [Peven]. As its result, it should return a new property [P] such
    that [P n] is equivalent to [Podd n] when [n] is odd, and
    equivalent to [Peven n] otherwise. *)

Definition combine_odd_even (Podd Peven : nat -> Prop) : nat -> Prop :=
  (* FILL IN HERE *) admit.

(** To test your definition, see whether you can prove the following
    facts: *)

Theorem combine_odd_even_intro : 
  forall (Podd Peven : nat -> Prop) (n : nat),
    (oddb n = true -> Podd n) ->
    (oddb n = false -> Peven n) ->
    combine_odd_even Podd Peven n.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem combine_odd_even_elim_odd :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = true ->
    Podd n.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem combine_odd_even_elim_even :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = false ->
    Peven n.
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)

(* ##################################################### *)
(** One more quick digression, for adventurous souls: if we can define
    parameterized propositions using [Definition], then can we also
    define them using [Fixpoint]?  Of course we can!  However, this
    kind of "recursive parameterization" doesn't correspond to
    anything very familiar from everyday mathematics.  The following
    exercise gives a slightly contrived example. *)

(** **** Exercise: 4 stars, optional (true_upto_n__true_everywhere)  *)
(** Define a recursive function
    [true_upto_n__true_everywhere] that makes
    [true_upto_n_example] work. *)

(* 
Fixpoint true_upto_n__true_everywhere
(* FILL IN HERE *)

Example true_upto_n_example :
    (true_upto_n__true_everywhere 3 (fun n => even n))
  = (even 3 -> even 2 -> even 1 -> forall m : nat, even m).
Proof. reflexivity.  Qed.
*)
(** [] *)

(** $Date: 2015-08-11 12:03:04 -0400 (Tue, 11 Aug 2015) $ *)

(** * Poly: Polymorphism and Higher-Order Functions *)

Require Export Lists.


(* ###################################################### *)
(** * Polymorphism *)

(** In this chapter we continue our development of basic
    concepts of functional programming.  The critical new ideas are
    _polymorphism_ (abstracting functions over the types of the data
    they manipulate) and _higher-order functions_ (treating functions
    as data).  We begin with polymorphism.
*)

(* ###################################################### *)
(** ** Polymorphic Lists *)

(** For the last couple of chapters, we've been working just
    with lists of numbers.  Obviously, interesting programs also need
    to be able to manipulate lists with elements from other types --
    lists of strings, lists of booleans, lists of lists, etc.  We
    _could_ just define a new inductive datatype for each of these,
    for example... *)

Inductive boollist : Type :=
  | bool_nil : boollist
  | bool_cons : bool -> boollist -> boollist.

(** ... but this would quickly become tedious, partly because we
    have to make up different constructor names for each datatype, but
    mostly because we would also need to define new versions of all
    our list manipulating functions ([length], [rev], etc.)  for each
    new datatype definition. *)

(** To avoid all this repetition, Coq supports _polymorphic_
    inductive type definitions.  For example, here is a _polymorphic
    list_ datatype. *)

Inductive list (X:Type) : Type :=
  | nil : list X
  | cons : X -> list X -> list X.



(** This is exactly like the definition of [natlist] from the
    previous chapter, except that the [nat] argument to the [cons]
    constructor has been replaced by an arbitrary type [X], a binding
    for [X] has been added to the header, and the occurrences of
    [natlist] in the types of the constructors have been replaced by
    [list X].  (We can re-use the constructor names [nil] and [cons]
    because the earlier definition of [natlist] was inside of a
    [Module] definition that is now out of scope.) *)

(** What sort of thing is [list] itself?  One good way to think
    about it is that [list] is a _function_ from [Type]s to
    [Inductive] definitions; or, to put it another way, [list] is a
    function from [Type]s to [Type]s.  For any particular type [X],
    the type [list X] is an [Inductive]ly defined set of lists whose
    elements are things of type [X]. *)

(*
    list : Type -> Type
    list X = nil | cons X (list X)
*)


(** With this definition, when we use the constructors [nil] and
    [cons] to build lists, we need to tell Coq the type of the
    elements in the lists we are building -- that is, [nil] and [cons]
    are now _polymorphic constructors_.  Observe the types of these
    constructors: *)

Check nil.
(* ===> nil : forall X : Type, list X *)
Check cons.
(* ===> cons : forall X : Type, X -> list X -> list X *)

(** (Side note on notation: In .v files, the "forall" quantifier is
    spelled out in letters.  In the generated HTML files, [forall] is
    usually typeset as the usual mathematical "upside down A," but
    you'll see the spelled-out "forall" in a few places, as in the
    above comments.  This is just a quirk of typesetting: there is no
    difference in meaning.) *)

(** The "[forall X]" in these types can be read as an additional
    argument to the constructors that determines the expected types of
    the arguments that follow.  When [nil] and [cons] are used, these
    arguments are supplied in the same way as the others.  For
    example, the list containing [2] and [1] is written like this: *)

Check (cons nat 2 (cons nat 1 (nil nat))).


(** (We've written [nil] and [cons] explicitly here because we haven't
    yet defined the [ [] ] and [::] notations for the new version of
    lists.  We'll do that in a bit.) *)

(** We can now go back and make polymorphic versions of all the
    list-processing functions that we wrote before.  Here is [length],
    for example: *)


Fixpoint length (X:Type) (l:list X) : nat :=
  match l with
  | nil      => 0
  | cons h t => S (length X t)
  end.

(** Note that the uses of [nil] and [cons] in [match] patterns
    do not require any type annotations: Coq already knows that the list
    [l] contains elements of type [X], so there's no reason to include
    [X] in the pattern.  (More precisely, the type [X] is a parameter
    of the whole definition of [list], not of the individual
    constructors.  We'll come back to this point later.)

    As with [nil] and [cons], we can use [length] by applying it first
    to a type and then to its list argument: *)

Example test_length1 :
    length nat (cons nat 1 (cons nat 2 (nil nat))) = 2.
Proof. reflexivity.  Qed.

(** To use [length] with other kinds of lists, we simply
    instantiate it with an appropriate type parameter: *)

Example test_length2 :
    length bool (cons bool true (nil bool)) = 1.
Proof. reflexivity.  Qed.

(** Let's finish by re-implementing a few other standard list
    functions on our new polymorphic lists... *)

Fixpoint app (X : Type) (l1 l2 : list X)
             : (list X) :=
  match l1 with
  | nil      => l2
  | cons h t => cons X h (app X t l2)
  end.

Fixpoint rev (X:Type) (l:list X) : list X :=
  match l with
  | nil      => nil X
  | cons h t => app X (rev X t) (cons X h (nil X))
  end.


Example test_rev1 :
  rev nat (cons nat 1 (cons nat 2 (nil nat)))
  = (cons nat 2 (cons nat 1 (nil nat))).
Proof. reflexivity.  Qed.

Example test_rev2:
  rev bool (nil bool) = nil bool.
Proof. reflexivity.  Qed.

Module MumbleGrumble.

(** **** Exercise: 2 stars (mumble_grumble)  *)
(** Consider the following two inductively defined types. *)

Inductive mumble : Type :=
  | a : mumble
  | b : mumble -> nat -> mumble
  | c : mumble.

Inductive grumble (X:Type) : Type :=
  | d : mumble -> grumble X
  | e : X -> grumble X.


Check (b a 5).
Check (d bool (b a 5)).
Check (e mumble (b c 0)).


Check (cons (grumble bool) (d bool (b a 5))) (nil (grumble bool)).
Check (cons (grumble mumble) (d mumble (b a 5)) (nil (grumble mumble))).
Check (cons (grumble bool) (e bool true) (nil (grumble bool))).
Check (cons (grumble mumble) (e mumble (b c 0)) (nil (grumble mumble))).
Check (cons mumble c) (nil mumble).


(** Which of the following are well-typed elements of [grumble X] for
    some type [X]?
      - [d (b a 5)]
      - [d mumble (b a 5)]
      - [d bool (b a 5)]
      - [e bool true]
      - [e mumble (b c 0)]

      - [e bool (b c 0)]
      - [c]
(* FILL IN HERE *)

      - [d mumble (b a 5)]
      - [d bool (b a 5)]
      - [e bool true]
      - [e mumble (b c 0)]

*)

End MumbleGrumble.


(* ###################################################### *)
(** *** Type Annotation Inference *)

(** Let's write the definition of [app] again, but this time we won't
    specify the types of any of the arguments. Will Coq still accept
    it? *)

Fixpoint app' X l1 l2 : list X :=
  match l1 with
  | nil      => l2
  | cons h t => cons X h (app' X t l2)
  end.

(** Indeed it will.  Let's see what type Coq has assigned to [app']: *)

Check app'.
(* ===> forall X : Type, list X -> list X -> list X *)
Check app.
(* ===> forall X : Type, list X -> list X -> list X *)

(** It has exactly the same type type as [app].  Coq was able to
    use _type inference_ to deduce what the types of [X], [l1], and
    [l2] must be, based on how they are used.  For example, since [X]
    is used as an argument to [cons], it must be a [Type], since
    [cons] expects a [Type] as its first argument; matching [l1] with
    [nil] and [cons] means it must be a [list]; and so on.

    This powerful facility means we don't always have to write
    explicit type annotations everywhere, although explicit type
    annotations are still quite useful as documentation and sanity
    checks, so we will continue to use them most of the time.  You
    should try to find a balance in your own code between too many
    type annotations (which can clutter and distract) and too
    few (which forces readers to perform type inference in their heads
    in order to understand your code). *)

(* ###################################################### *)
(** *** Type Argument Synthesis *)

(** To we use a polymorphic function, we need to pass it one or
    more types in addition to its other arguments.  For example, the
    recursive call in the body of the [length] function above must
    pass along the type [X].  But since the second argument to
    [length] is a list of [X]s, it seems entirely obvious that the
    first argument can only be [X] -- why should we have to write it
    explicitly?

    Fortunately, Coq permits us to avoid this kind of redundancy.  In
    place of any type argument we can write the "implicit argument"
    [_], which can be read as "Please try to figure out for yourself
    what belongs here."  More precisely, when Coq encounters a [_], it
    will attempt to _unify_ all locally available information -- the
    type of the function being applied, the types of the other
    arguments, and the type expected by the context in which the
    application appears -- to determine what concrete type should
    replace the [_].

    This may sound similar to type annotation inference -- indeed, the
    two procedures rely on the same underlying mechanisms.  Instead of
    simply omitting the types of some arguments to a function, like
      app' X l1 l2 : list X :=
    we can also replace the types with [_]
      app' (X : _) (l1 l2 : _) : list X :=
    to tell Coq to attempt to infer the missing information.

    Using implicit arguments, the [length] function can be written
    like this: *)

Fixpoint length' (X:Type) (l:list X) : nat :=
  match l with
  | nil      => 0
  | cons h t => S (length' _ t)
  end.

(** In this instance, we don't save much by writing [_] instead of
    [X].  But in many cases the difference in both keystrokes and
    readability is nontrivial.  For example, suppose we want to write
    down a list containing the numbers [1], [2], and [3].  Instead of
    writing this... *)

Definition list123 :=
  cons nat 1 (cons nat 2 (cons nat 3 (nil nat))).

(** ...we can use argument synthesis to write this: *)

Definition list123' :=
  cons _ 1 (cons _ 2 (cons _ 3 (nil _))).

(* ###################################################### *)
(** *** Implicit Arguments *)

(** We can go further and even avoid writing [_]'s in most cases by
    telling Coq _always_ to infer the type argument(s) of a given
    function.  The [Arguments] directive specifies the name of the
    function (or constructor) and then lists its argument names, with
    curly braces around any arguments to be treated as implicit.  (If
    some arguments of a definition don't have a name, as is often the
    case for constructors, they can be marked with a wildcard pattern
    [_].) *)

Definition list123''' := cons _ 1 (cons _ 2 (cons nat 3 (nil _))).

Arguments nil {X}.
Arguments cons {X} _ _.
Arguments length {X} l.
Arguments app {X} l1 l2.
Arguments rev {X} l.

(** Now, we don't have to supply type arguments at all: *)

Definition list123'' := cons 1 (cons 2 (cons 3 nil)).
Check (length list123'').

(** Alternatively, we can declare an argument to be implicit
    when defining the function itself, by surrounding it in curly
    braces.  For example: *)

Fixpoint length'' {X:Type} (l:list X) : nat :=
  match l with
  | nil      => 0
  | cons h t => S (length'' t)
  end.

(** (Note that we didn't even have to provide a type argument to the
    recursive call to [length'']; indeed, it would be invalid to
    provide one!)

    We will use the latter style whenever possible, but we will
    continue to use use explicit [Argument] declarations for
    [Inductive] constructors.  The reason for this is that marking the
    parameter of an inductive type as implicit causes it to become
    implicit for the type itself, not just for its constructors.  For
    instance, consider the following alternative definition of the
    [list] type: *)

Inductive list' {X:Type} : Type :=
  | nil' : list'
  | cons' : X -> list' -> list'.

(** Because [X] is declared as implicit for the _entire_ inductive
    definition including [list'] itself, we now have to write just
    [list'] whether we are talking about lists of numbers or booleans
    or anything else, rather than [list' nat] or [list' bool] or
    whatever; this is a step too far. *)

(** One small problem with declaring arguments [Implicit] is
    that, occasionally, Coq does not have enough local information to
    determine a type argument; in such cases, we need to tell Coq that
    we want to give the argument explicitly just this time.  For
    example, suppose we write this: *)

Fail Definition mynil := nil.

(** (The [Fail] qualifier that appears before [Definition] can be
    used with _any_ command, and is used to ensure that that command
    indeed fails when executed. If the command does fail, Coq prints
    the corresponding error message, but continues processing the rest
    of the file.)

    Here, Coq gives us an error because it doesn't know what type
    argument to supply to [nil].  We can help it by providing an
    explicit type declaration (so that Coq has more information
    available when it gets to the "application" of [nil]): *)

Definition mynil : list nat := nil.

(** Alternatively, we can force the implicit arguments to be explicit by
   prefixing the function name with [@]. *)

Check @nil.

Definition mynil' := @nil nat.


(** Using argument synthesis and implicit arguments, we can
    define convenient notation for lists, as before.  Since we have
    made the constructor type arguments implicit, Coq will know to
    automatically infer these when we use the notations. *)

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

(** Now lists can be written just the way we'd hope: *)

Definition list123'''' := [1; 2; 3].





(* ###################################################### *)
(** *** Exercises *)

(** **** Exercise: 2 stars, optional (poly_exercises)  *)
(** Here are a few simple exercises, just like ones in the [Lists]
    chapter, for practice with polymorphism.  Fill in the definitions
    and complete the proofs below. *)

Fixpoint repeat {X : Type} (n : X) (count : nat) : list X :=
  match count with
      | O    => nil
      | S c' => cons n (repeat n c')
  end.


Example test_repeat1:
  repeat true 2 = cons true (cons true nil).
Proof. reflexivity. Qed.
  

Theorem app_nil_r : forall (X:Type), forall l:list X,
  l ++ [] = l.
Proof.
  intros X l. induction l.
    + reflexivity.
    + simpl. rewrite -> IHl. reflexivity.
Qed.  
  

Theorem app_assoc : forall A (l m n:list A),
  l ++ m ++ n = (l ++ m) ++ n.
Proof.
  intros A l m n. induction l.
    + simpl. reflexivity.
    + simpl. rewrite -> IHl. reflexivity.
Qed.


Lemma app_length : forall (X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros X l1 l2. induction l1.
    + reflexivity.
    + simpl. rewrite <- IHl1. reflexivity.
Qed.


Theorem cons_app_equiv : forall (X : Type) (l : list X) (x : X),
  x::l = [x] ++ l.
Proof.                           
  intros X l x. induction l.
    + simpl. reflexivity.
    + simpl. reflexivity.
Qed.

(** **** Exercise: 2 stars, optional (more_poly_exercises)  *)
(** Here are some slightly more interesting ones... *)

Theorem app_r_id : forall (X:Type), forall l : list X,
  l ++ [] = l.
Proof.
  intros X l. induction l as [|n l' IHl'].
    + simpl. reflexivity.
    + simpl. rewrite -> IHl'. reflexivity.
Qed.

Theorem rev_app_distr: forall X (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros X l1 l2. induction l1.
    + simpl. rewrite -> app_r_id. reflexivity.
    + simpl. rewrite -> IHl1. rewrite -> app_assoc. reflexivity.
Qed.   

Theorem rev_involutive : forall X : Type, forall l : list X,
  rev (rev l) = l.
Proof.
  intros X l. induction l.
    + simpl. reflexivity.
    + simpl. rewrite -> rev_app_distr. rewrite -> IHl. simpl. reflexivity.
Qed.

(* ###################################################### *)
(** ** Polymorphic Pairs *)

(** Following the same pattern, the type definition we gave in
    the last chapter for pairs of numbers can be generalized to
    _polymorphic pairs_, often called _products_: *)

Inductive prod (X Y : Type) : Type :=
| pair : X -> Y -> prod X Y.

Arguments pair {X} {Y} _ _.

(** As with lists, we make the type arguments implicit and define the
    familiar concrete notation. *)

Notation "( x , y )" := (pair x y).

(** We can also use the [Notation] mechanism to define the standard
    notation for product _types_: *)

Notation "X * Y" := (prod X Y) : type_scope.

(** (The annotation [: type_scope] tells Coq that this abbreviation
    should only be used when parsing types.  This avoids a clash with
    the multiplication symbol.) *)

(** It is easy at first to get [(x,y)] and [X*Y] confused.
    Remember that [(x,y)] is a _value_ built from two other values,
    while [X*Y] is a _type_ built from two other types.  If [x] has
    type [X] and [y] has type [Y], then [(x,y)] has type [X*Y]. *)

(** The first and second projection functions now look pretty
    much as they would in any functional programming language. *)

Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with
  | (x, y) => x
  end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with
  | (x, y) => y
  end.

(** The following function takes two lists and combines them
    into a list of pairs.  In other functional languages, it is often
    called [zip]; we call it [combine] for consistency with Coq's
    standard library. *)

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
           : list (X*Y):=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: (combine tx ty)
  end.

(** **** Exercise: 1 star, optional (combine_checks)  *)
(** Try answering the following questions on paper and
    checking your answers in coq:
    - What is the type of [combine] (i.e., what does [Check
      @combine] print?)

      combine: forall X Y : Type, list X -> list Y -> list (Prod X Y)

    - What does
        Compute (combine [1;2] [false;false;true;true]).
      print?   [(1,false),(2,false)] :: list (nat * bool)       
*)



(** **** Exercise: 2 stars, recommended (split)  *)
(** The function [split] is the right inverse of [combine]: it takes a
    list of pairs and returns a pair of lists.  In many functional
    languages, it is called [unzip].

    Uncomment the material below and fill in the definition of
    [split].  Make sure it passes the given unit test. *)


(* why isn't there a forall infront of X and Y ?? *)
Fixpoint map_ {X Y:Type} (f:X->Y) (l:list X) : (list Y) :=
  match l with
  | []     => []
  | h :: t => (f h) :: (map_ f t)
  end.

Fixpoint split {X Y : Type} (l : list (X*Y)) : (list X) * (list Y) :=
  (map_ fst l, map_ snd l).

Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof. reflexivity. Qed.

(* ###################################################### *)
(** ** Polymorphic Options *)

(** One last polymorphic type for now: _polymorphic options_,
    which generalize [natoption] from the previous chapter: *)

Inductive option (X:Type) : Type :=
  | Some : X -> option X
  | None : option X.

Arguments Some {X} _.
Arguments None {X}.

(** We can now rewrite the [nth_error] function so that it works
    with any type of lists. *)

Fixpoint nth_error {X : Type} (l : list X) (n : nat)
                   : option X :=
  match l with
  | [] => None
  | a :: l' => if beq_nat n O then Some a else nth_error l' (pred n)
  end.

Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. reflexivity.  Qed.
Example test_nth_error2 : nth_error [[1];[2]] 1 = Some [2].
Proof. reflexivity.  Qed.
Example test_nth_error3 : nth_error [true] 2 = None.
Proof. reflexivity. Qed.

(** **** Exercise: 1 star, optional (hd_error_poly)  *)
(** Complete the definition of a polymorphic version of the
    [hd_error] function from the last chapter. Be sure that it
    passes the unit tests below. *)

Definition hd_error {X : Type} (l : list X) : option X :=
  match l with
  | nil     => None
  | x :: _  => Some x
  end.                  

(** Once again, to force the implicit arguments to be explicit,
    we can use [@] before the name of the function. *)

Check @hd_error.

Example test_hd_error1 : hd_error [1;2] = Some 1.
Proof. reflexivity. Qed.
 
Example test_hd_error2 : hd_error  [[1];[2]]  = Some [1].
Proof. reflexivity. Qed.


(* ###################################################### *)
(** * Functions as Data *)

(** Like many other modern programming languages -- including
    all functional languages (ML, Haskell, Scheme, Scala, Clojure,
    etc.) -- Coq treats functions as first-class citizens, allowing
    them to be passed as arguments to other functions, returned as
    results, stored in data structures, etc.*)

(* ###################################################### *)
(** ** Higher-Order Functions *)

(** Functions that manipulate other functions are often called
    _higher-order_ functions.  Here's a simple one: *)

Definition doit3times {X:Type} (f:X->X) (n:X) : X :=
  f (f (f n)).

(** The argument [f] here is itself a function (from [X] to
    [X]); the body of [doit3times] applies [f] three times to some
    value [n]. *)

Check @doit3times.
(* ===> doit3times : forall X : Type, (X -> X) -> X -> X *)

Example test_doit3times: doit3times minustwo 9 = 3.
Proof. reflexivity.  Qed.

Example test_doit3times': doit3times negb true = false.
Proof. reflexivity.  Qed.

(* ###################################################### *)
(** ** Filter *)

(** Here is a more useful higher-order function, taking a list
    of [X]s and a _predicate_ on [X] (a function from [X] to [bool])
    and "filtering" the list, returning a new list containing just
    those elements for which the predicate returns [true]. *)

Fixpoint filter {X:Type} (test: X->bool) (l:list X)
                : (list X) :=
  match l with
  | []     => []
  | h :: t => if test h then h :: (filter test t)
                        else       filter test t
  end.

(** For example, if we apply [filter] to the predicate [evenb]
    and a list of numbers [l], it returns a list containing just the
    even members of [l]. *)

Example test_filter1: filter evenb [1;2;3;4] = [2;4].
Proof. reflexivity.  Qed.

Definition length_is_1 {X : Type} (l : list X) : bool :=
  beq_nat (length l) 1.

Example test_filter2:
    filter length_is_1
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof. reflexivity.  Qed.


(** We can use [filter] to give a concise version of the
    [countoddmembers] function from the [Lists] chapter. *)

Definition countoddmembers' (l:list nat) : nat :=
  length (filter oddb l).

Example test_countoddmembers'1:   countoddmembers' [1;0;3;1;4;5] = 4.
Proof. reflexivity.  Qed.
Example test_countoddmembers'2:   countoddmembers' [0;2;4] = 0.
Proof. reflexivity.  Qed.
Example test_countoddmembers'3:   countoddmembers' nil = 0.
Proof. reflexivity.  Qed.

(* ###################################################### *)
(** ** Anonymous Functions *)

(** It is arguably a little sad, in the example just above, to
    be forced to define the function [length_is_1] and give it a name
    just to be able to pass it as an argument to [filter], since we
    will probably never use it again.  Moreover, this is not an
    isolated example: when using higher-order functions, we often want
    to pass as arguments "one-off" functions that we will never use
    again; having to give each of these functions a name would be
    tedious.

    Fortunately, there is a better way.  We can construct a function
    "on the fly" without declaring it at the top level or giving it a
    name. *)

Example test_anon_fun':
  doit3times (fun n => n * n) 2 = 256.
Proof. reflexivity.  Qed.

(** The expression [(fun n => n * n)] can be read as "the function
    that, given a number [n], yields [n * n]." *)

(** Here is the [filter] example, rewritten to use an anonymous
    function. *)

Example test_filter2':
    filter (fun l => beq_nat (length l) 1)
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof. reflexivity.  Qed.

(** **** Exercise: 2 stars (filter_even_gt7)  *)
(** Use [filter] (instead of [Fixpoint]) to write a Coq function
    [filter_even_gt7] that takes a list of natural numbers as input
    and returns a list of just those that are even and greater than
    7. *)


Definition bgt_nat (n m : nat) : bool := negb (blt_nat n m) && negb (beq_nat n m).

Definition filter_even_gt7 (l : list nat) : list nat :=
  filter (fun x => evenb x && bgt_nat x 7) l.


Example test_filter_even_gt7_1 :
  filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
Proof. reflexivity. Qed.
 
Example test_filter_even_gt7_2 :
  filter_even_gt7 [5;2;6;19;129] = [].
Proof. reflexivity. Qed.


(** **** Exercise: 3 stars (partition)  *)
(** Use [filter] to write a Coq function [partition]:
  partition : forall X : Type,
              (X -> bool) -> list X -> list X * list X
   Given a set [X], a test function of type [X -> bool] and a [list
   X], [partition] should return a pair of lists.  The first member of
   the pair is the sublist of the original list containing the
   elements that satisfy the test, and the second is the sublist
   containing those that fail the test.  The order of elements in the
   two sublists should be the same as their order in the original
   list.
*)

Compute (filter evenb [1;2;3]).

Definition partition {X : Type}
                     (test : X -> bool)
                     (l : list X)
                   : list X * list X :=
  (filter test l, filter (fun x => negb (test x)) l).


Example test_partition1: partition oddb [1;2;3;4;5] = ([1;3;5], [2;4]).
Proof. reflexivity. Qed.
 
Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
Proof. reflexivity. Qed.


(* ###################################################### *)
(** ** Map *)

(** Another handy higher-order function is called [map]. *)

Fixpoint map {X Y:Type} (f:X->Y) (l:list X) : (list Y) :=
  match l with
  | []     => []
  | h :: t => (f h) :: (map f t)
  end.

(** It takes a function [f] and a list [ l = [n1, n2, n3, ...] ]
    and returns the list [ [f n1, f n2, f n3,...] ], where [f] has
    been applied to each element of [l] in turn.  For example: *)

Example test_map1: map (plus 3) [2;0;2] = [5;3;5].
Proof. reflexivity.  Qed.

(** The element types of the input and output lists need not be
    the same, since [map] takes _two_ type arguments, [X] and [Y]; it
    can thus be applied to a list of numbers and a function from
    numbers to booleans to yield a list of booleans: *)

Example test_map2:
  map oddb [2;1;2;5] = [false;true;false;true].
Proof. reflexivity.  Qed.

(** It can even be applied to a list of numbers and
    a function from numbers to _lists_ of booleans to
    yield a _list of lists_ of booleans: *)

Example test_map3:
    map (fun n => [evenb n;oddb n]) [2;1;2;5]
  = [[true;false];[false;true];[true;false];[false;true]].
Proof. reflexivity.  Qed.



(** *** Exercises *)

(** **** Exercise: 3 stars (map_rev)  *)
(** Show that [map] and [rev] commute.  You may need to define an
    auxiliary lemma. *)

Theorem distr_map_app : forall (X Y : Type) (f : X -> Y) (l1 l2 : list X),
  map f (l1 ++ l2) = map f l1 ++ map f l2.                       
Proof.
  intros X Y f l1 l2. induction l1.
    + reflexivity.
    + simpl. rewrite -> IHl1. reflexivity.
Qed.      

Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
  intros X Y f l. induction l.
    + simpl. reflexivity.
    + simpl. rewrite -> distr_map_app. simpl. rewrite -> IHl. reflexivity.
Qed.  


(** **** Exercise: 2 stars, recommended (flat_map)  *)
(** The function [map] maps a [list X] to a [list Y] using a function
    of type [X -> Y].  We can define a similar function, [flat_map],
    which maps a [list X] to a [list Y] using a function [f] of type
    [X -> list Y].  Your definition should work by 'flattening' the
    results of [f], like so:
        flat_map (fun n => [n;n+1;n+2]) [1;5;10]
      = [1; 2; 3; 5; 6; 7; 10; 11; 12].
*)


Fixpoint join {X : Type} (l: list (list X)) : list X :=
  match l with
  |[]    => []
  |x::l' => x ++ join l'
  end.            

Fixpoint flat_map {X Y:Type} (f:X -> list Y) (l:list X)
                   : (list Y) := join (map f l).



Example test_flat_map1:
  flat_map (fun n => [n;n;n]) [1;5;4]
  = [1; 1; 1; 5; 5; 5; 4; 4; 4].
Proof. reflexivity. Qed.
  
(** Lists are not the only inductive type that we can write a
    [map] function for.  Here is the definition of [map] for the
    [option] type: *)

Definition option_map {X Y : Type} (f : X -> Y) (xo : option X)
                      : option Y :=
  match xo with
    | None   => None
    | Some x => Some (f x)
  end.


(** **** Exercise: 2 stars, optional (implicit_args)  *)
(** The definitions and uses of [filter] and [map] use implicit
    arguments in many places.  Replace the curly braces around the
    implicit arguments with parentheses, and then fill in explicit
    type parameters where necessary and use Coq to check that you've
    done so correctly.  (This exercise is not to be turned in; it is
    probably easiest to do it on a _copy_ of this file that you can
    throw away afterwards.)  [] *)

(* ###################################################### *)
(** ** Fold *)

(** An even more powerful higher-order function is called
    [fold].  This function is the inspiration for the "[reduce]"
    operation that lies at the heart of Google's map/reduce
    distributed programming framework. *)

Fixpoint fold {X Y:Type} (f: X->Y->Y) (l:list X) (b:Y)
                         : Y :=
  match l with
  | nil    => b
  | h :: t => f h (fold f t b)
  end.

(** Intuitively, the behavior of the [fold] operation is to
    insert a given binary operator [f] between every pair of elements
    in a given list.  For example, [ fold plus [1;2;3;4] ] intuitively
    means [1+2+3+4].  To make this precise, we also need a "starting
    element" that serves as the initial second input to [f].  So, for
    example,
   fold plus [1;2;3;4] 0
    yields
   1 + (2 + (3 + (4 + 0))).
    Some more examples:
*)

Check (fold andb).
(* ===> fold andb : list bool -> bool -> bool *)

Example fold_example1 :
  fold mult [1;2;3;4] 1 = 24.
Proof. reflexivity. Qed.

Example fold_example2 :
  fold andb [true;true;false;true] true = false.
Proof. reflexivity. Qed.

Example fold_example3 :
  fold app  [[1];[];[2;3];[4]] [] = [1;2;3;4].
Proof. reflexivity. Qed.


(** **** Exercise: 1 star, advanced (fold_types_different)  *)
(** Observe that the type of [fold] is parameterized by _two_ type
    variables, [X] and [Y], and the parameter [f] is a binary operator
    that takes an [X] and a [Y] and returns a [Y].  Can you think of a
    situation where it would be useful for [X] and [Y] to be
    different?

    let [x = nat] and [y = list nat]
    then we can fold over a list to create another list, ie
    [fold (fun x xs => xs ++ [x]) [1;2;3] []]
    reverses the list

 *)


(* ###################################################### *)
(** ** Functions That Construct Functions *)

(** Most of the higher-order functions we have talked about so
    far take functions as arguments.  Let's look at some examples that
    involve _returning_ functions as the results of other functions.
    To begin, here is a function that takes a value [x] (drawn from
    some type [X]) and returns a function from [nat] to [X] that
    yields [x] whenever it is called, ignoring its [nat] argument. *)

Definition constfun {X: Type} (x: X) : nat->X :=
  fun (k:nat) => x.

Definition ftrue := constfun true.

Example constfun_example1 : ftrue 0 = true.
Proof. reflexivity. Qed.

Example constfun_example2 : (constfun 5) 99 = 5.
Proof. reflexivity. Qed.

(** In fact, the multiple-argument functions we have already
    seen are also examples of passing functions as data.  To see why,
    recall the type of [plus]. *)

Check plus.
(* ==> nat -> nat -> nat *)

(** Each [->] in this expression is actually a _binary_ operator
    on types.  This operator is _right-associative_, so the type of
    [plus] is really a shorthand for [nat -> (nat -> nat)] -- i.e., it
    can be read as saying that "[plus] is a one-argument function that
    takes a [nat] and returns a one-argument function that takes
    another [nat] and returns a [nat]."  In the examples above, we
    have always applied [plus] to both of its arguments at once, but
    if we like we can supply just the first.  This is called _partial
    application_. *)

Definition plus3 := plus 3.
Check plus3.

Example test_plus3 :    plus3 4 = 7.
Proof. reflexivity.  Qed.
Example test_plus3' :   doit3times plus3 0 = 9.
Proof. reflexivity.  Qed.
Example test_plus3'' :  doit3times (plus 3) 0 = 9.
Proof. reflexivity.  Qed.

(* ##################################################### *)
(** * Additional Exercises *)

Module Exercises.

(** **** Exercise: 2 stars (fold_length)  *)
(** Many common functions on lists can be implemented in terms of
   [fold].  For example, here is an alternative definition of [length]: *)

Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0.


Example test_fold_length1 : fold_length [4;7;0] = 3.
Proof. reflexivity. Qed.


(** Prove the correctness of [fold_length]. *)
Lemma fold_len_nil : forall (X : Type) (l : list X),
  l = [] -> fold_length l = 0.                       
Proof.
  intros X l H. rewrite -> H.
  unfold fold_length. simpl. reflexivity.
Qed.
  
Lemma fold_len_distr : forall (X : Type) (l1 l2 : list X),
  fold_length (l1 ++ l2) = fold_length l1 + fold_length l2.
Proof.
  intros X l1 l2. induction l1 as [|n l1' IHl1'].
    + simpl. reflexivity.
    + unfold fold_length in *. simpl. rewrite -> IHl1'. reflexivity.
Qed.

Theorem fold_length_correct : forall X (l : list X),
  fold_length l = length l.
Proof.
  intros X l. induction l.
    + reflexivity.
    + simpl. rewrite cons_app_equiv. rewrite -> fold_len_distr.
      simpl. rewrite -> IHl. reflexivity.
Qed.




(** **** Exercise: 3 stars (fold_map)  *)
(** We can also define [map] in terms of [fold].  Finish [fold_map]
    below. *)

(* fold :  forall X Y : Type, (X -> Y -> Y) -> list X -> Y -> Y *)


Definition fold_map {X Y:Type} (f : X -> Y) (l : list X) : list Y :=
  fold (fun x xs => f x :: xs) l [].


(** Write down a theorem [fold_map_correct] in Coq stating that
   [fold_map] is correct, and prove it. *)

Theorem fold_map_correct : forall (X Y : Type) (f : X -> Y) (l : list X),
  fold_map f l = map f l.
Proof.
  intros X Y f l. induction l.
    + reflexivity.
    + unfold fold_map in *. simpl. rewrite <- IHl. reflexivity.
Qed.


(** **** Exercise: 2 stars, advanced (currying)  *)
(** In Coq, a function [f : A -> B -> C] really has the type [A
    -> (B -> C)].  That is, if you give [f] a value of type [A], it
    will give you function [f' : B -> C].  If you then give [f'] a
    value of type [B], it will return a value of type [C].  This
    allows for partial application, as in [plus3].  Processing a list
    of arguments with functions that return functions is called
    _currying_, in honor of the logician Haskell Curry.

    Conversely, we can reinterpret the type [A -> B -> C] as [(A *
    B) -> C].  This is called _uncurrying_.  With an uncurried binary
    function, both arguments must be given at once as a pair; there is
    no partial application. *)

(** We can define currying as follows: *)

Definition prod_curry {X Y Z : Type}
  (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).

(** As an exercise, define its inverse, [prod_uncurry].  Then prove
    the theorems below to show that the two are inverses. *)

Definition prod_uncurry {X Y Z : Type}
  (f : X -> Y -> Z) (p : X * Y) : Z := match p with
    | (x,y) => f x y
    end.             


(** Thought exercise: before running the following commands, can you
    calculate the types of [prod_curry] and [prod_uncurry]? *)

Check @prod_curry.
Check @prod_uncurry.

Theorem uncurry_curry : forall (X Y Z : Type)
                        (f : X -> Y -> Z)
                        x y,
  prod_curry (prod_uncurry f) x y = f x y.
Proof.
  intros X Y Z f x y.
  unfold prod_curry, prod_uncurry. reflexivity.
Qed.  

Theorem curry_uncurry : forall (X Y Z : Type)
                        (f : (X * Y) -> Z) (p : X * Y),
  prod_uncurry (prod_curry f) p = f p.
Proof.
  intros X Y Z f p. destruct p.
  unfold prod_uncurry, prod_curry. reflexivity.
Qed.  
  


(** **** Exercise: 2 stars, advanced (nth_error_informal)  *)
(** Recall the definition of the [nth_error] function:
   Fixpoint nth_error {X : Type} (l : list X) (n : nat) : option X :=
     match l with
     | [] => None
     | a :: l' => if beq_nat n O then Some a else nth_error l' (pred n)
     end.
   Write an informal proof of the following theorem:
   forall X n l, length l = n -> @nth_error X l n
(* FILL IN HERE *)
*)
(** todo: finish exercise above *)
Theorem foo : forall x : Type, x = x.
Proof. Abort.


(** **** Exercise: 4 stars, advanced (church_numerals)  *)
(** This exercise explores an alternative way of defining natural
    numbers, using the so-called _Church numerals_, named after
    mathematician Alonzo Church.  We can represent a natural number
    [n] as a function that takes a function [f] as a parameter and
    returns [f] iterated [n] times. *)

Module Church.


Definition nat := forall X : Type, (X -> X) -> X -> X.


(** Let's see how to write some numbers with this notation. Iterating
    a function once should be the same as just applying it. Thus, *)

Definition one : nat :=
  fun (X : Type) (f : X -> X) (x : X) => f x.

(** Similarly, [two] should apply [f] twice to its argument: *)

Definition two : nat :=
  fun (X : Type) (f : X -> X) (x : X) => f (f x).

(** Defining [zero] is somewhat trickier: how can we "apply a function
    zero times"? The answer is actually simple: just return the
    argument untouched. *)

Definition zero : nat :=
  fun (X : Type) (f : X -> X) (x : X) => x.

(** More generally, a number [n] can be written as [fun X f x => f (f
    ... (f x) ...)], with [n] occurrences of [f].  Notice in
    particular how the [doit3times] function we've defined previously
    is actually just the Church representation of [3]. *)

Definition three : nat := @doit3times.

(** Complete the definitions of the following functions. Make sure
    that the corresponding unit tests pass by proving them with
    [reflexivity]. *)

(** Successor of a natural number: *)

(* n : forall X : Type, (X -> X) -> X -> X *)
Definition succ (n : nat) : nat := fun X f x => f (n X f x).


Example succ_1 : succ zero = one.
Proof. reflexivity. Qed.

  
Example succ_2 : succ one = two.
Proof. reflexivity. Qed.


Example succ_3 : succ two = three.
Proof. reflexivity. Qed.


(** Addition of two natural numbers: *)

Definition plus (n m : nat) : nat := fun X f x => n X f (m X f x).


Example plus_1 : plus zero one = one.
Proof. reflexivity. Qed.

Example plus_2 : plus two three = plus three two.
Proof. reflexivity. Qed.

Example plus_3 :
  plus (plus two two) three = plus one (plus three three).
Proof. reflexivity. Qed.

Example plus_4 : plus one zero = one.
Proof. reflexivity. Qed.


(** Multiplication: *)

Definition mult (n m : nat) : nat := fun X f x => m X (n X f) x.

Example mult_1 : mult one one = one.
Proof. reflexivity. Qed.

(* left annilator *)
Example mult_2 : mult zero (plus three three) = zero.
Proof. reflexivity. Qed.

Example mult_3 : mult two three = plus three three.
Proof. reflexivity. Qed.

Example mult_4 : mult three two = plus three three.
Proof. reflexivity. Qed.

(* right id *)
Example mult_5 : mult three one = three.
Proof. reflexivity. Qed.

(* left id *)
Example mult_6 : mult one three = three.
Proof. reflexivity. Qed.

(* right annilator *)
Example mult_7 : mult (plus three three) zero = zero.
Proof. reflexivity. Qed.


(** Exponentiation: *)

(** (_Hint_: Polymorphism plays a crucial role here.  However,
    choosing the right type to iterate over can be tricky.  If you hit
    a "Universe inconsistency" error, try iterating over a different
    type: [nat] itself is usually problematic.) *)

(* nat := forall X : Type, (X -> X) -> X -> X *)
Definition exp (n m : nat) : nat := fun X f x => m X f (n X f x).


Example exp_4 : exp three one = three.
Proof.
  unfold exp, three, one, doit3times.
  unfold mult. reflexivity.
Qed.

Example exp_5 : exp zero three = zero.
Proof.
  unfold exp, three, zero, one, doit3times, mult. reflexivity.
Qed.

Example exp_3 : exp three zero = one.
Proof.
  unfold exp, three, zero, one.


  
Example exp_2 : exp three two = plus (mult two (mult two two)) one.
Proof.
  unfold exp, three, two, one.
  unfold doit3times, mult, plus.
Abort.


  
Example exp_1 : exp two two = plus two two.
Proof. 
  unfold exp, plus.
  unfold two, mult, one.
  reflexivity.
Abort.




End Church.
(** [] *)

End Exercises.

(** $Date: 2016-01-13 11:14:59 -0500 (Wed, 13 Jan 2016) $ *)
