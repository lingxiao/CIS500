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
    + simpl. rewrite -> app_nil_r. reflexivity.
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

Definition ls := [1;2;3].
Compute (@nth_error nat ls (length ls)).

(** **** Exercise: 2 stars, advanced (nth_error_informal)  *)
(** Recall the definition of the [nth_error] function:

   Fixpoint nth_error {X : Type} (l : list X) (n : nat) : option X :=
     match l with
     | [] => None
     | a :: l' => if beq_nat n O then Some a else nth_error l' (pred n)
     end.
   Write an informal proof of the following theorem:

   forall X n l, length l = n -> @nth_error X l n = None


    We show
          ∀ n X l. length l = n -> nth_error l n = None
    by induction on l.

    + suppose l = []. then our goals is:
          ∀ n X. length [] = n -> nth_error [] n = None,
      and we do induction on n.
       - if we let n = 0 then we have
          ∀ X. length [] = 0 -> nth_error [] 0 = None,
          which is immediately true by def of nth-error.
       - let n = S n' and we have to show:
          ∀ X. length [] = S n' -> nth_error [] (S n') = None.
         but this cannot be true by def of length.

     + suppose l = x:l' and we show:
           ∀ n X. length (x:l') = n -> nth_error (x:l') n = None,
       and our induction hypothesis is:
            [InH] := ∀ n X. length l' = n -> nth_error l' n = None.
       Let's do induction on n.
          - for n = 0 we have
               ∀ X. length (x:l') = 0 -> nth_error (x:l') 0 = None.
             but length (x:l') cannot be 0 and we are done.
          - pick n = S n' so that:
               ∀ X. length (x:l') = S n'.
            or by def of length
               ∀ X. S (length l') = S n'
            which by injectivitiy of successor [S] reduces to:
               ∀ X. length l' = n'.
            So we need to show
               nth_error (x:l') (S n') = None.
            which reduces to:
               [H] := nth_error l' n' = None
            by def of nth_error. And by [InH] the statement above is true if
               length l' = n',
             which is true by [H].

     []
 *)

Theorem nth_error_formal: forall (n : nat) (X : Type) (l : list X),
     length l = n ->
     nth_error l n = None.
Proof.
  intros n X l. generalize dependent n. induction l as [|l'].
    + induction n as [|n'].
        - intros H. reflexivity.
        - intros contra. inversion contra.
    + induction n as [|n'].
        - intros contra. inversion contra.
        - simpl. intros H. apply IHl. apply S_injective in H. apply H.
Qed.






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
Definition succ (n : nat) : nat
  := fun (X : Type) (f : X -> X) (x : X)
  => f (n X f x).


Example succ_1 : succ zero = one.
Proof. reflexivity. Qed.

  
Example succ_2 : succ one = two.
Proof. reflexivity. Qed.


Example succ_3 : succ two = three.
Proof. reflexivity. Qed.


(** Addition of two natural numbers: *)

Definition plus (n m : nat) : nat
  := fun (X : Type) (f : X -> X) (x : X)
  => n X f (m X f x).


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

Definition mult (n m : nat) : nat
  := fun (X : Type) (f : X -> X) (x : X)
  => m X (n X f) x.

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

(* todo: really understand this one, why does it work?? *)
(*

  So we see that:
  exp :: forall X : Type, (X -> X) -> X -> X
  n X :: (X -> X) -> X -> X
  m x :: ((X -> X) -> (X -> X)) -> (X -> X) -> (X -> X)

  but this does not give the correct type signature? which is forall X?
  so we let the X in forall X  to be X -> X ?

*)

Definition m := two.
Definition n := three.
Definition X := Type.

Check (m (X -> X)).
Check (n X).
Check (m (X -> X) (n X)).


Definition exp (n m : nat) : nat
  := fun (X : Type) (f : X -> X) (x : X)
  => (m (X -> X) (n X)) f x.


Example exp_1 : exp two two = plus two two.
Proof. 
  unfold exp, plus.
  unfold two, mult, one.
  reflexivity.
Qed.  

Example exp_2 : exp three two = plus (mult two (mult two two)) one.
Proof.
  unfold exp, three, two, one.
  unfold doit3times, mult, plus.
  reflexivity.
Qed.


Example exp_3 : exp three zero = one.
Proof. 
  unfold exp, three, zero, one. reflexivity.
Qed.

Example exp_4 : exp three one = three.
Proof.
  unfold exp, three, one, doit3times. reflexivity.
Qed.

Example exp_5 : exp zero three = zero.
Proof.
  unfold exp, three, zero, one, doit3times, mult. reflexivity.
Qed.





End Church.
(** [] *)

End Exercises.


