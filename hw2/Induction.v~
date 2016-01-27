(** * Induction: Proof by Induction *)
 

(** The next line imports all of our definitions from the
    previous chapter. *)

Require Export Basics.

(** For it to work, you need to use [coqc] to compile [Basics.v]
    into [Basics.vo].  This is like making a .class file from a .java
    file, or a .o file from a .c file.
  
    Here are two ways to compile your code:
  
     - In CoqIDE:
   
         Open [Basics.v].
         In the "Compile" menu, click on "Compile Buffer".
   
     - From the command line:
   
         Run [coqc Basics.v]
*)

(* ###################################################################### *)
(** * Proof by Induction *)

(** We proved in the last chapter that [0] is a neutral element
    for [+] on the left using an easy argument based on
    simplification.  The fact that it is also a neutral element on the
    _right_... *)

Theorem plus_0_r_firsttry : forall n:nat,
  n + 0 = n.

(** ... cannot be proved in the same simple way.  Just applying*)

Fixpoint nat_bin (n: nat) : bin := match n with
  | O    => BO
  | S n' => incr_bin (nat_bin n')
  end.

(* we show [bin_nat . nat_bin $ (n + 1) = 1 + (bin_nat . nat_bin $ n)] *)
Lemma bin_to_nat_add_one : forall n : nat,
  bin_nat (nat_bin (S n)) = S (bin_nat (nat_bin n)).
Proof.  
  intros n.
  induction n as [|n' IHn'].
    + simpl. reflexivity.
    + simpl. rewrite -> bin_to_nat_pres_incr. reflexivity.
Qed.
      

Theorem nat_bin_roundtrip : forall n : nat,
  bin_nat (nat_bin n) = n.                               
Proof.
  intros n.
  induction n as [|n' IHn'].
    + simpl. reflexivity.
    + rewrite -> bin_to_nat_add_one.
      rewrite -> IHn'. reflexivity.
Qed.
      

(*

    (b) You might naturally think that we should also prove the
        opposite direction: that starting with a binary number,
        converting to a natural, and then back to binary yields the
        same number we started with.  However, this is not true!
        Explain what the problem is.

        we show there is a  [b : bin] where [nat_bin (bin_nat b) /= b].
 
*)

(* try to see if it is false *)
Theorem bin_nat_roundtrip : forall b : bin,
  nat_bin (bin_nat b) = b.
Proof.
  intros b. induction b.
    + simpl. reflexivity.
    + simpl. 
Abort.  
                              
    
(*

    (c) Define a "direct" normalization function -- i.e., a function
        [normalize] from binary numbers to binary numbers such that,
        for any binary number b, converting to a natural and then back
        to binary yields [(normalize b)].  Prove it.  (Warning: This
        part is tricky!)

    Again, feel free to change your earlier definitions if this helps
    here. 
*)

Fixpoint direct (b: bin) : bin := admit.

(* FILL IN HERE *)
(** [] *)

(* ###################################################################### *)
(** * Formal vs. Informal Proof (Optional) *)

(** "Informal proofs are algorithms; formal proofs are code." *)

(** The question of what constitutes a proof of a mathematical
    claim has challenged philosophers for millennia, but a rough and
    ready definition could be this: A proof of a mathematical
    proposition [P] is a written (or spoken) text that instills in the
    reader or hearer the certainty that [P] is true.  That is, a proof
    is an act of communication.

    Acts of communication may involve different sorts of readers.  On
    one hand, the "reader" can be a program like Coq, in which case
    the "belief" that is instilled is that [P] can be mechanically
    derived from a certain set of formal logical rules, and the proof
    is a recipe that guides the program in checking this fact.  Such
    recipes are _formal_ proofs.

    Alternatively, the reader can be a human being, in which case the
    proof will be written in English or some other natural language,
    and will thus necessarily be _informal_.  Here, the criteria for
    success are less clearly specified.  A "valid" proof is one that
    makes the reader believe [P].  But the same proof may be read by
    many different readers, some of whom may be convinced by a
    particular way of phrasing the argument, while others may not be.
    Some readers may be particularly pedantic, inexperienced, or just
    plain thick-headed; the only way to convince them will be to make
    the argument in painstaking detail.  But other readers, more
    familiar in the area, may find all this detail so overwhelming
    that they lose the overall thread; all they want is to be told the
    main ideas, since it is easier for them to fill in the details for
    themselves than to wade through a written presentation of them.
    Ultimately, there is no universal standard, because there is no
    single way of writing an informal proof that is guaranteed to
    convince every conceivable reader.  

    In practice, however, mathematicians have developed a rich set of
    conventions and idioms for writing about complex mathematical
    objects that -- at least within a certain community -- make
    communication fairly reliable.  The conventions of this stylized
    form of communication give a fairly clear standard for judging
    proofs good or bad.

    Because we are using Coq in this course, we will be working
    heavily with formal proofs.  But this doesn't mean we can
    completely forget about informal ones!  Formal proofs are useful
    in many ways, but they are _not_ very efficient ways of
    communicating ideas between human beings. *)

(** For example, here is a proof that addition is associative: *)

Theorem plus_assoc' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof. intros n m p. induction n as [| n' IHn']. reflexivity.
  simpl. rewrite -> IHn'. reflexivity.  Qed.

(** Coq is perfectly happy with this.  For a human, however, it
    is difficult to make much sense of it.  We can use comments and
    bullets to show the structure a little more clearly... *)

Theorem plus_assoc'' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n' IHn'].
  - (* n = 0 *)
    reflexivity.
  - (* n = S n' *)
    simpl. rewrite -> IHn'. reflexivity.
Qed.

(** ... and if you're used to Coq you may be able to step
    through the tactics one after the other in your mind and imagine
    the state of the context and goal stack at each point, but if the
    proof were even a little bit more complicated this would be next
    to impossible.

    A (pedantic) mathematician might write the proof something like
    this: *)
(** - _Theorem_: For any [n], [m] and [p],
      n + (m + p) = (n + m) + p.
    _Proof_: By induction on [n].

    - First, suppose [n = 0].  We must show 
        0 + (m + p) = (0 + m) + p.  
      This follows directly from the definition of [+].

    - Next, suppose [n = S n'], where
        n' + (m + p) = (n' + m) + p.
      We must show
        (S n') + (m + p) = ((S n') + m) + p.
      By the definition of [+], this follows from
        S (n' + (m + p)) = S ((n' + m) + p),
      which is immediate from the induction hypothesis.  _Qed_. *)

(** The overall form of the proof is basically similar, and of
    course this is no accident: Coq has been designed so that its
    [induction] tactic generates the same sub-goals, in the same
    order, as the bullet points that a mathematician would write.  But
    there are significant differences of detail: the formal proof is
    much more explicit in some ways (e.g., the use of [reflexivity])
    but much less explicit in others (in particular, the "proof state"
    at any given point in the Coq proof is completely implicit,
    whereas the informal proof reminds the reader several times where
    things stand). *)

(** **** Exercise: 2 stars, advanced, recommended (plus_comm_informal)  *)
(** Translate your solution for [plus_comm] into an informal proof. *)

(** Theorem: Addition is commutative.
 
    we show that [forall m n : nat, n + m = m + n].

    _Proof_ : By induction on [n].

    - first let [n = 0] so we must show
              [0 + m = m + 0]
      but this follows directly from the def of [+].

    - Now let [n = S n'] and our induction hypothesis is that
              [n' + m = m + n'].
      so we must show
              [S n' + m = m + S n']
      by def of [+] we have
              [S (n' + m) = m + S n']
      by induction hypothesis we have
              [S (m + n') = m + S n']
      they are equal by [plus_n_Sm].

      Qed.

*)

(** **** Exercise: 2 stars, optional (beq_nat_refl_informal)  *)
(** Write an informal proof of the following theorem, using the
    informal proof of [plus_assoc] as a model.  Don't just
    paraphrase the Coq tactics into English!
 
    Theorem: [true = beq_nat n n] for any [n].
    
    Proof: By induction on [n].

    let [n = 0] and we have [true = beq_nat 0 0], this follows from def of [beq_nat].
    now let [n = S n'] and our induction hypo is:
            [true = beq_nat n' n'],
    and our goal is:
            [true = beq_nat (S n') (S n')].
    By def of [beq_nat] we are evaluating the branch:
    [S n'] and our [m] is matched with [S n'].
    Thus the inductive step reduces to [beq_nat n' n'].
    This is true by the inductive hypothesis.

    Qed.


[] *)

(** $Date: 2016-01-13 12:02:23 -0500 (Wed, 13 Jan 2016) $ *)