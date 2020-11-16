(** * HoareAsLogic: Hoare Logic as a Logic *)

(** The presentation of Hoare logic in chapter [Hoare] could be
    described as "model-theoretic": the proof rules for each of the
    constructors were presented as _theorems_ about the evaluation
    behavior of programs, and proofs of program correctness (validity
    of Hoare triples) were constructed by combining these theorems
    directly in Coq.

    Another way of presenting Hoare logic is to define a completely
    separate proof system -- a set of axioms and inference rules that
    talk about commands, Hoare triples, etc. -- and then say that a
    proof of a Hoare triple is a valid derivation in _that_ logic.  We
    can do this by giving an inductive definition of _valid
    derivations_ in this new logic.

    This chapter is optional.  Before reading it, you'll want to read
    the [ProofObjects] chapter in _Logical
    Foundations_ (_Software Foundations_, volume 1). *)

From PLF Require Import Maps.
From PLF Require Import Imp.
Hint Constructors ceval : core.
From PLF Require Import Hoare.

(* ################################################################# *)
(** * Hoare Logic and Model Theory *)

(** In [Hoare] we introduced Hoare triples, which contain a
    precondition, command, and postcondition.  For example (and for
    the moment deliberately avoiding the notation we previously
    introduced),

      Pre:  X = 0
      Com:  X ::= X + 1
      Post: X = 1

    is a Hoare triple, as is

      Pre:  X = 0
      Com:  skip
      Post: X = 1

    But there's an important difference between those two triples: the
    former expresses a truth about how Imp programs execute, whereas
    the latter does not.

    To capture that difference, we introduced a definition
    [hoare_triple] that described when a triple expresses such a
    truth.  Let's repeat that definition, but this time we'll call it
    [valid]: *)

Definition valid (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st st',
     st =[ c ]=> st'  ->
     P st  ->
     Q st'.

(** This notion of _validity_ is based on the underlying model of how
    Imp programs execute.  That model itself is based on states.  So,

      Pre:  X = 0
      Com:  X ::= X + 1
      Post: X = 1

    is _valid_, because starting from any state in which [X] is [0],
    and executing [X ::= X + 1], we are guaranteed to reach a state in
    which [X] is [1]. But,

      Pre:  X = 0
      Com:  skip
      Post: X = 1

    is _invalid_, because starting from any state in which [X] is [0],
    we are guaranteed not to change the state, so [X] cannot be [1].
*)

(** So far, we have punned between the syntax of a Hoare triple,
    written [{{P}} c {{Q}}], and its validity, as expressed by
    [valid].  In essence, we have said that the semantic meaning of
    that syntax is the proposition returned by [valid].  This way of
    giving semantic meaning to something syntactic is part of the
    branch of mathematical logic known as _model theory_.  *)

(** Our approach to Hoare logic through model theory led us to
    state proof rules in terms of that same state-based model, and to
    prove program correctness in it, too.  But there is another
    approach, which is arguably more common in Hoare logic. We turn to
    it, next.  *)

(* ################################################################# *)
(** * Hoare Logic and Proof Theory *)

(** Instead of using states and evaluation as the basis for reasoning,
    let's take the proof rules from [Hoare] as the basis.  Those
    proof rules give us a set of axioms and inference rules that
    constitute a logic in their own right.  We repeat them here: *)

(**

             ----------------  (hoare_skip)
             {{P}} skip {{P}}

             ----------------------------- (hoare_asgn)
             {{Q [X |-> a]}} X ::= a {{Q}}

               {{P}} c1 {{Q}}
               {{Q}} c2 {{R}}
              ------------------  (hoare_seq)
              {{P}} c1;; c2 {{R}}

              {{P /\   b}} c1 {{Q}}
              {{P /\ ~ b}} c2 {{Q}}
      ------------------------------------  (hoare_if)
      {{P}} if b then c1 else c2 end {{Q}}

            {{P /\ b}} c {{P}}
      ----------------------------- (hoare_while)
      {{P} while b do c end {{P /\ ~b}}

                {{P'}} c {{Q'}}
                   P ->> P'
                   Q' ->> Q
         -----------------------------   (hoare_consequence)
                {{P}} c {{Q}}
*)

(** Read the Hoare triples in those rules as devoid of any
    meaning other than what the rules give them.  Forget about states
    and evaluations.  They are just syntax that the rules tell us how
    to manipulate in legal ways.

    Through this new lens, triple [{{X = 0}} X ::= X + 1 {{X = 1}}]
    is _derivable_, because we can derive a proof tree using the rules:
*)

(**

                 ---------------------------  (hoare_asgn)
X=0 ->> X+1=1    {{X+1=1}} X ::= X+1 {{X=1}}
----------------------------------------------------------  (hoare_consequence)
                  {{X=0}} X ::= X+1 {{X=1}}
*)

(** At each step we have either used one of the rules, or we
    have appealed to reasoning about assertions, which do not involve
    Hoare triples.  (Note that we have left off the trivial part of
    [hoare_consequence] above, namely X=1 ->> X=1, only because of
    horizontal space contraints: it's hard to fit that many characters
    on a line and have the page still be readable.  If you prefer,
    think of it as using [hoare_consequence_pre] instead.)

    On the other hand, [{{X = 0}} skip {{X = 1}}] is _not_ derivable,
    because there is no way to apply the rules to construct a proof
    tree with this triple at its root. *)

(** This approach gives meaning to triples not in terms of a model,
    but in terms of how they can be used to construct proof trees.
    It's a different way of giving semantic meaning to something
    syntactic, and it's part of the branch of mathematical logic known
    as _proof theory_.

    Our goal for the rest of this chapter is to formalize Hoare logic
    using proof theory, and then to prove that the model-theoretic and
    proof-theoretic formalizations are consistent with one another.
*)

(* ################################################################# *)
(** * Derivability *)

(** To formalize derivability of Hoare triples, we introduce inductive type
    [derivable], which describes legal proof trees using the Hoare rules. *)

Inductive derivable : Assertion -> com -> Assertion -> Type :=
  | H_Skip : forall P,
      derivable P <{skip}> P
  | H_Asgn : forall Q V a,
      derivable (Q [V |-> a]) <{V := a}> Q
  | H_Seq  : forall P c Q d R,
      derivable P c Q -> derivable Q d R -> derivable P <{c;d}> R
  | H_If : forall P Q b c1 c2,
    derivable (fun st => P st /\ bassn b st) c1 Q ->
    derivable (fun st => P st /\ ~(bassn b st)) c2 Q ->
    derivable P <{if b then c1 else c2 end}> Q
  | H_While : forall P b c,
    derivable (fun st => P st /\ bassn b st) c P ->
    derivable P <{while b do c end}> (fun st => P st /\ ~ (bassn b st))
  | H_Consequence  : forall (P Q P' Q' : Assertion) c,
    derivable P' c Q' ->
    (forall st, P st -> P' st) ->
    (forall st, Q' st -> Q st) ->
    derivable P c Q.

(** We don't need to include axioms corresponding to
    [hoare_consequence_pre] or [hoare_consequence_post], because these
    can be proven easily from [H_Consequence]. *)

Lemma H_Consequence_pre : forall (P Q P': Assertion) c,
    derivable P' c Q ->
    (forall st, P st -> P' st) ->
    derivable P c Q.
Proof. eauto using H_Consequence. Qed.

Lemma H_Consequence_post  : forall (P Q Q' : Assertion) c,
    derivable P c Q' ->
    (forall st, Q' st -> Q st) ->
    derivable P c Q.
Proof. eauto using H_Consequence. Qed.

(** As an example, let's construct a proof tree for

        {{(X=3) [X |-> X + 2] [X |-> X + 1]}}
      X ::= X + 1;;
      X ::= X + 2
        {{X=3}}
*)

Example sample_proof :
  derivable
    ((fun st:state => st X = 3) [X |-> X + 2] [X |-> X + 1])
    <{ X := X + 1; X := X + 2}>
    (fun st:state => st X = 3).
Proof.
  eapply H_Seq.
  - apply H_Asgn.
  - apply H_Asgn.
Qed.

(** You can see how the structure of the proof script mirrors the structure
    of the proof tree: at the root there is a use of the sequence rule; and
    at the leaves, the assignment rule. *)

(** **** Exercise: 3 stars, standard (provable_true_post)  *)

(** Show that any Hoare triple whose postcondition is [True] is derivable. Proceed
    by induction on [c]. *)

Theorem provable_true_post : forall c P,
    derivable P c True.
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 3 stars, standard (provable_false_pre)  *)

(** Show that any Hoare triple whose precondition is [False] is derivable. Again,
    proceed by induction on [c]. *)

Theorem provable_false_pre : forall c Q,
    derivable False c Q.
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)


(* ################################################################# *)
(** * Soundness and Completeness *)

(** We now have two approaches to formulating Hoare logic:

    - The model-theoretic approach uses [valid] to characterize when a Hoare
      triple holds in a model, which is based on states.

    - The proof-theoretic approach uses [derivable] to characterize when a Hoare
      triple is derivable as the end of a proof tree.

    Do these two approaches agree?  That is, are the valid Hoare triples exactly
    the derivable ones?  This is a standard question investigated in
    mathematical logic.  There are two pieces to answering it:

    - A logic is _sound_ if everything that is derivable is valid.

    - A logic is _complete_ if everything that is valid is derivable.

    We can prove that Hoare logic is sound and complete.

*)

(** **** Exercise: 3 stars, standard (hoare_sound)  *)

(** Prove that if a Hoare triple is derivable, then it is valid.
    Nearly all the work for this was already done in [Hoare] as
    theorems [hoare_skip], [hoare_asgn], etc.; leverage those
    proofs. Proceed by induction on the derivation of the triple. *)

Theorem hoare_sound : forall P c Q,
  derivable P c Q -> valid P c Q.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** The proof of completeness is more challenging.  To carry out the
    proof, we need to invent some intermediate assertions using a
    technical device known as _weakest preconditions_ (which are also
    discussed in [Hoare2]).  Given a command [c] and a desired
    postcondition assertion [Q], the weakest precondition [wp c Q] is
    an assertion [P] such that [{{P}} c {{Q}}] holds, and moreover,
    for any other assertion [P'], if [{{P'}} c {{Q}}] holds then [P'
    ->> P].

    Another way of stating that idea is that [wp c Q] is the following
    assertion: *)

Definition wp (c:com) (Q:Assertion) : Assertion :=
  fun s => forall s', s =[ c ]=> s' -> Q s'.

Hint Unfold wp : core.

(** The following two theorems show that the two ways of thinking
    about [wp] are the same. *)

Theorem wp_is_precondition : forall c Q,
  {{wp c Q}} c {{Q}}.
Proof. auto. Qed.

Theorem wp_is_weakest : forall c Q P',
    {{P'}} c {{Q}} ->
    P' ->> (wp c Q).
Proof. eauto. Qed.

(** Weakest preconditions are useful because they enable us to
    identify assertions that otherwise would require clever thinking.
    The next two lemmas show that in action. *)

(** **** Exercise: 1 star, standard (wp_seq)  *)

(** What if we have a sequence [c1;; c2], but not an intermediate assertion for
    what should hold in between [c1] and [c2]?  No problem.  Prove that [wp c2 Q]
    suffices as such an assertion. *)

Lemma wp_seq : forall P Q c1 c2,
    derivable P c1 (wp c2 Q) -> derivable (wp c2 Q) c2 Q -> derivable P <{c1; c2}> Q.
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 2 stars, standard (wp_invariant)  *)

(** What if we have a while loop, but not an invariant for it?  No
    problem.  Prove that for any [Q], assertion [wp (while b do c end)
    Q] is a loop invariant of [while b do c end]. *)

Lemma wp_invariant : forall b c Q,
    valid (wp <{while b do c end}> Q /\ b) c (wp <{while b do c end}> Q).
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 4 stars, standard (hoare_complete)  *)

(** Now we are ready to prove the completeness of Hoare logic.  Finish
    the proof of the theorem below.

    Hint: for the [while] case, use the invariant suggested by
    [wp_invariant].

    Acknowledgment: Our approach to this proof is inspired by:

      https://www.ps.uni-saarland.de/courses/sem-ws11/script/Hoare.html
*)

Theorem hoare_complete: forall P c Q,
  valid P c Q -> derivable P c Q.
Proof.
  unfold valid. intros P c. generalize dependent P.
  induction c; intros P Q HT.
  (* FILL IN HERE *) Admitted.

(** [] *)


(* ################################################################# *)
(** * Postscript: Decidability *)

(** We might hope that Hoare logic would be _decidable_; that is, that
    there is an (terminating) algorithm (a _decision procedure_) that
    can determine whether or not a given Hoare triple is valid or
    derivable.  But such a decision procedure cannot exist.

    Consider the triple [{{True}} c {{False}}]. This triple is valid if and
    only if [c] is non-terminating.  So any algorithm that could
    determine validity of arbitrary triples could solve the Halting
    Problem.

    Similarly, the triple [{{True}} skip {{P}}] is valid if and only if
    [forall s, P s] is valid, where [P] is an arbitrary assertion of Coq's
    logic. But it is known that there can be no decision procedure for
    this logic. *)

(* 2020-09-09 21:08 *)
