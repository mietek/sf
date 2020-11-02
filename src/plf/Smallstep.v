(** * Smallstep: Small-step Operational Semantics *)

Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Init.Nat.
From Coq Require Import Lia.
From Coq Require Import Lists.List.
Import ListNotations.
From PLF Require Import Maps.
From PLF Require Import Imp.

(** The evaluators we have seen so far (for [aexp]s, [bexp]s,
    commands, ...) have been formulated in a "big-step" style: they
    specify how a given expression can be evaluated to its final
    value (or a command plus a store to a final store) "all in one big
    step."

    This style is simple and natural for many purposes -- indeed,
    Gilles Kahn, who popularized it, called it _natural semantics_.
    But there are some things it does not do well.  In particular, it
    does not give us a natural way of talking about _concurrent_
    programming languages, where the semantics of a program -- i.e.,
    the essence of how it behaves -- is not just which input states
    get mapped to which output states, but also includes the
    intermediate states that it passes through along the way, since
    these states can also be observed by concurrently executing code.

    Another shortcoming of the big-step style is more technical, but
    critical in many situations.  Suppose we want to define a variant
    of Imp where variables could hold _either_ numbers _or_ lists of
    numbers.  In the syntax of this extended language, it will be
    possible to write strange expressions like [2 + nil], and our
    semantics for arithmetic expressions will then need to say
    something about how such expressions behave.  One possibility is
    to maintain the convention that every arithmetic expression
    evaluates to some number by choosing some way of viewing a list as
    a number -- e.g., by specifying that a list should be interpreted
    as [0] when it occurs in a context expecting a number.  But this
    is really a bit of a hack.

    A much more natural approach is simply to say that the behavior of
    an expression like [2+nil] is _undefined_ -- i.e., it doesn't
    evaluate to any result at all.  And we can easily do this: we just
    have to formulate [aeval] and [beval] as [Inductive] propositions
    rather than [Fixpoint]s, so that we can make them partial functions
    instead of total ones.

    Now, however, we encounter a serious deficiency.  In this
    language, a command might fail to map a given starting state to
    any ending state for _two quite different reasons_: either because
    the execution gets into an infinite loop or because, at some
    point, the program tries to do an operation that makes no sense,
    such as adding a number to a list, so that none of the evaluation
    rules can be applied.

    These two outcomes -- nontermination vs. getting stuck in an
    erroneous configuration -- should not be confused.  In particular, we
    want to _allow_ the first (permitting the possibility of infinite
    loops is the price we pay for the convenience of programming with
    general looping constructs like [while]) but _prevent_ the
    second (which is just wrong), for example by adding some form of
    _typechecking_ to the language.  Indeed, this will be a major
    topic for the rest of the course.  As a first step, we need a way
    of presenting the semantics that allows us to distinguish
    nontermination from erroneous "stuck states."

    So, for lots of reasons, we'd often like to have a finer-grained
    way of defining and reasoning about program behaviors.  This is
    the topic of the present chapter.  Our goal is to replace the
    "big-step" [eval] relation with a "small-step" relation that
    specifies, for a given program, how the "atomic steps" of
    computation are performed. *)

(* ################################################################# *)
(** * A Toy Language *)

(** To save space in the discussion, let's go back to an
    incredibly simple language containing just constants and
    addition.  (We use single letters -- [C] and [P] (for Constant and
    Plus) -- as constructor names, for brevity.)  At the end of the
    chapter, we'll see how to apply the same techniques to the full
    Imp language.  *)

Inductive tm : Type :=
  | C : nat -> tm         (* Constant *)
  | P : tm -> tm -> tm.   (* Plus *)

(** Here is a standard evaluator for this language, written in
    the big-step style that we've been using up to this point. *)

Fixpoint evalF (t : tm) : nat :=
  match t with
  | C n => n
  | P t1 t2 => evalF t1 + evalF t2
  end.

(** Here is the same evaluator, written in exactly the same
    style, but formulated as an inductively defined relation.
    We use the notation [t ==> n] for "[t] evaluates to [n]."

                               ---------                               (E_Const)
                               C n ==> n

                               t1 ==> n1
                               t2 ==> n2
                           -------------------                         (E_Plus)
                           P t1 t2 ==> n1 + n2
*)

Reserved Notation " t '==>' n " (at level 50, left associativity).

Inductive eval : tm -> nat -> Prop :=
  | E_Const : forall n,
      C n ==> n
  | E_Plus : forall t1 t2 n1 n2,
      t1 ==> n1 ->
      t2 ==> n2 ->
      P t1 t2 ==> (n1 + n2)

where " t '==>' n " := (eval t n).

Module SimpleArith1.

(** Now, here is the corresponding _small-step_ evaluation relation.

    
                     -------------------------------        (ST_PlusConstConst)
                     P (C n1) (C n2) --> C (n1 + n2)

                              t1 --> t1'
                         --------------------                        (ST_Plus1)
                         P t1 t2 --> P t1' t2

                              t2 --> t2'
                      ----------------------------                   (ST_Plus2)
                      P (C n1) t2 --> P (C n1) t2'
*)

Reserved Notation " t '-->' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
      P (C n1) (C n2) --> C (n1 + n2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 --> t1' ->
      P t1 t2 --> P t1' t2
  | ST_Plus2 : forall n1 t2 t2',
      t2 --> t2' ->
      P (C n1) t2 --> P (C n1) t2'

  where " t '-->' t' " := (step t t').

(** Things to notice:

    - We are defining just a single reduction step, in which
      one [P] node is replaced by its value.

    - Each step finds the _leftmost_ [P] node that is ready to
      go (both of its operands are constants) and rewrites it in
      place.  The first rule tells how to rewrite this [P] node
      itself; the other two rules tell how to find it.

    - A term that is just a constant cannot take a step. *)

(** Let's pause and check a couple of examples of reasoning with
    the [step] relation... *)

(** If [t1] can take a step to [t1'], then [P t1 t2] steps
    to [P t1' t2]: *)

Example test_step_1 :
      P
        (P (C 1) (C 3))
        (P (C 2) (C 4))
      -->
      P
        (C 4)
        (P (C 2) (C 4)).
Proof.
  apply ST_Plus1. apply ST_PlusConstConst.  Qed.

(** **** Exercise: 1 star, standard (test_step_2) 

    Right-hand sides of sums can take a step only when the
    left-hand side is finished: if [t2] can take a step to [t2'],
    then [P (C n) t2] steps to [P (C n) t2']: *)

Example test_step_2 :
      P
        (C 0)
        (P
          (C 2)
          (P (C 1) (C 3)))
      -->
      P
        (C 0)
        (P
          (C 2)
          (C 4)).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

End SimpleArith1.

(* ################################################################# *)
(** * Relations *)

(** We will be working with several different single-step relations,
    so it is helpful to generalize a bit and state a few definitions
    and theorems about relations in general.  (The optional chapter
    [Rel.v] develops some of these ideas in a bit more detail; it may
    be useful if the treatment here is too dense.)

    A _binary relation_ on a set [X] is a family of propositions
    parameterized by two elements of [X] -- i.e., a proposition about
    pairs of elements of [X].  *)

Definition relation (X : Type) := X -> X -> Prop.

(** Our main examples of such relations in this chapter will be
    the single-step reduction relation, [-->], and its multi-step
    variant, [-->*] (defined below), but there are many other
    examples -- e.g., the "equals," "less than," "less than or equal
    to," and "is the square of" relations on numbers, and the "prefix
    of" relation on lists and strings. *)

(** One simple property of the [-->] relation is that, like the
    big-step evaluation relation for Imp, it is _deterministic_.

    _Theorem_: For each [t], there is at most one [t'] such that [t]
    steps to [t'] ([t --> t'] is provable). *)

(** _Proof sketch_: We show that if [x] steps to both [y1] and
    [y2], then [y1] and [y2] are equal, by induction on a derivation
    of [step x y1].  There are several cases to consider, depending on
    the last rule used in this derivation and the last rule in the
    given derivation of [step x y2].

      - If both are [ST_PlusConstConst], the result is immediate.

      - The cases when both derivations end with [ST_Plus1] or
        [ST_Plus2] follow by the induction hypothesis.

      - It cannot happen that one is [ST_PlusConstConst] and the other
        is [ST_Plus1] or [ST_Plus2], since this would imply that [x]
        has the form [P t1 t2] where both [t1] and [t2] are
        constants (by [ST_PlusConstConst]) _and_ one of [t1] or [t2]
        has the form [P _].

      - Similarly, it cannot happen that one is [ST_Plus1] and the
        other is [ST_Plus2], since this would imply that [x] has the
        form [P t1 t2] where [t1] has both the form [P t11 t12] and the
        form [C n]. [] *)

(** Formally: *)

Definition deterministic {X : Type} (R : relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

Module SimpleArith2.
Import SimpleArith1.

Theorem step_deterministic:
  deterministic step.
Proof.
  unfold deterministic. intros x y1 y2 Hy1 Hy2.
  generalize dependent y2.
  induction Hy1; intros y2 Hy2.
  - (* ST_PlusConstConst *) inversion Hy2; subst.
    + (* ST_PlusConstConst *) reflexivity.
    + (* ST_Plus1 *) inversion H2.
    + (* ST_Plus2 *) inversion H2.
  - (* ST_Plus1 *) inversion Hy2; subst.
    + (* ST_PlusConstConst *)
      inversion Hy1.
    + (* ST_Plus1 *)
      rewrite <- (IHHy1 t1'0).
      reflexivity. assumption.
    + (* ST_Plus2 *)
      inversion Hy1.
  - (* ST_Plus2 *) inversion Hy2; subst.
    + (* ST_PlusConstConst *)
      inversion Hy1.
    + (* ST_Plus1 *) inversion H2.
    + (* ST_Plus2 *)
      rewrite <- (IHHy1 t2'0).
      reflexivity. assumption.
Qed.

End SimpleArith2.

(** There is some annoying repetition in this proof.  Each use of
    [inversion Hy2] results in three subcases, only one of which is
    relevant (the one that matches the current case in the induction
    on [Hy1]).  The other two subcases need to be dismissed by finding
    the contradiction among the hypotheses and doing inversion on it.

    The following custom tactic, called [solve_by_inverts], can be
    helpful in such cases.  It will solve the goal if it can be solved
    by inverting some hypothesis; otherwise, it fails. *)

Ltac solve_by_inverts n :=
  match goal with | H : ?T |- _ =>
  match type of T with Prop =>
    solve [
      inversion H;
      match n with S (S (?n')) => subst; solve_by_inverts (S n') end ]
  end end.

(** The details of how this works are not important for now, but it
    illustrates the power of Coq's [Ltac] language for
    programmatically defining special-purpose tactics.  It looks
    through the current proof state for a hypothesis [H] (the first
    [match]) of type [Prop] (the second [match]) such that performing
    inversion on [H] (followed by a recursive invocation of the same
    tactic, if its argument [n] is greater than one) completely solves
    the current goal.  If no such hypothesis exists, it fails.

    We will usually want to call [solve_by_inverts] with argument
    [1] (especially as larger arguments can lead to very slow proof
    checking), so we define [solve_by_invert] as a shorthand for this
    case. *)

Ltac solve_by_invert :=
  solve_by_inverts 1.

(** The proof of the previous theorem can now be simplified... *)

Module SimpleArith3.
Import SimpleArith1.

Theorem step_deterministic_alt: deterministic step.
Proof.
  intros x y1 y2 Hy1 Hy2.
  generalize dependent y2.
  induction Hy1; intros y2 Hy2;
    inversion Hy2; subst; try solve_by_invert.
  - (* ST_PlusConstConst *) reflexivity.
  - (* ST_Plus1 *)
    apply IHHy1 in H2. rewrite H2. reflexivity.
  - (* ST_Plus2 *)
    apply IHHy1 in H2. rewrite H2. reflexivity.
Qed.

End SimpleArith3.

(* ================================================================= *)
(** ** Values *)

(** Next, it will be useful to slightly reformulate the
    definition of single-step reduction by stating it in terms of
    "values." *)

(** It can be useful to think of the [-->] relation as defining an
    _abstract machine_:

      - At any moment, the _state_ of the machine is a term.

      - A _step_ of the machine is an atomic unit of computation --
        here, a single "add" operation.

      - The _halting states_ of the machine are ones where there is no
        more computation to be done. *)

(** We can then execute a term [t] as follows:

      - Take [t] as the starting state of the machine.

      - Repeatedly use the [-->] relation to find a sequence of
        machine states, starting with [t], where each state steps to
        the next.

      - When no more reduction is possible, "read out" the final state
        of the machine as the result of execution. *)

(** Intuitively, it is clear that the final states of the
    machine are always terms of the form [C n] for some [n].
    We call such terms _values_. *)

Inductive value : tm -> Prop :=
  | v_const : forall n, value (C n).

(** Having introduced the idea of values, we can use it in the
    definition of the [-->] relation to write [ST_Plus2] rule in a
    slightly more elegant way: *)

(** 
                     -------------------------------        (ST_PlusConstConst)
                     P (C n1) (C n2) --> C (n1 + n2)

                              t1 --> t1'
                         --------------------                        (ST_Plus1)
                         P t1 t2 --> P t1' t2

                               value v1
                              t2 --> t2'
                         --------------------                        (ST_Plus2)
                         P v1 t2 --> P v1 t2'
*)
(** Again, the variable names here carry important information:
    by convention, [v1] ranges only over values, while [t1] and [t2]
    range over arbitrary terms.  (Given this convention, the explicit
    [value] hypothesis is arguably redundant, since the naming
    convention tells us where to add it when translating the informal
    rule to Coq.  We'll keep it for now, to maintain a close
    correspondence between the informal and Coq versions of the rules,
    but later on we'll drop it in informal rules for brevity.) *)

(**  Here are the formal rules: *)

Reserved Notation " t '-->' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
          P (C n1) (C n2)
      --> C (n1 + n2)
  | ST_Plus1 : forall t1 t1' t2,
        t1 --> t1' ->
        P t1 t2 --> P t1' t2
  | ST_Plus2 : forall v1 t2 t2',
        value v1 ->                     (* <--- n.b. *)
        t2 --> t2' ->
        P v1 t2 --> P v1 t2'

  where " t '-->' t' " := (step t t').

(** **** Exercise: 3 stars, standard, especially useful (redo_determinism) 

    As a sanity check on this change, let's re-verify determinism.
    Here's an informal proof:

    _Proof sketch_: We must show that if [x] steps to both [y1] and
    [y2], then [y1] and [y2] are equal.  Consider the final rules used
    in the derivations of [step x y1] and [step x y2].

    - If both are [ST_PlusConstConst], the result is immediate.

    - It cannot happen that one is [ST_PlusConstConst] and the other
      is [ST_Plus1] or [ST_Plus2], since this would imply that [x] has
      the form [P t1 t2] where both [t1] and [t2] are constants (by
      [ST_PlusConstConst]) _and_ one of [t1] or [t2] has the form [P
      _].

    - Similarly, it cannot happen that one is [ST_Plus1] and the other
      is [ST_Plus2], since this would imply that [x] has the form [P
      t1 t2] where [t1] both has the form [P t11 t12] and is a
      value (hence has the form [C n]).

    - The cases when both derivations end with [ST_Plus1] or
      [ST_Plus2] follow by the induction hypothesis. [] *)

(** Most of this proof is the same as the one above.  But to get
    maximum benefit from the exercise you should try to write your
    formal version from scratch and just use the earlier one if you
    get stuck. *)

Theorem step_deterministic :
  deterministic step.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** Strong Progress and Normal Forms *)

(** The definition of single-step reduction for our toy language
    is fairly simple, but for a larger language it would be easy to
    forget one of the rules and accidentally create a situation where
    some term cannot take a step even though it has not been
    completely reduced to a value.  The following theorem shows that
    we did not, in fact, make such a mistake here. *)

(** _Theorem_ (_Strong Progress_): If [t] is a term, then either [t]
    is a value or else there exists a term [t'] such that [t --> t']. *)

(** _Proof_: By induction on [t].

    - Suppose [t = C n]. Then [t] is a value.

    - Suppose [t = P t1 t2], where (by the IH) [t1] either is a value
      or can step to some [t1'], and where [t2] is either a value or
      can step to some [t2']. We must show [P t1 t2] is either a value
      or steps to some [t'].

      - If [t1] and [t2] are both values, then [t] can take a step, by
        [ST_PlusConstConst].

      - If [t1] is a value and [t2] can take a step, then so can [t],
        by [ST_Plus2].

      - If [t1] can take a step, then so can [t], by [ST_Plus1].  []

   Or, formally: *)

Theorem strong_progress : forall t,
  value t \/ (exists t', t --> t').
Proof.
  induction t.
  - (* C *) left. apply v_const.
  - (* P *) right. destruct IHt1 as [IHt1 | [t1' Ht1] ].
    + (* l *) destruct IHt2 as [IHt2 | [t2' Ht2] ].
      * (* l *) inversion IHt1. inversion IHt2.
        exists (C (n + n0)).
        apply ST_PlusConstConst.
      * (* r *)
        exists (P t1 t2').
        apply ST_Plus2. apply IHt1. apply Ht2.
    + (* r *)
      exists (P t1' t2).
      apply ST_Plus1. apply Ht1.
Qed.

(** This important property is called _strong progress_, because
    every term either is a value or can "make progress" by stepping to
    some other term.  (The qualifier "strong" distinguishes it from a
    more refined version that we'll see in later chapters, called
    just _progress_.) *)

(** The idea of "making progress" can be extended to tell us something
    interesting about values: they are exactly the terms that _cannot_
    make progress in this sense.

    To state this observation formally, let's begin by giving a name
    to "terms that cannot make progress."  We'll call them _normal
    forms_.  *)

Definition normal_form {X : Type}
              (R : relation X) (t : X) : Prop :=
  ~ exists t', R t t'.

(** Note that this definition specifies what it is to be a normal form
    for an _arbitrary_ relation [R] over an arbitrary set [X], not
    just for the particular single-step reduction relation over terms
    that we are interested in at the moment.  We'll re-use the same
    terminology for talking about other relations later in the
    course. *)

(** We can use this terminology to generalize the observation we made
    in the strong progress theorem: in this language, normal forms and
    values are actually the same thing. *)

Lemma value_is_nf : forall v,
  value v -> normal_form step v.
Proof.
  unfold normal_form. intros v H. destruct H.
  intros contra. destruct contra. inversion H.
Qed.

Lemma nf_is_value : forall t,
  normal_form step t -> value t.
Proof. (* a corollary of [strong_progress]... *)
  unfold normal_form. intros t H.
  assert (G : value t \/ exists t', t --> t').
  { apply strong_progress. }
  destruct G as [G | G].
  - (* l *) apply G.
  - (* r *) exfalso. apply H. assumption.
Qed.

Corollary nf_same_as_value : forall t,
  normal_form step t <-> value t.
Proof.
  split. apply nf_is_value. apply value_is_nf.
Qed.

(** Why is this interesting?

    Because [value] is a syntactic concept -- it is defined by looking
    at the way a term is written -- while [normal_form] is a semantic
    one -- it is defined by looking at how the term steps.

    It is not obvious that these concepts should define the same set
    of terms!  *)

(** Indeed, we could easily have written the definitions (incorrectly)
    so that they would _not_ coincide. *)

(** **** Exercise: 3 stars, standard, optional (value_not_same_as_normal_form1) 

    We might, for example, define [value] so that it
    includes some terms that are not finished reducing.

    (Even if you don't work this exercise and the following ones
    in Coq, make sure you can think of an example of such a term.) *)

Module Temp1.

Inductive value : tm -> Prop :=
  | v_const : forall n, value (C n)
  | v_funny : forall t1 n2,
                value (P t1 (C n2)).              (* <--- *)

Reserved Notation " t '-->' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
      P (C n1) (C n2) --> C (n1 + n2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 --> t1' ->
      P t1 t2 --> P t1' t2
  | ST_Plus2 : forall v1 t2 t2',
      value v1 ->
      t2 --> t2' ->
      P v1 t2 --> P v1 t2'

  where " t '-->' t' " := (step t t').

Lemma value_not_same_as_normal_form :
  exists v, value v /\ ~ normal_form step v.
Proof.
  (* FILL IN HERE *) Admitted.
End Temp1.

(** [] *)

(** **** Exercise: 2 stars, standard, optional (value_not_same_as_normal_form2) 

    Or we might (again, wrongly) define [step] so that it permits
    something designated as a value to reduce further. *)

Module Temp2.

Inductive value : tm -> Prop :=
  | v_const : forall n, value (C n).         (* Original definition *)

Reserved Notation " t '-->' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_Funny : forall n,
      C n --> P (C n) (C 0)                  (* <--- NEW *)
  | ST_PlusConstConst : forall n1 n2,
      P (C n1) (C n2) --> C (n1 + n2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 --> t1' ->
      P t1 t2 --> P t1' t2
  | ST_Plus2 : forall v1 t2 t2',
      value v1 ->
      t2 --> t2' ->
      P v1 t2 --> P v1 t2'

  where " t '-->' t' " := (step t t').

Lemma value_not_same_as_normal_form :
  exists v, value v /\ ~ normal_form step v.
Proof.
  (* FILL IN HERE *) Admitted.

End Temp2.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (value_not_same_as_normal_form3) 

    Finally, we might define [value] and [step] so that there is some
    term that is not a value but that cannot take a step in the [step]
    relation.  Such terms are said to be _stuck_. In this case this is
    caused by a mistake in the semantics, but we will also see
    situations where, even in a correct language definition, it makes
    sense to allow some terms to be stuck. *)

Module Temp3.

Inductive value : tm -> Prop :=
  | v_const : forall n, value (C n).

Reserved Notation " t '-->' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
      P (C n1) (C n2) --> C (n1 + n2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 --> t1' ->
      P t1 t2 --> P t1' t2

  where " t '-->' t' " := (step t t').

(** (Note that [ST_Plus2] is missing.) *)

Lemma value_not_same_as_normal_form :
  exists t, ~ value t /\ normal_form step t.
Proof.
  (* FILL IN HERE *) Admitted.

End Temp3.
(** [] *)

(* ----------------------------------------------------------------- *)
(** *** Additional Exercises *)

Module Temp4.

(** Here is another very simple language whose terms, instead of being
    just addition expressions and numbers, are just the booleans true
    and false and a conditional expression... *)

Inductive tm : Type :=
  | tru : tm
  | fls : tm
  | test : tm -> tm -> tm -> tm.

Inductive value : tm -> Prop :=
  | v_tru : value tru
  | v_fls : value fls.

Reserved Notation " t '-->' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_IfTrue : forall t1 t2,
      test tru t1 t2 --> t1
  | ST_IfFalse : forall t1 t2,
      test fls t1 t2 --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      test t1 t2 t3 --> test t1' t2 t3

  where " t '-->' t' " := (step t t').

(** **** Exercise: 1 star, standard (smallstep_bools) 

    Which of the following propositions are provable?  (This is just a
    thought exercise, but for an extra challenge feel free to prove
    your answers in Coq.) *)

Definition bool_step_prop1 :=
  fls --> fls.

(* FILL IN HERE *)

Definition bool_step_prop2 :=
     test
       tru
       (test tru tru tru)
       (test fls fls fls)
  -->
     tru.

(* FILL IN HERE *)

Definition bool_step_prop3 :=
     test
       (test tru tru tru)
       (test tru tru tru)
       fls
   -->
     test
       tru
       (test tru tru tru)
       fls.

(* FILL IN HERE *)

(* Do not modify the following line: *)
Definition manual_grade_for_smallstep_bools : option (nat*string) := None.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (progress_bool) 

    Just as we proved a progress theorem for plus expressions, we can
    do so for boolean expressions, as well. *)

Theorem strong_progress : forall t,
  value t \/ (exists t', t --> t').
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (step_deterministic)  *)
Theorem step_deterministic :
  deterministic step.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

Module Temp5.

(** **** Exercise: 2 stars, standard (smallstep_bool_shortcut) 

    Suppose we want to add a "short circuit" to the step relation for
    boolean expressions, so that it can recognize when the [then] and
    [else] branches of a conditional are the same value (either
    [tru] or [fls]) and reduce the whole conditional to this
    value in a single step, even if the guard has not yet been reduced
    to a value. For example, we would like this proposition to be
    provable:

         test
            (test tru tru tru)
            fls
            fls
     -->
         fls.
*)

(** Write an extra clause for the step relation that achieves this
    effect and prove [bool_step_prop4]. *)

Reserved Notation " t '-->' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_IfTrue : forall t1 t2,
      test tru t1 t2 --> t1
  | ST_IfFalse : forall t1 t2,
      test fls t1 t2 --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      test t1 t2 t3 --> test t1' t2 t3
  (* FILL IN HERE *)

  where " t '-->' t' " := (step t t').

Definition bool_step_prop4 :=
         test
            (test tru tru tru)
            fls
            fls
     -->
         fls.

Example bool_step_prop4_holds :
  bool_step_prop4.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (properties_of_altered_step) 

    It can be shown that the determinism and strong progress theorems
    for the step relation in the lecture notes also hold for the
    definition of step given above.  After we add the clause
    [ST_ShortCircuit]...

    - Is the [step] relation still deterministic?  Write yes or no and
      briefly (1 sentence) explain your answer.

      Optional: prove your answer correct in Coq. *)

(* FILL IN HERE
   - Does a strong progress theorem hold? Write yes or no and
     briefly (1 sentence) explain your answer.

     Optional: prove your answer correct in Coq.
*)

(* FILL IN HERE
   - In general, is there any way we could cause strong progress to
     fail if we took away one or more constructors from the original
     step relation? Write yes or no and briefly (1 sentence) explain
     your answer.

(* FILL IN HERE *)
*)
(** [] *)

End Temp5.
End Temp4.

(* ################################################################# *)
(** * Multi-Step Reduction *)

(** We've been working so far with the _single-step reduction_
    relation [-->], which formalizes the individual steps of an
    abstract machine for executing programs.

    We can use the same machine to reduce programs to completion -- to
    find out what final result they yield.  This can be formalized as
    follows:

    - First, we define a _multi-step reduction relation_ [-->*], which
      relates terms [t] and [t'] if [t] can reach [t'] by any number
      (including zero) of single reduction steps.

    - Then we define a "result" of a term [t] as a normal form that
      [t] can reach by multi-step reduction. *)

(** Since we'll want to reuse the idea of multi-step reduction many
    times, let's pause and define it generically.

    Given a relation [R] (which will be [-->] for present purposes),
    we define a relation [multi R], called the _multi-step closure of
    [R]_ as follows. *)

Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.

(** (In the [Rel] chapter of _Logical Foundations_ and
    the Coq standard library, this relation is called
    [clos_refl_trans_1n].  We give it a shorter name here for the sake
    of readability.) *)

(** The effect of this definition is that [multi R] relates two
    elements [x] and [y] if

       - [x = y], or
       - [R x y], or
       - there is some nonempty sequence [z1], [z2], ..., [zn] such that

           R x z1
           R z1 z2
           ...
           R zn y.

    Thus, if [R] describes a single-step of computation, then [z1] ... [zn]
    is the sequence of intermediate steps of computation between [x] and
    [y]. *)

(** We write [-->*] for the [multi step] relation on terms. *)

Notation " t '-->*' t' " := (multi step t t') (at level 40).

(** The relation [multi R] has several crucial properties.

    First, it is obviously _reflexive_ (that is, [forall x, multi R x
    x]).  In the case of the [-->*] (i.e., [multi step]) relation, the
    intuition is that a term can execute to itself by taking zero
    steps of execution. *)

(** Second, it contains [R] -- that is, single-step executions are a
    particular case of multi-step executions.  (It is this fact that
    justifies the word "closure" in the term "multi-step closure of
    [R].") *)

Theorem multi_R : forall (X : Type) (R : relation X) (x y : X),
    R x y -> (multi R) x y.
Proof.
  intros X R x y H.
  apply multi_step with y. apply H. apply multi_refl.
Qed.

(** Third, [multi R] is _transitive_. *)

Theorem multi_trans :
  forall (X : Type) (R : relation X) (x y z : X),
      multi R x y  ->
      multi R y z ->
      multi R x z.
Proof.
  intros X R x y z G H.
  induction G.
    - (* multi_refl *) assumption.
    - (* multi_step *)
      apply multi_step with y. assumption.
      apply IHG. assumption.
Qed.

(** In particular, for the [multi step] relation on terms, if
    [t1 -->* t2] and [t2 -->* t3], then [t1 -->* t3]. *)

(* ================================================================= *)
(** ** Examples *)

(** Here's a specific instance of the [multi step] relation: *)

Lemma test_multistep_1:
      P
        (P (C 0) (C 3))
        (P (C 2) (C 4))
   -->*
      C ((0 + 3) + (2 + 4)).
Proof.
  apply multi_step with
            (P (C (0 + 3))
               (P (C 2) (C 4))).
  { apply ST_Plus1. apply ST_PlusConstConst. }
  apply multi_step with
            (P (C (0 + 3))
               (C (2 + 4))).
  { apply ST_Plus2. apply v_const. apply ST_PlusConstConst. }
  apply multi_R.
  apply ST_PlusConstConst.
Qed.

(** Here's an alternate proof of the same fact that uses [eapply] to
    avoid explicitly constructing all the intermediate terms. *)

Lemma test_multistep_1':
      P
        (P (C 0) (C 3))
        (P (C 2) (C 4))
  -->*
      C ((0 + 3) + (2 + 4)).
Proof.
  eapply multi_step. { apply ST_Plus1. apply ST_PlusConstConst. }
  eapply multi_step. { apply ST_Plus2. apply v_const.
                       apply ST_PlusConstConst. }
  eapply multi_step. { apply ST_PlusConstConst. }
  apply multi_refl.
Qed.

(** **** Exercise: 1 star, standard, optional (test_multistep_2)  *)
Lemma test_multistep_2:
  C 3 -->* C 3.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 1 star, standard, optional (test_multistep_3)  *)
Lemma test_multistep_3:
      P (C 0) (C 3)
   -->*
      P (C 0) (C 3).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard (test_multistep_4)  *)
Lemma test_multistep_4:
      P
        (C 0)
        (P
          (C 2)
          (P (C 0) (C 3)))
  -->*
      P
        (C 0)
        (C (2 + (0 + 3))).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** Normal Forms Again *)

(** If [t] reduces to [t'] in zero or more steps and [t'] is a
    normal form, we say that "[t'] is a normal form of [t]." *)

Definition step_normal_form := normal_form step.

Definition normal_form_of (t t' : tm) :=
  (t -->* t' /\ step_normal_form t').

(** We have already seen that, for our language, single-step reduction is
    deterministic -- i.e., a given term can take a single step in
    at most one way.  It follows from this that, if [t] can reach
    a normal form, then this normal form is unique.  In other words, we
    can actually pronounce [normal_form t t'] as "[t'] is _the_
    normal form of [t]." *)

(** **** Exercise: 3 stars, standard, optional (normal_forms_unique)  *)
Theorem normal_forms_unique:
  deterministic normal_form_of.
Proof.
  (* We recommend using this initial setup as-is! *)
  unfold deterministic. unfold normal_form_of.
  intros x y1 y2 P1 P2.
  destruct P1 as [P11 P12].
  destruct P2 as [P21 P22].
  generalize dependent y2.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** Indeed, something stronger is true for this language (though not
    for all languages): the reduction of _any_ term [t] will
    eventually reach a normal form -- i.e., [normal_form_of] is a
    _total_ function.  Formally, we say the [step] relation is
    _normalizing_. *)

Definition normalizing {X : Type} (R : relation X) :=
  forall t, exists t',
    (multi R) t t' /\ normal_form R t'.

(** To prove that [step] is normalizing, we need a couple of lemmas.

    First, we observe that, if [t] reduces to [t'] in many steps, then
    the same sequence of reduction steps within [t] is also possible
    when [t] appears as the first argument to [P], and
    similarly when [t] appears as the second argument to [P]
    when the first argument is a value. *)

Lemma multistep_congr_1 : forall t1 t1' t2,
     t1 -->* t1' ->
     P t1 t2 -->* P t1' t2.
Proof.
  intros t1 t1' t2 H. induction H.
  - (* multi_refl *) apply multi_refl.
  - (* multi_step *) apply multi_step with (P y t2).
    + apply ST_Plus1. apply H.
    + apply IHmulti.
Qed.

(** **** Exercise: 2 stars, standard (multistep_congr_2)  *)
Lemma multistep_congr_2 : forall t1 t2 t2',
     value t1 ->
     t2 -->* t2' ->
     P t1 t2 -->* P t1 t2'.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** With these lemmas in hand, the main proof is a straightforward
    induction.

    _Theorem_: The [step] function is normalizing -- i.e., for every
    [t] there exists some [t'] such that [t] reduces to [t'] and [t']
    is a normal form.

    _Proof sketch_: By induction on terms.  There are two cases to
    consider:

    - [t = C n] for some [n].  Here [t] doesn't take a step, and we
      have [t' = t].  We can derive the left-hand side by reflexivity
      and the right-hand side by observing (a) that values are normal
      forms (by [nf_same_as_value]) and (b) that [t] is a value (by
      [v_const]).

    - [t = P t1 t2] for some [t1] and [t2].  By the IH, [t1] and [t2]
      reduce to normal forms [t1'] and [t2'].  Recall that normal
      forms are values (by [nf_same_as_value]); we therefore know that
      [t1' = C n1] and [t2' = C n2], for some [n1] and [n2].  We can
      combine the [-->*] derivations for [t1] and [t2] using
      [multi_congr_1] and [multi_congr_2] to prove that [P t1 t2]
      reduces in many steps to [t' = C (n1 + n2)].

      Finally, [C (n1 + n2)] is a value, which is in turn a normal
      form by [nf_same_as_value]. [] *)

Theorem step_normalizing :
  normalizing step.
Proof.
  unfold normalizing.
  induction t.
  - (* C *)
    exists (C n).
    split.
    + (* l *) apply multi_refl.
    + (* r *)
      (* We can use [rewrite] with "iff" statements, not
           just equalities: *)
      rewrite nf_same_as_value. apply v_const.
  - (* P *)
    destruct IHt1 as [t1' [Hsteps1 Hnormal1] ].
    destruct IHt2 as [t2' [Hsteps2 Hnormal2] ].
    rewrite nf_same_as_value in Hnormal1.
    rewrite nf_same_as_value in Hnormal2.
    destruct Hnormal1 as [n1].
    destruct Hnormal2 as [n2].
    exists (C (n1 + n2)).
    split.
    + (* l *)
      apply multi_trans with (P (C n1) t2).
      * apply multistep_congr_1. apply Hsteps1.
      * apply multi_trans with (P (C n1) (C n2)).
        { apply multistep_congr_2. apply v_const. apply Hsteps2. }
        apply multi_R. apply ST_PlusConstConst.
    + (* r *)
      rewrite nf_same_as_value. apply v_const.
Qed.

(* ================================================================= *)
(** ** Equivalence of Big-Step and Small-Step *)

(** Having defined the operational semantics of our tiny programming
    language in two different ways (big-step and small-step), it makes
    sense to ask whether these definitions actually define the same
    thing! *)

(** They do, though it takes a little work to show it.  The
    details are left as an exercise. *)

(** **** Exercise: 3 stars, standard (eval__multistep)  *)
Theorem eval__multistep : forall t n,
  t ==> n -> t -->* C n.

(** The key ideas in the proof can be seen in the following picture:

       P t1 t2 -->            (by ST_Plus1)
       P t1' t2 -->           (by ST_Plus1)
       P t1'' t2 -->          (by ST_Plus1)
       ...
       P (C n1) t2 -->        (by ST_Plus2)
       P (C n1) t2' -->       (by ST_Plus2)
       P (C n1) t2'' -->      (by ST_Plus2)
       ...
       P (C n1) (C n2) -->    (by ST_PlusConstConst)
       C (n1 + n2)

    That is, the multistep reduction of a term of the form [P t1 t2]
    proceeds in three phases:
       - First, we use [ST_Plus1] some number of times to reduce [t1]
         to a normal form, which must (by [nf_same_as_value]) be a
         term of the form [C n1] for some [n1].
       - Next, we use [ST_Plus2] some number of times to reduce [t2]
         to a normal form, which must again be a term of the form [C
         n2] for some [n2].
       - Finally, we use [ST_PlusConstConst] one time to reduce [P (C
         n1) (C n2)] to [C (n1 + n2)]. *)

(** To formalize this intuition, you'll need to use the congruence
    lemmas from above (you might want to review them now, so that
    you'll be able to recognize when they are useful), plus some basic
    properties of [-->*]: that it is reflexive, transitive, and
    includes [-->]. *)

Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, advanced (eval__multistep_inf) 

    Write a detailed informal version of the proof of [eval__multistep].

(* FILL IN HERE *)
*)

(* Do not modify the following line: *)
Definition manual_grade_for_eval__multistep_inf : option (nat*string) := None.
(** [] *)

(** For the other direction, we need one lemma, which establishes a
    relation between single-step reduction and big-step evaluation. *)

(** **** Exercise: 3 stars, standard (step__eval)  *)
Lemma step__eval : forall t t' n,
     t --> t' ->
     t' ==> n ->
     t  ==> n.
Proof.
  intros t t' n Hs. generalize dependent n.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** The fact that small-step reduction implies big-step evaluation is now
    straightforward to prove.

    The proof proceeds by induction on the multi-step reduction
    sequence that is buried in the hypothesis [normal_form_of t t']. *)

(** Make sure you understand the statement before you start to
    work on the proof.  *)

(** **** Exercise: 3 stars, standard (multistep__eval)  *)
Theorem multistep__eval : forall t t',
  normal_form_of t t' -> exists n, t' = C n /\ t ==> n.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** Additional Exercises *)

(** **** Exercise: 3 stars, standard, optional (interp_tm) 

    Remember that we also defined big-step evaluation of terms as a
    function [evalF].  Prove that it is equivalent to the existing
    semantics.  (Hint: we just proved that [eval] and [multistep] are
    equivalent, so logically it doesn't matter which you choose.
    One will be easier than the other, though!) *)

Theorem evalF_eval : forall t n,
  evalF t = n <-> t ==> n.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 4 stars, standard (combined_properties) 

    We've considered arithmetic and conditional expressions
    separately.  This exercise explores how the two interact. *)

Module Combined.

Inductive tm : Type :=
  | C : nat -> tm
  | P : tm -> tm -> tm
  | tru : tm
  | fls : tm
  | test : tm -> tm -> tm -> tm.

Inductive value : tm -> Prop :=
  | v_const : forall n, value (C n)
  | v_tru : value tru
  | v_fls : value fls.

Reserved Notation " t '-->' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
      P (C n1) (C n2) --> C (n1 + n2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 --> t1' ->
      P t1 t2 --> P t1' t2
  | ST_Plus2 : forall v1 t2 t2',
      value v1 ->
      t2 --> t2' ->
      P v1 t2 --> P v1 t2'
  | ST_IfTrue : forall t1 t2,
      test tru t1 t2 --> t1
  | ST_IfFalse : forall t1 t2,
      test fls t1 t2 --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      test t1 t2 t3 --> test t1' t2 t3

  where " t '-->' t' " := (step t t').

(** Earlier, we separately proved for both plus- and if-expressions...

    - that the step relation was deterministic, and

    - a strong progress lemma, stating that every term is either a
      value or can take a step.

    Formally prove or disprove these two properties for the combined
    language.  (That is, state a theorem saying that the property
    holds or does not hold, and prove your theorem.) *)

(* FILL IN HERE *)

End Combined.

(* Do not modify the following line: *)
Definition manual_grade_for_combined_properties : option (nat*string) := None.
(** [] *)

(* ################################################################# *)
(** * Small-Step Imp *)

(** Now for a more serious example: a small-step version of the Imp
    operational semantics. *)

(** The small-step reduction relations for arithmetic and
    boolean expressions are straightforward extensions of the tiny
    language we've been working up to now.  To make them easier to
    read, we introduce the symbolic notations [-->a] and [-->b] for
    the arithmetic and boolean step relations. *)

Inductive aval : aexp -> Prop :=
  | av_num : forall n, aval (ANum n).

(** We are not actually going to bother to define boolean
    values, since they aren't needed in the definition of [-->b]
    below (why?), though they might be if our language were a bit
    more complicated (why?). *)

Reserved Notation " a '/' st '-->a' a' "
                  (at level 40, st at level 39).

Inductive astep (st : state) : aexp -> aexp -> Prop :=
  | AS_Id : forall i,
      AId i / st -->a ANum (st i)
  | AS_Plus1 : forall a1 a1' a2,
      a1 / st -->a a1' ->
      (APlus a1 a2) / st -->a (APlus a1' a2)
  | AS_Plus2 : forall v1 a2 a2',
      aval v1 ->
      a2 / st -->a a2' ->
      (APlus v1 a2) / st -->a (APlus v1 a2')
  | AS_Plus : forall n1 n2,
      APlus (ANum n1) (ANum n2) / st -->a ANum (n1 + n2)
  | AS_Minus1 : forall a1 a1' a2,
      a1 / st -->a a1' ->
      (AMinus a1 a2) / st -->a (AMinus a1' a2)
  | AS_Minus2 : forall v1 a2 a2',
      aval v1 ->
      a2 / st -->a a2' ->
      (AMinus v1 a2) / st -->a (AMinus v1 a2')
  | AS_Minus : forall n1 n2,
      (AMinus (ANum n1) (ANum n2)) / st -->a (ANum (minus n1 n2))
  | AS_Mult1 : forall a1 a1' a2,
      a1 / st -->a a1' ->
      (AMult a1 a2) / st -->a (AMult a1' a2)
  | AS_Mult2 : forall v1 a2 a2',
      aval v1 ->
      a2 / st -->a a2' ->
      (AMult v1 a2) / st -->a (AMult v1 a2')
  | AS_Mult : forall n1 n2,
      (AMult (ANum n1) (ANum n2)) / st -->a (ANum (mult n1 n2))

    where " a '/' st '-->a' a' " := (astep st a a').

Reserved Notation " b '/' st '-->b' b' "
                  (at level 40, st at level 39).

Inductive bstep (st : state) : bexp -> bexp -> Prop :=
| BS_Eq1 : forall a1 a1' a2,
    a1 / st -->a a1' ->
    (BEq a1 a2) / st -->b (BEq a1' a2)
| BS_Eq2 : forall v1 a2 a2',
    aval v1 ->
    a2 / st -->a a2' ->
    (BEq v1 a2) / st -->b (BEq v1 a2')
| BS_Eq : forall n1 n2,
    (BEq (ANum n1) (ANum n2)) / st -->b
    (if (n1 =? n2) then BTrue else BFalse)
| BS_LtEq1 : forall a1 a1' a2,
    a1 / st -->a a1' ->
    (BLe a1 a2) / st -->b (BLe a1' a2)
| BS_LtEq2 : forall v1 a2 a2',
    aval v1 ->
    a2 / st -->a a2' ->
    (BLe v1 a2) / st -->b (BLe v1 a2')
| BS_LtEq : forall n1 n2,
    (BLe (ANum n1) (ANum n2)) / st -->b
             (if (n1 <=? n2) then BTrue else BFalse)
| BS_NotStep : forall b1 b1',
    b1 / st -->b b1' ->
    (BNot b1) / st -->b (BNot b1')
| BS_NotTrue : (BNot BTrue) / st -->b BFalse
| BS_NotFalse : (BNot BFalse) / st -->b BTrue
| BS_AndStep : forall b1 b1' b2,
    b1 / st -->b b1' ->
    (BAnd b1 b2) / st -->b (BAnd b1' b2)
| BS_AndTrueStep : forall b2 b2',
    b2 / st -->b b2' ->
    (BAnd BTrue b2) / st -->b (BAnd BTrue b2')
| BS_AndFalse : forall b2,
    (BAnd BFalse b2) / st -->b BFalse
| BS_AndTrueTrue : (BAnd BTrue BTrue) / st -->b BTrue
| BS_AndTrueFalse : (BAnd BTrue BFalse) / st -->b BFalse

where " b '/' st '-->b' b' " := (bstep st b b').

(** The semantics of commands is the interesting part.  We need two
    small tricks to make it work:

       - We use [skip] as a "command value" -- i.e., a command that
         has reached a normal form.

            - An assignment command reduces to [skip] (and an updated
              state).

            - The sequencing command waits until its left-hand
              subcommand has reduced to [skip], then throws it away so
              that reduction can continue with the right-hand
              subcommand.

       - We reduce a [while] command by transforming it into a
         conditional followed by the same [while]. *)

(** (There are other ways of achieving the effect of the latter
    trick, but they all share the feature that the original [while]
    command needs to be saved somewhere while a single copy of the loop
    body is being reduced.) *)

Reserved Notation " t '/' st '-->' t' '/' st' "
                  (at level 40, st at level 39, t' at level 39).

Inductive cstep : (com * state) -> (com * state) -> Prop :=
  | CS_AssStep : forall st i a1 a1',
      a1 / st -->a a1' ->
      <{ i := a1 }> / st --> <{ i := a1' }> / st
  | CS_Ass : forall st i n,
      <{ i := ANum n }> / st --> <{ skip }> / (i !-> n ; st)
  | CS_SeqStep : forall st c1 c1' st' c2,
      c1 / st --> c1' / st' ->
      <{ c1 ; c2 }> / st --> <{ c1' ; c2 }> / st'
  | CS_SeqFinish : forall st c2,
      <{ skip ; c2 }> / st --> c2 / st
  | CS_IfStep : forall st b1 b1' c1 c2,
      b1 / st -->b b1' ->
      <{ if b1 then c1 else c2 end }> / st
      -->
      <{ if b1' then c1 else c2 end }> / st
  | CS_IfTrue : forall st c1 c2,
      <{ if true then c1 else c2 end }> / st --> c1 / st
  | CS_IfFalse : forall st c1 c2,
      <{ if false then c1 else c2 end }> / st --> c2 / st
  | CS_While : forall st b1 c1,
      <{ while b1 do c1 end }> / st
      -->
      <{ if b1 then c1; while b1 do c1 end else skip end }> / st

  where " t '/' st '-->' t' '/' st' " := (cstep (t,st) (t',st')).

(* ################################################################# *)
(** * Concurrent Imp *)

(** Finally, to show the power of this definitional style, let's
    enrich Imp with a new form of command that runs two subcommands in
    parallel and terminates when both have terminated.  To reflect the
    unpredictability of scheduling, the actions of the subcommands may
    be interleaved in any order, but they share the same memory and
    can communicate by reading and writing the same variables. *)

Module CImp.

Inductive com : Type :=
  | CSkip : com
  | CAss : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CPar : com -> com -> com.         (* <--- NEW *)

Notation "'par' c1 'with' c2 'end'" :=
         (CPar c1 c2)
            (in custom com at level 0, c1 at level 99, c2 at level 99).
Notation "'skip'"  :=
         CSkip (in custom com at level 0).
Notation "x := y"  :=
         (CAss x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity).
Notation "x ; y" :=
         (CSeq x y)
           (in custom com at level 90, right associativity).
Notation "'if' x 'then' y 'else' z 'end'" :=
         (CIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99).
Notation "'while' x 'do' y 'end'" :=
         (CWhile x y)
            (in custom com at level 89, x at level 99, y at level 99).

Inductive cstep : (com * state)  -> (com * state) -> Prop :=
    (* Old part *)
  | CS_AssStep : forall st i a1 a1',
      a1 / st -->a a1' ->
      <{ i := a1 }> / st --> <{i := a1'}> / st
  | CS_Ass : forall st i n,
      <{i := ANum n}> / st --> <{skip}> / (i !-> n ; st)
  | CS_SeqStep : forall st c1 c1' st' c2,
      c1 / st --> c1' / st' ->
      <{c1 ; c2}> / st --> <{c1' ; c2}> / st'
  | CS_SeqFinish : forall st c2,
      <{skip ; c2}> / st --> c2 / st
  | CS_IfStep : forall st b1 b1' c1 c2,
      b1 /st -->b b1' ->
          <{if b1  then c1 else c2 end}> / st
      --> <{if b1' then c1 else c2 end}> / st
  | CS_IfTrue : forall st c1 c2,
      <{if true then c1 else c2 end}> / st --> c1 / st
  | CS_IfFalse : forall st c1 c2,
      <{if false then c1 else c2 end}> / st --> c2 / st
  | CS_While : forall st b1 c1,
          <{while b1 do c1 end}> / st
      --> <{if b1 then (c1; (while b1 do c1 end)) else skip end}> / st
    (* New part: *)
  | CS_Par1 : forall st c1 c1' c2 st',
      c1 / st --> c1' / st' ->
      <{par c1 with c2 end}> / st --> <{par c1' with c2 end}> / st'
  | CS_Par2 : forall st c1 c2 c2' st',
      c2 / st --> c2' / st' ->
      <{par c1 with c2 end}> / st --> <{par c1 with c2' end}> / st'
  | CS_ParDone : forall st,
      <{par skip with skip end}> / st --> <{skip}> / st
  where " t '/' st '-->' t' '/' st' " := (cstep (t,st) (t',st')).

Definition cmultistep := multi cstep.

Notation " t '/' st '-->*' t' '/' st' " :=
   (multi cstep  (t,st) (t',st'))
   (at level 40, st at level 39, t' at level 39).

(** Among the many interesting properties of this language is the fact
    that the following program can terminate with the variable [X] set
    to any value. *)

Definition par_loop : com :=
  <{
  par
    Y := 1
  with
    while (Y = 0) do
      X := X + 1
    end
  end}>.

(** In particular, it can terminate with [X] set to [0]: *)

Example par_loop_example_0:
  exists st',
       par_loop / empty_st  -->* <{skip}> / st'
    /\ st' X = 0.
Proof.
  eapply ex_intro. split.
  unfold par_loop.
  eapply multi_step. apply CS_Par1.
    apply CS_Ass.
  eapply multi_step. apply CS_Par2. apply CS_While.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq1. apply AS_Id.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq. simpl.
  eapply multi_step. apply CS_Par2. apply CS_IfFalse.
  eapply multi_step. apply CS_ParDone.
  eapply multi_refl.
  reflexivity. Qed.

(** It can also terminate with [X] set to [2]: *)

Example par_loop_example_2:
  exists st',
       par_loop / empty_st -->* <{skip}> / st'
    /\ st' X = 2.
Proof.
  eapply ex_intro. split.
  eapply multi_step. apply CS_Par2. apply CS_While.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq1. apply AS_Id.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq. simpl.
  eapply multi_step. apply CS_Par2. apply CS_IfTrue.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_AssStep. apply AS_Plus1. apply AS_Id.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_AssStep. apply AS_Plus.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_Ass.
  eapply multi_step. apply CS_Par2. apply CS_SeqFinish.

  eapply multi_step. apply CS_Par2. apply CS_While.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq1. apply AS_Id.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq. simpl.
  eapply multi_step. apply CS_Par2. apply CS_IfTrue.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_AssStep. apply AS_Plus1. apply AS_Id.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_AssStep. apply AS_Plus.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_Ass.

  eapply multi_step. apply CS_Par1. apply CS_Ass.
  eapply multi_step. apply CS_Par2. apply CS_SeqFinish.
  eapply multi_step. apply CS_Par2. apply CS_While.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq1. apply AS_Id.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq. simpl.
  eapply multi_step. apply CS_Par2. apply CS_IfFalse.
  eapply multi_step. apply CS_ParDone.
  eapply multi_refl.
  reflexivity. Qed.

(** More generally... *)

(** **** Exercise: 3 stars, standard, optional (par_body_n__Sn)  *)
Lemma par_body_n__Sn : forall n st,
  st X = n /\ st Y = 0 ->
  par_loop / st -->* par_loop / (X !-> S n ; st).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (par_body_n)  *)
Lemma par_body_n : forall n st,
  st X = 0 /\ st Y = 0 ->
  exists st',
    par_loop / st -->*  par_loop / st' /\ st' X = n /\ st' Y = 0.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** ... the above loop can exit with [X] having any value
    whatsoever. *)

Theorem par_loop_any_X:
  forall n, exists st',
    par_loop / empty_st -->*  <{skip}> / st'
    /\ st' X = n.
Proof.
  intros n.
  destruct (par_body_n n empty_st).
    split; reflexivity.

  rename x into st.
  inversion H as [H' [HX HY] ]; clear H.
  exists (Y !-> 1 ; st). split.
  eapply multi_trans with (par_loop,st). apply H'.
  eapply multi_step. apply CS_Par1. apply CS_Ass.
  eapply multi_step. apply CS_Par2. apply CS_While.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq1. apply AS_Id. rewrite t_update_eq.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq. simpl.
  eapply multi_step. apply CS_Par2. apply CS_IfFalse.
  eapply multi_step. apply CS_ParDone.
  apply multi_refl.

  rewrite t_update_neq. assumption. intro X; inversion X.
Qed.

End CImp.

(* ################################################################# *)
(** * A Small-Step Stack Machine *)

(** Our last example is a small-step semantics for the stack machine
    example from the [Imp] chapter of _Logical Foundations_. *)

Definition stack := list nat.
Definition prog  := list sinstr.

Inductive stack_step (st : state) : prog * stack -> prog * stack -> Prop :=
  | SS_Push : forall stk n p,
    stack_step st (SPush n :: p, stk)      (p, n :: stk)
  | SS_Load : forall stk i p,
    stack_step st (SLoad i :: p, stk)      (p, st i :: stk)
  | SS_Plus : forall stk n m p,
    stack_step st (SPlus :: p, n::m::stk)  (p, (m+n)::stk)
  | SS_Minus : forall stk n m p,
    stack_step st (SMinus :: p, n::m::stk) (p, (m-n)::stk)
  | SS_Mult : forall stk n m p,
    stack_step st (SMult :: p, n::m::stk)  (p, (m*n)::stk).

Theorem stack_step_deterministic : forall st,
  deterministic (stack_step st).
Proof.
  unfold deterministic. intros st x y1 y2 H1 H2.
  induction H1; inversion H2; reflexivity.
Qed.

Definition stack_multistep st := multi (stack_step st).

(** **** Exercise: 3 stars, advanced (compiler_is_correct) 

    Remember the definition of [compile] for [aexp] given in the
    [Imp] chapter of _Logical Foundations_. We want now to
    prove [s_compile] correct with respect to the stack machine.

    Copy your definition of [s_compile] from Imp here, then state
    what it means for the compiler to be correct according to the
    stack machine small step semantics, and then prove it. *)

(* Copy your definition of s_compile here *)

Definition compiler_is_correct_statement : Prop
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Theorem compiler_is_correct : compiler_is_correct_statement.
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################################# *)
(** * Aside: A [normalize] Tactic *)

(** When experimenting with definitions of programming languages
    in Coq, we often want to see what a particular concrete term steps
    to -- i.e., we want to find proofs for goals of the form [t -->*
    t'], where [t] is a completely concrete term and [t'] is unknown.
    These proofs are quite tedious to do by hand.  Consider, for
    example, reducing an arithmetic expression using the small-step
    relation [astep]. *)

Example step_example1 :
  (P (C 3) (P (C 3) (C 4)))
  -->* (C 10).
Proof.
  apply multi_step with (P (C 3) (C 7)).
    apply ST_Plus2.
      apply v_const.
      apply ST_PlusConstConst.
  apply multi_step with (C 10).
    apply ST_PlusConstConst.
  apply multi_refl.
Qed.

(** The proof repeatedly applies [multi_step] until the term reaches a
    normal form.  Fortunately The sub-proofs for the intermediate
    steps are simple enough that [auto], with appropriate hints, can
    solve them. *)

Hint Constructors step value : core.
Example step_example1' :
  (P (C 3) (P (C 3) (C 4)))
  -->* (C 10).
Proof.
  eapply multi_step. auto. simpl.
  eapply multi_step. auto. simpl.
  apply multi_refl.
Qed.

(** The following custom [Tactic Notation] definition captures this
    pattern.  In addition, before each step, we print out the current
    goal, so that we can follow how the term is being reduced. *)

Tactic Notation "print_goal" :=
  match goal with |- ?x => idtac x end.

Tactic Notation "normalize" :=
  repeat (print_goal; eapply multi_step ;
            [ (eauto 10; fail) | (instantiate; simpl)]);
  apply multi_refl.

Example step_example1'' :
  (P (C 3) (P (C 3) (C 4)))
  -->* (C 10).
Proof.
  normalize.
  (* The [print_goal] in the [normalize] tactic shows
     a trace of how the expression reduced...
         (P (C 3) (P (C 3) (C 4)) -->* C 10)
         (P (C 3) (C 7) -->* C 10)
         (C 10 -->* C 10)
  *)
Qed.

(** The [normalize] tactic also provides a simple way to calculate the
    normal form of a term, by starting with a goal with an existentially
    bound variable. *)

Example step_example1''' : exists e',
  (P (C 3) (P (C 3) (C 4)))
  -->* e'.
Proof.
  eexists. normalize.
Qed.
(** This time, the trace is:

       (P (C 3) (P (C 3) (C 4)) -->* ?e')
       (P (C 3) (C 7) -->* ?e')
       (C 10 -->* ?e')

   where [?e'] is the variable ``guessed'' by eapply. *)

(** **** Exercise: 1 star, standard (normalize_ex)  *)
Theorem normalize_ex : exists e',
  (P (C 3) (P (C 2) (C 1)))
  -->* e' /\ value e'.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 1 star, standard, optional (normalize_ex') 

    For comparison, prove it using [apply] instead of [eapply]. *)

Theorem normalize_ex' : exists e',
  (P (C 3) (P (C 2) (C 1)))
  -->* e' /\ value e'.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* 2020-09-09 21:08 *)
