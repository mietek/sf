(** * Auto: More Automation *)

Require Import Coq.omega.Omega.
Require Import Maps.
Require Import Imp.

(** Up to now, we've used a quite restricted set of Coq's tactic
    facilities.  In this chapter, we'll learn more about two very
    powerful features of Coq's tactic language: proof search via the
    [auto] and [eauto] tactics, and automated forward reasoning via
    the [Ltac] hypothesis matching machinery.  Using these features
    together with Ltac's scripting facilities will enable us to make
    our proofs startlingly short!  Used properly, they can also make
    proofs more maintainable and robust in the face of incremental
    changes to underlying definitions.  This chapter introduces [auto]
    and [eauto].  A deeper treatment can be found in the [UseAuto]
    chapter.

    There's a third major category of automation we haven't fully
    studied yet, namely built-in decision procedures for specific
    kinds of problems: [omega] is one example, but there are others.
    This topic will be deferred for a while longer. 

    Our motivating example will be this proof, repeated with just a
    few small changes from [Imp].  We will try to simplify this proof
    in several stages. *)

Ltac inv H := inversion H; subst; clear H.

Theorem ceval_deterministic: forall c st st1 st2,
     c / st \\ st1  ->
     c / st \\ st2 ->
     st1 = st2.
Proof.
  intros c st st1 st2 E1 E2;
  generalize dependent st2;
  induction E1; intros st2 E2; inv E2.
  - (* E_Skip *) reflexivity.
  - (* E_Ass *) reflexivity.
  - (* E_Seq *)
    assert (st' = st'0) as EQ1.
    { (* Proof of assertion *) apply IHE1_1; assumption. }
    subst st'0.
    apply IHE1_2. assumption.
  (* E_IfTrue *)
  - (* b evaluates to true *)
    apply IHE1. assumption.
  - (* b evaluates to false (contradiction) *)
    rewrite H in H5. inversion H5.
  (* E_IfFalse *)
  - (* b evaluates to true (contradiction) *)
    rewrite H in H5. inversion H5.
  - (* b evaluates to false *)
    apply IHE1. assumption.
  (* E_WhileEnd *)
  - (* b evaluates to false *)
    reflexivity.
  - (* b evaluates to true (contradiction) *)
    rewrite H in H2. inversion H2.
  (* E_WhileLoop *)
  - (* b evaluates to false (contradiction) *)
    rewrite H in H4. inversion H4.
  - (* b evaluates to true *)
    assert (st' = st'0) as EQ1.
    { (* Proof of assertion *) apply IHE1_1; assumption. }
    subst st'0.
    apply IHE1_2. assumption.  Qed.

(** * The [auto] and [eauto] Tactics *)

(** Thus far, we have generally written proof scripts that apply
    relevant hypotheses or lemmas by name.  In particular, when a
    chain of hypothesis applications is needed, we have specified them
    explicitly.  (The only exceptions we've seen to this are using
    [assumption] to find a matching unqualified hypothesis or
    [(e)constructor] to find a matching constructor.) *)

Example auto_example_1 : forall (P Q R: Prop), (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  intros P Q R H1 H2 H3.
  apply H2.  apply H1. assumption.
Qed.

(** The [auto] tactic frees us from this drudgery by _searching_
   for a sequence of applications that will prove the goal *)

Example auto_example_1' : forall (P Q R: Prop), (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  intros P Q R H1 H2 H3.
  auto.
Qed.

(** The [auto] tactic solves goals that are solvable by any combination of
     - [intros],
     - [apply] (with a local hypothesis, by default).

    The [eauto] tactic works just like [auto], except that it uses
    [eapply] instead of [apply]. *)

(** Using [auto] is always "safe" in the sense that it will never fail
    and will never change the proof state: either it completely solves
    the current goal, or it does nothing. *)

(** A more complicated example: *)

Example auto_example_2 : forall P Q R S T U : Prop,
  (P -> Q) ->
  (P -> R) ->
  (T -> R) ->
  (S -> T -> U) ->
  ((P->Q) -> (P->S)) ->
  T ->
  P ->
  U.
Proof. auto. Qed.

(** Search can take an arbitrarily long time, so there are limits to
    how far [auto] will search by default. *)

Example auto_example_3 : forall (P Q R S T U: Prop),
                           (P -> Q) -> (Q -> R) -> (R -> S) ->
                           (S -> T) -> (T -> U) -> P -> U.
Proof.
  (* When it cannot solve the goal, [auto] does nothing *)
  auto. 
  (* Optional argument says how deep to search (default depth is 5) *)
  auto 6. 
Qed.

(** When searching for potential proofs of the current goal,
    [auto] and [eauto] consider the hypotheses in the current context
    together with a _hint database_ of other lemmas and constructors.
    Some of the lemmas and constructors we've already seen -- e.g.,
    [eq_refl], [conj], [or_introl], and [or_intror] -- are installed
    in this hint database by default. *)

Example auto_example_4 : forall P Q R : Prop,
  Q ->
  (Q -> R) ->
  P \/ (Q /\ R).
Proof.
  auto. Qed.

(** If we want to see which facts [auto] is using, we can use
    [info_auto] instead. *)

Example auto_example_5: 2 = 2.
Proof.
  (* auto subsumes reflexivity because eq_refl is in hint database *)
  info_auto.  
Qed.

(** We can extend the hint database just for the purposes of one
    application of [auto] or [eauto] by writing [auto using ...]. *)

Lemma le_antisym : forall n m: nat, (n <= m /\ m <= n) -> n = m.
Proof. intros. omega. Qed.

Example auto_example_6 : forall n m p : nat,
  (n<= p -> (n <= m /\ m <= n)) ->
  n <= p ->
  n = m.
Proof.
  intros.
  auto. (* does nothing: auto doesn't destruct hypotheses! *)
  auto using le_antisym.
Qed.

(** Of course, in any given development there will probably be
    some specific constructors and lemmas that are used very often in
    proofs.  We can add these to the global hint database by writing

      Hint Resolve T.

    at the top level, where [T] is a top-level theorem or a
    constructor of an inductively defined proposition (i.e., anything
    whose type is an implication).  As a shorthand, we can write

      Hint Constructors c.

    to tell Coq to do a [Hint Resolve] for _all_ of the constructors
    from the inductive definition of [c].

    It is also sometimes necessary to add

      Hint Unfold d.

    where [d] is a defined symbol, so that [auto] knows to expand uses
    of [d] and enable further possibilities for applying lemmas that
    it knows about. *)

Hint Resolve le_antisym.

Example auto_example_6' : forall n m p : nat,
  (n<= p -> (n <= m /\ m <= n)) ->
  n <= p ->
  n = m.
Proof.
  intros.
  auto. (* picks up hint from database *)
Qed.

Definition is_fortytwo x := x = 42.

Example auto_example_7: forall x, (x <= 42 /\ 42 <= x) -> is_fortytwo x.
Proof.
  auto.  (* does nothing *)
Abort.

Hint Unfold is_fortytwo.

Example auto_example_7' : forall x, (x <= 42 /\ 42 <= x) -> is_fortytwo x.
Proof.
  info_auto.
Qed.

Hint Constructors ceval.
Hint Transparent state.
Hint Transparent total_map.

Definition st12 := t_update (t_update empty_state X 1) Y 2.
Definition st21 := t_update (t_update empty_state X 2) Y 1.

Example auto_example_8 : exists s',
  (IFB (BLe (AId X) (AId Y))
    THEN (Z ::= AMinus (AId Y) (AId X))
    ELSE (Y ::= APlus (AId X) (AId Z))
  FI) / st21 \\ s'.
Proof. eauto. Qed.

Example auto_example_8' : exists s',
  (IFB (BLe (AId X) (AId Y))
    THEN (Z ::= AMinus (AId Y) (AId X))
    ELSE (Y ::= APlus (AId X) (AId Z))
  FI) / st12 \\ s'.
Proof. info_eauto. Qed.

(** Now let's take a pass over [ceval_deterministic] using [auto] to
    simplify the proof script. We see that all simple sequences of
    hypothesis applications and all uses of [reflexivity] can be
    replaced by [auto], which we add to the default tactic to be
    applied to each case. *)

Theorem ceval_deterministic': forall c st st1 st2,
     c / st \\ st1  ->
     c / st \\ st2 ->
     st1 = st2.
Proof.
  intros c st st1 st2 E1 E2;
  generalize dependent st2;
  induction E1;
           intros st2 E2; inv E2; auto.
  - (* E_Seq *)
    assert (st' = st'0) as EQ1 by auto.
    subst st'0.
    auto.
  - (* E_IfTrue *)
    + (* b evaluates to false (contradiction) *)
      rewrite H in H5. inversion H5.
  - (* E_IfFalse *)
    + (* b evaluates to true (contradiction) *)
      rewrite H in H5. inversion H5.
  - (* E_WhileEnd *)
    + (* b evaluates to true (contradiction) *)
      rewrite H in H2. inversion H2.
  (* E_WhileLoop *)
  - (* b evaluates to false (contradiction) *)
    rewrite H in H4. inversion H4.
  - (* b evaluates to true *)
    assert (st' = st'0) as EQ1 by auto.
    subst st'0.
    auto.
Qed.

(** When we are using a particular tactic many times in a proof, we
    can use a variant of the [Proof] command to make that tactic into
    a default within the proof.  Saying [Proof with t] (where [t] is
    an arbitrary tactic) allows us to use [t1...] as a shorthand for
    [t1;t] within the proof.  As an illustration, here is an alternate
    version of the previous proof, using [Proof with auto]. *)

Theorem ceval_deterministic'_alt: forall c st st1 st2,
     c / st \\ st1  ->
     c / st \\ st2 ->
     st1 = st2.
Proof with auto.
  intros c st st1 st2 E1 E2;
  generalize dependent st2;
  induction E1;
           intros st2 E2; inv E2...
  - (* E_Seq *)
    assert (st' = st'0) as EQ1...
    subst st'0...
  - (* E_IfTrue *)
    + (* b evaluates to false (contradiction) *)
      rewrite H in H5. inversion H5.
  - (* E_IfFalse *)
    + (* b evaluates to true (contradiction) *)
      rewrite H in H5. inversion H5.
  - (* E_WhileEnd *)
    + (* b evaluates to true (contradiction) *)
      rewrite H in H2. inversion H2.
  (* E_WhileLoop *)
  - (* b evaluates to false (contradiction) *)
    rewrite H in H4. inversion H4.
  - (* b evaluates to true *)
    assert (st' = st'0) as EQ1...
    subst st'0...
Qed.

(** * Searching Hypotheses *)

(** The proof has become simpler, but there is still an annoying
    amount of repetition. Let's start by tackling the contradiction
    cases. Each of them occurs in a situation where we have both

      [H1: beval st b = false]

    and

      [H2: beval st b = true]

    as hypotheses.  The contradiction is evident, but demonstrating it
    is a little complicated: we have to locate the two hypotheses [H1]
    and [H2] and do a [rewrite] following by an [inversion].  We'd
    like to automate this process.

    (Note: In fact, Coq has a built-in tactic [congruence] that will do
    the job.  But we'll ignore the existence of this tactic for now,
    in order to demonstrate how to build forward search tactics by
    hand.) 

    As a first step, we can abstract out the piece of script in question by
    writing a small amount of paramerized Ltac. *)

Ltac rwinv H1 H2 := rewrite H1 in H2; inv H2.

Theorem ceval_deterministic'': forall c st st1 st2,
     c / st \\ st1  ->
     c / st \\ st2 ->
     st1 = st2.
Proof.
  intros c st st1 st2 E1 E2;
  generalize dependent st2;
  induction E1; intros st2 E2; inv E2; auto.
  - (* E_Seq *)
    assert (st' = st'0) as EQ1 by auto.
    subst st'0.
    auto.
  - (* E_IfTrue *)
    + (* b evaluates to false (contradiction) *)
      rwinv H H5.
  - (* E_IfFalse *)
    + (* b evaluates to true (contradiction) *)
      rwinv H H5.
  - (* E_WhileEnd *)
    + (* b evaluates to true (contradiction) *)
      rwinv H H2.
  (* E_WhileLoop *)
  - (* b evaluates to false (contradiction) *)
    rwinv H H4.
  - (* b evaluates to true *)
    assert (st' = st'0) as EQ1 by auto.
    subst st'0.
    auto. Qed.

(** But this is not much better.  We really want Coq to discover the
    relevant hypotheses for us.  We can do this by using the [match
    goal with ... end] facility of Ltac. *)

Ltac find_rwinv :=
  match goal with
    H1: ?E = true, H2: ?E = false |- _ => rwinv H1 H2
  end.

(** In words, this [match goal] looks for two distinct hypotheses that
    have the form of equalities with the same arbitrary expression [E]
    on the left and conflicting boolean values on the right; if such
    hypotheses are found, it binds [H1] and [H2] to their names, and
    applies the [rwinv] tactic.

    Adding this tactic to our default string handles all the
    contradiction cases. *)

Theorem ceval_deterministic''': forall c st st1 st2,
     c / st \\ st1  ->
     c / st \\ st2 ->
     st1 = st2.
Proof.
  intros c st st1 st2 E1 E2;
  generalize dependent st2;
  induction E1; intros st2 E2; inv E2; try find_rwinv; auto.
  - (* E_Seq *)
    assert (st' = st'0) as EQ1 by auto.
    subst st'0.
    auto.
  - (* E_WhileLoop *)
    + (* b evaluates to true *)
      assert (st' = st'0) as EQ1 by auto.
      subst st'0.
      auto. Qed.

(** Let's see about the remaining cases. Each of them involves
    applying a conditional hypothesis to extract an equality.
    Currently we have phrased these as assertions, so that we have to
    predict what the resulting equality will be (although we can then
    use [auto] to prove it.)  An alternative is to pick the relevant
    hypotheses to use, and then rewrite with them, as follows: *)

Theorem ceval_deterministic'''': forall c st st1 st2,
     c / st \\ st1  ->
     c / st \\ st2 ->
     st1 = st2.
Proof.
  intros c st st1 st2 E1 E2;
  generalize dependent st2;
  induction E1; intros st2 E2; inv E2; try find_rwinv; auto.
  - (* E_Seq *)
    rewrite (IHE1_1 st'0 H1) in *. auto.
  - (* E_WhileLoop *)
    + (* b evaluates to true *)
      rewrite (IHE1_1 st'0 H3) in *. auto. Qed.

(** Now we can automate the task of finding the relevant hypotheses to
    rewrite with. *)

Ltac find_eqn :=
  match goal with
    H1: forall x, ?P x -> ?L = ?R, H2: ?P ?X |- _ =>
         rewrite (H1 X H2) in *
  end.

(** But there are several pairs of hypotheses that have the right
    general form, and it seems tricky to pick out the ones we actually
    need.  A key trick is to realize that we can _try them all_!
    Here's how this works:

    - [rewrite] will fail given a trivial equation of the form [X = X];
    - each execution of [match goal] will keep trying to find a valid
      pair of hypotheses until the tactic on the RHS of the match
      succeeds; if there are no such pairs, it fails;
    - we can wrap the whole thing in a [repeat], which will keep doing
      useful rewrites until only trivial ones are left. *)

Theorem ceval_deterministic''''': forall c st st1 st2,
     c / st \\ st1  ->
     c / st \\ st2 ->
     st1 = st2.
Proof.
  intros c st st1 st2 E1 E2;
  generalize dependent st2;
  induction E1; intros st2 E2; inv E2; try find_rwinv;
    repeat find_eqn; auto.
  Qed.

(** The big payoff in this approach is that our proof script
    should be robust in the face of modest changes to our language.
    For example, we can add a [REPEAT] command to the language.
    (This was an exercise in [Hoare.v].) *)

Module Repeat.

Inductive com : Type :=
  | CSkip : com
  | CAsgn : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CRepeat : com -> bexp -> com.

(** [REPEAT] behaves like [WHILE], except that the loop guard is
    checked _after_ each execution of the body, with the loop
    repeating as long as the guard stays _false_.  Because of this,
    the body will always execute at least once. *)

Notation "'SKIP'" :=
  CSkip.
Notation "c1 ; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "X '::=' a" :=
  (CAsgn X a) (at level 60).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' e1 'THEN' e2 'ELSE' e3 'FI'" :=
  (CIf e1 e2 e3) (at level 80, right associativity).
Notation "'REPEAT' e1 'UNTIL' b2 'END'" :=
  (CRepeat e1 b2) (at level 80, right associativity).

Inductive ceval : state -> com -> state -> Prop :=
  | E_Skip : forall st,
      ceval st SKIP st
  | E_Ass  : forall st a1 n X,
      aeval st a1 = n ->
      ceval st (X ::= a1) (t_update st X n)
  | E_Seq : forall c1 c2 st st' st'',
      ceval st c1 st' ->
      ceval st' c2 st'' ->
      ceval st (c1 ; c2) st''
  | E_IfTrue : forall st st' b1 c1 c2,
      beval st b1 = true ->
      ceval st c1 st' ->
      ceval st (IFB b1 THEN c1 ELSE c2 FI) st'
  | E_IfFalse : forall st st' b1 c1 c2,
      beval st b1 = false ->
      ceval st c2 st' ->
      ceval st (IFB b1 THEN c1 ELSE c2 FI) st'
  | E_WhileEnd : forall b1 st c1,
      beval st b1 = false ->
      ceval st (WHILE b1 DO c1 END) st
  | E_WhileLoop : forall st st' st'' b1 c1,
      beval st b1 = true ->
      ceval st c1 st' ->
      ceval st' (WHILE b1 DO c1 END) st'' ->
      ceval st (WHILE b1 DO c1 END) st''
  | E_RepeatEnd : forall st st' b1 c1,
      ceval st c1 st' ->
      beval st' b1 = true ->
      ceval st (CRepeat c1 b1) st'
  | E_RepeatLoop : forall st st' st'' b1 c1,
      ceval st c1 st' ->
      beval st' b1 = false ->
      ceval st' (CRepeat c1 b1) st'' ->
      ceval st (CRepeat c1 b1) st''.

Notation "c1 '/' st '\\' st'" := (ceval st c1 st')
                                 (at level 40, st at level 39).

Theorem ceval_deterministic: forall c st st1 st2,
     c / st \\ st1  ->
     c / st \\ st2 ->
     st1 = st2.
Proof.
  intros c st st1 st2 E1 E2;
  generalize dependent st2;
  induction E1;
           intros st2 E2; inv E2; try find_rwinv; repeat find_eqn; auto.
  - (* E_RepeatEnd *)
    + (* b evaluates to false (contradiction) *)
       find_rwinv.
       (* oops: why didn't [find_rwinv] solve this for us already?
          answer: we did things in the wrong order. *)
  - (* E_RepeatLoop *)
     + (* b evaluates to true (contradiction) *)
        find_rwinv.
Qed.

Theorem ceval_deterministic': forall c st st1 st2,
     c / st \\ st1  ->
     c / st \\ st2 ->
     st1 = st2.
Proof.
  intros c st st1 st2 E1 E2;
  generalize dependent st2;
  induction E1;
           intros st2 E2; inv E2; repeat find_eqn; try find_rwinv; auto.
Qed.

End Repeat.

(** These examples just give a flavor of what "hyper-automation" can
    do.  The details of using [match goal] are a bit tricky, and
    debugging scripts using it is not very pleasant.  But it is well
    worth adding at least simple uses to your proofs to avoid tedium
    and to "future proof" your scripts. *)

(** $Date: 2016-05-26 12:03:56 -0400 (Thu, 26 May 2016) $ *)
