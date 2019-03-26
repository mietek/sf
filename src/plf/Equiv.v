(** * Equiv: Program Equivalence *)

Set Warnings "-notation-overridden,-parsing".
From PLF Require Import Maps.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Arith.EqNat.
From Coq Require Import omega.Omega.
From Coq Require Import Lists.List.
From Coq Require Import Logic.FunctionalExtensionality.
Import ListNotations.
From PLF Require Import Imp.

(** *** Some Advice for Working on Exercises:

    - Most of the Coq proofs we ask you to do are similar to proofs
      that we've provided.  Before starting to work on exercises
      problems, take the time to work through our proofs (both
      informally and in Coq) and make sure you understand them in
      detail.  This will save you a lot of time.

    - The Coq proofs we're doing now are sufficiently complicated that
      it is more or less impossible to complete them by random
      experimentation or "following your nose."  You need to start
      with an idea about why the property is true and how the proof is
      going to go.  The best way to do this is to write out at least a
      sketch of an informal proof on paper -- one that intuitively
      convinces you of the truth of the theorem -- before starting to
      work on the formal one.  Alternately, grab a friend and try to
      convince them that the theorem is true; then try to formalize
      your explanation.

    - Use automation to save work!  The proofs in this chapter can get
      pretty long if you try to write out all the cases explicitly. *)

(* ################################################################# *)
(** * Behavioral Equivalence *)

(** In an earlier chapter, we investigated the correctness of a very
    simple program transformation: the [optimize_0plus] function.  The
    programming language we were considering was the first version of
    the language of arithmetic expressions -- with no variables -- so
    in that setting it was very easy to define what it means for a
    program transformation to be correct: it should always yield a
    program that evaluates to the same number as the original.

    To talk about the correctness of program transformations for the
    full Imp language, in particular assignment, we need to consider
    the role of variables and state. *)

(* ================================================================= *)
(** ** Definitions *)

(** For [aexp]s and [bexp]s with variables, the definition we want is
    clear: Two [aexp]s or [bexp]s are _behaviorally equivalent_ if
    they evaluate to the same result in every state. *)

Definition aequiv (a1 a2 : aexp) : Prop :=
  forall (st : state),
    aeval st a1 = aeval st a2.

Definition bequiv (b1 b2 : bexp) : Prop :=
  forall (st : state),
    beval st b1 = beval st b2.

(** Here are some simple examples of equivalences of arithmetic
    and boolean expressions. *)

Theorem aequiv_example: aequiv (X - X) 0.
Proof.
  intros st. simpl. omega.
Qed.

Theorem bequiv_example: bequiv (X - X = 0)%imp true.
Proof.
  intros st. unfold beval.
  rewrite aequiv_example. reflexivity.
Qed.

(** For commands, the situation is a little more subtle.  We can't
    simply say "two commands are behaviorally equivalent if they
    evaluate to the same ending state whenever they are started in the
    same initial state," because some commands, when run in some
    starting states, don't terminate in any final state at all!  What
    we need instead is this: two commands are behaviorally equivalent
    if, for any given starting state, they either (1) both diverge
    or (2) both terminate in the same final state.  A compact way to
    express this is "if the first one terminates in a particular state
    then so does the second, and vice versa." *)

Definition cequiv (c1 c2 : com) : Prop :=
  forall (st st' : state),
    (st =[ c1 ]=> st') <-> (st =[ c2 ]=> st').

(* ================================================================= *)
(** ** Simple Examples *)

(** For examples of command equivalence, let's start by looking at
    some trivial program transformations involving [SKIP]: *)

Theorem skip_left : forall c,
  cequiv
    (SKIP;; c)
    c.
Proof.
  (* WORKED IN CLASS *)
  intros c st st'.
  split; intros H.
  - (* -> *)
    inversion H; subst.
    inversion H2. subst.
    assumption.
  - (* <- *)
    apply E_Seq with st.
    apply E_Skip.
    assumption.
Qed.

(** **** Exercise: 2 stars, standard (skip_right)  

    Prove that adding a [SKIP] after a command results in an
    equivalent program *)

Theorem skip_right : forall c,
  cequiv
    (c ;; SKIP)
    c.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** Similarly, here is a simple transformation that optimizes [TEST]
    commands: *)

Theorem TEST_true_simple : forall c1 c2,
  cequiv
    (TEST true THEN c1 ELSE c2 FI)
    c1.
Proof.
  intros c1 c2.
  split; intros H.
  - (* -> *)
    inversion H; subst. assumption. inversion H5.
  - (* <- *)
    apply E_IfTrue. reflexivity. assumption.  Qed.

(** Of course, no (human) programmer would write a conditional whose
    guard is literally [true].  But they might write one whose guard
    is _equivalent_ to true: 

    _Theorem_: If [b] is equivalent to [BTrue], then [TEST b THEN c1
    ELSE c2 FI] is equivalent to [c1]. 
   _Proof_:

     - ([->]) We must show, for all [st] and [st'], that if [st =[
       TEST b THEN c1 ELSE c2 FI ]=> st'] then [st =[ c1 ]=> st'].

       Proceed by cases on the rules that could possibly have been
       used to show [st =[ TEST b THEN c1 ELSE c2 FI ]=> st'], namely
       [E_IfTrue] and [E_IfFalse].

       - Suppose the final rule in the derivation of [st =[ TEST b
         THEN c1 ELSE c2 FI ]=> st'] was [E_IfTrue].  We then have,
         by the premises of [E_IfTrue], that [st =[ c1 ]=> st'].
         This is exactly what we set out to prove.

       - On the other hand, suppose the final rule in the derivation
         of [st =[ TEST b THEN c1 ELSE c2 FI ]=> st'] was [E_IfFalse].
         We then know that [beval st b = false] and [st =[ c2 ]=> st'].

         Recall that [b] is equivalent to [BTrue], i.e., forall [st],
         [beval st b = beval st BTrue].  In particular, this means
         that [beval st b = true], since [beval st BTrue = true].  But
         this is a contradiction, since [E_IfFalse] requires that
         [beval st b = false].  Thus, the final rule could not have
         been [E_IfFalse].

     - ([<-]) We must show, for all [st] and [st'], that if
       [st =[ c1 ]=> st'] then
       [st =[ TEST b THEN c1 ELSE c2 FI ]=> st'].

       Since [b] is equivalent to [BTrue], we know that [beval st b] =
       [beval st BTrue] = [true].  Together with the assumption that
       [st =[ c1 ]=> st'], we can apply [E_IfTrue] to derive
       [st =[ TEST b THEN c1 ELSE c2 FI ]=> st'].  []

   Here is the formal version of this proof: *)

Theorem TEST_true: forall b c1 c2,
  bequiv b BTrue  ->
  cequiv
    (TEST b THEN c1 ELSE c2 FI)
    c1.
Proof.
  intros b c1 c2 Hb.
  split; intros H.
  - (* -> *)
    inversion H; subst.
    + (* b evaluates to true *)
      assumption.
    + (* b evaluates to false (contradiction) *)
      unfold bequiv in Hb. simpl in Hb.
      rewrite Hb in H5.
      inversion H5.
  - (* <- *)
    apply E_IfTrue; try assumption.
    unfold bequiv in Hb. simpl in Hb.
    rewrite Hb. reflexivity.  Qed.

(** **** Exercise: 2 stars, standard, recommended (TEST_false)  *)
Theorem TEST_false : forall b c1 c2,
  bequiv b BFalse ->
  cequiv
    (TEST b THEN c1 ELSE c2 FI)
    c2.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, standard (swap_if_branches)  

    Show that we can swap the branches of an IF if we also negate its
    guard. *)

Theorem swap_if_branches : forall b e1 e2,
  cequiv
    (TEST b THEN e1 ELSE e2 FI)
    (TEST BNot b THEN e2 ELSE e1 FI).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** For [WHILE] loops, we can give a similar pair of theorems.  A loop
    whose guard is equivalent to [BFalse] is equivalent to [SKIP],
    while a loop whose guard is equivalent to [BTrue] is equivalent to
    [WHILE BTrue DO SKIP END] (or any other non-terminating program).
    The first of these facts is easy. *)

Theorem WHILE_false : forall b c,
  bequiv b BFalse ->
  cequiv
    (WHILE b DO c END)
    SKIP.
Proof.
  intros b c Hb. split; intros H.
  - (* -> *)
    inversion H; subst.
    + (* E_WhileFalse *)
      apply E_Skip.
    + (* E_WhileTrue *)
      rewrite Hb in H2. inversion H2.
  - (* <- *)
    inversion H; subst.
    apply E_WhileFalse.
    rewrite Hb.
    reflexivity.  Qed.

(** **** Exercise: 2 stars, advanced, optional (WHILE_false_informal)  

    Write an informal proof of [WHILE_false].

(* FILL IN HERE *)

    [] *)

(** To prove the second fact, we need an auxiliary lemma stating that
    [WHILE] loops whose guards are equivalent to [BTrue] never
    terminate. *)

(** _Lemma_: If [b] is equivalent to [BTrue], then it cannot be
    the case that [st =[ WHILE b DO c END ]=> st'].

    _Proof_: Suppose that [st =[ WHILE b DO c END ]=> st'].  We show,
    by induction on a derivation of [st =[ WHILE b DO c END ]=> st'],
    that this assumption leads to a contradiction. The only two cases
    to consider are [E_WhileFalse] and [E_WhileTrue], the others
    are contradictory.

    - Suppose [st =[ WHILE b DO c END ]=> st'] is proved using rule
      [E_WhileFalse].  Then by assumption [beval st b = false].  But
      this contradicts the assumption that [b] is equivalent to
      [BTrue].

    - Suppose [st =[ WHILE b DO c END ]=> st'] is proved using rule
      [E_WhileTrue].  We must have that:

      1. [beval st b = true],
      2. there is some [st0] such that [st =[ c ]=> st0] and
         [st0 =[ WHILE b DO c END ]=> st'],
      3. and we are given the induction hypothesis that
         [st0 =[ WHILE b DO c END ]=> st'] leads to a contradiction,

      We obtain a contradiction by 2 and 3. [] *)

Lemma WHILE_true_nonterm : forall b c st st',
  bequiv b BTrue ->
  ~( st =[ WHILE b DO c END ]=> st' ).
Proof.
  (* WORKED IN CLASS *)
  intros b c st st' Hb.
  intros H.
  remember (WHILE b DO c END)%imp as cw eqn:Heqcw.
  induction H;
  (* Most rules don't apply; we rule them out by inversion: *)
  inversion Heqcw; subst; clear Heqcw.
  (* The two interesting cases are the ones for WHILE loops: *)
  - (* E_WhileFalse *) (* contradictory -- b is always true! *)
    unfold bequiv in Hb.
    (* [rewrite] is able to instantiate the quantifier in [st] *)
    rewrite Hb in H. inversion H.
  - (* E_WhileTrue *) (* immediate from the IH *)
    apply IHceval2. reflexivity.  Qed.

(** **** Exercise: 2 stars, standard, optional (WHILE_true_nonterm_informal)  

    Explain what the lemma [WHILE_true_nonterm] means in English.

(* FILL IN HERE *)

    [] *)

(** **** Exercise: 2 stars, standard, recommended (WHILE_true)  

    Prove the following theorem. _Hint_: You'll want to use
    [WHILE_true_nonterm] here. *)

Theorem WHILE_true : forall b c,
  bequiv b true  ->
  cequiv
    (WHILE b DO c END)
    (WHILE true DO SKIP END).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** A more interesting fact about [WHILE] commands is that any number
    of copies of the body can be "unrolled" without changing meaning.
    Loop unrolling is a common transformation in real compilers. *)

Theorem loop_unrolling : forall b c,
  cequiv
    (WHILE b DO c END)
    (TEST b THEN (c ;; WHILE b DO c END) ELSE SKIP FI).
Proof.
  (* WORKED IN CLASS *)
  intros b c st st'.
  split; intros Hce.
  - (* -> *)
    inversion Hce; subst.
    + (* loop doesn't run *)
      apply E_IfFalse. assumption. apply E_Skip.
    + (* loop runs *)
      apply E_IfTrue. assumption.
      apply E_Seq with (st' := st'0). assumption. assumption.
  - (* <- *)
    inversion Hce; subst.
    + (* loop runs *)
      inversion H5; subst.
      apply E_WhileTrue with (st' := st'0).
      assumption. assumption. assumption.
    + (* loop doesn't run *)
      inversion H5; subst. apply E_WhileFalse. assumption.  Qed.

(** **** Exercise: 2 stars, standard, optional (seq_assoc)  *)
Theorem seq_assoc : forall c1 c2 c3,
  cequiv ((c1;;c2);;c3) (c1;;(c2;;c3)).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** Proving program properties involving assignments is one place
    where the fact that program states are treated
    extensionally (e.g., [x !-> m x ; m] and [m] are equal maps) comes
    in handy. *)

Theorem identity_assignment : forall x,
  cequiv
    (x ::= x)
    SKIP.
Proof.
  intros.
  split; intro H; inversion H; subst.
  - (* -> *)
    rewrite t_update_same.
    apply E_Skip.
  - (* <- *)
    assert (Hx : st' =[ x ::= x ]=> (x !-> st' x ; st')).
    { apply E_Ass. reflexivity. }
    rewrite t_update_same in Hx.
    apply Hx.
Qed.

(** **** Exercise: 2 stars, standard, recommended (assign_aequiv)  *)
Theorem assign_aequiv : forall (x : string) e,
  aequiv x e ->
  cequiv SKIP (x ::= e).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard (equiv_classes)  *)

(** Given the following programs, group together those that are
    equivalent in Imp. Your answer should be given as a list of lists,
    where each sub-list represents a group of equivalent programs. For
    example, if you think programs (a) through (h) are all equivalent
    to each other, but not to (i), your answer should look like this:

       [ [prog_a;prog_b;prog_c;prog_d;prog_e;prog_f;prog_g;prog_h] ;
         [prog_i] ]

    Write down your answer below in the definition of
    [equiv_classes]. *)

Definition prog_a : com :=
  (WHILE ~(X <= 0) DO
    X ::= X + 1
  END)%imp.

Definition prog_b : com :=
  (TEST X = 0 THEN
    X ::= X + 1;;
    Y ::= 1
  ELSE
    Y ::= 0
  FI;;
  X ::= X - Y;;
  Y ::= 0)%imp.

Definition prog_c : com :=
  SKIP%imp.

Definition prog_d : com :=
  (WHILE ~(X = 0) DO
    X ::= (X * Y) + 1
  END)%imp.

Definition prog_e : com :=
  (Y ::= 0)%imp.

Definition prog_f : com :=
  (Y ::= X + 1;;
  WHILE ~(X = Y) DO
    Y ::= X + 1
  END)%imp.

Definition prog_g : com :=
  (WHILE true DO
    SKIP
  END)%imp.

Definition prog_h : com :=
  (WHILE ~(X = X) DO
    X ::= X + 1
  END)%imp.

Definition prog_i : com :=
  (WHILE ~(X = Y) DO
    X ::= Y + 1
  END)%imp.

Definition equiv_classes : list (list com)
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

(* Do not modify the following line: *)
Definition manual_grade_for_equiv_classes : option (nat*string) := None.
(** [] *)

(* ################################################################# *)
(** * Properties of Behavioral Equivalence *)

(** We next consider some fundamental properties of program
    equivalence. *)

(* ================================================================= *)
(** ** Behavioral Equivalence Is an Equivalence *)

(** First, we verify that the equivalences on [aexps], [bexps], and
    [com]s really are _equivalences_ -- i.e., that they are reflexive,
    symmetric, and transitive.  The proofs are all easy. *)

Lemma refl_aequiv : forall (a : aexp), aequiv a a.
Proof.
  intros a st. reflexivity.  Qed.

Lemma sym_aequiv : forall (a1 a2 : aexp),
  aequiv a1 a2 -> aequiv a2 a1.
Proof.
  intros a1 a2 H. intros st. symmetry. apply H.  Qed.

Lemma trans_aequiv : forall (a1 a2 a3 : aexp),
  aequiv a1 a2 -> aequiv a2 a3 -> aequiv a1 a3.
Proof.
  unfold aequiv. intros a1 a2 a3 H12 H23 st.
  rewrite (H12 st). rewrite (H23 st). reflexivity.  Qed.

Lemma refl_bequiv : forall (b : bexp), bequiv b b.
Proof.
  unfold bequiv. intros b st. reflexivity.  Qed.

Lemma sym_bequiv : forall (b1 b2 : bexp),
  bequiv b1 b2 -> bequiv b2 b1.
Proof.
  unfold bequiv. intros b1 b2 H. intros st. symmetry. apply H.  Qed.

Lemma trans_bequiv : forall (b1 b2 b3 : bexp),
  bequiv b1 b2 -> bequiv b2 b3 -> bequiv b1 b3.
Proof.
  unfold bequiv. intros b1 b2 b3 H12 H23 st.
  rewrite (H12 st). rewrite (H23 st). reflexivity.  Qed.

Lemma refl_cequiv : forall (c : com), cequiv c c.
Proof.
  unfold cequiv. intros c st st'. apply iff_refl.  Qed.

Lemma sym_cequiv : forall (c1 c2 : com),
  cequiv c1 c2 -> cequiv c2 c1.
Proof.
  unfold cequiv. intros c1 c2 H st st'.
  assert (st =[ c1 ]=> st' <-> st =[ c2 ]=> st') as H'.
  { (* Proof of assertion *) apply H. }
  apply iff_sym. assumption.
Qed.

Lemma iff_trans : forall (P1 P2 P3 : Prop),
  (P1 <-> P2) -> (P2 <-> P3) -> (P1 <-> P3).
Proof.
  intros P1 P2 P3 H12 H23.
  inversion H12. inversion H23.
  split; intros A.
    apply H1. apply H. apply A.
    apply H0. apply H2. apply A.  Qed.

Lemma trans_cequiv : forall (c1 c2 c3 : com),
  cequiv c1 c2 -> cequiv c2 c3 -> cequiv c1 c3.
Proof.
  unfold cequiv. intros c1 c2 c3 H12 H23 st st'.
  apply iff_trans with (st =[ c2 ]=> st'). apply H12. apply H23.  Qed.

(* ================================================================= *)
(** ** Behavioral Equivalence Is a Congruence *)

(** Less obviously, behavioral equivalence is also a _congruence_.
    That is, the equivalence of two subprograms implies the
    equivalence of the larger programs in which they are embedded:

              aequiv a1 a1'
      -----------------------------
      cequiv (x ::= a1) (x ::= a1')

              cequiv c1 c1'
              cequiv c2 c2'
         --------------------------
         cequiv (c1;;c2) (c1';;c2')

    ... and so on for the other forms of commands. *)

(** (Note that we are using the inference rule notation here not
    as part of a definition, but simply to write down some valid
    implications in a readable format. We prove these implications
    below.) *)

(** We will see a concrete example of why these congruence
    properties are important in the following section (in the proof of
    [fold_constants_com_sound]), but the main idea is that they allow
    us to replace a small part of a large program with an equivalent
    small part and know that the whole large programs are equivalent
    _without_ doing an explicit proof about the non-varying parts --
    i.e., the "proof burden" of a small change to a large program is
    proportional to the size of the change, not the program. *)

Theorem CAss_congruence : forall x a1 a1',
  aequiv a1 a1' ->
  cequiv (CAss x a1) (CAss x a1').
Proof.
  intros x a1 a2 Heqv st st'.
  split; intros Hceval.
  - (* -> *)
    inversion Hceval. subst. apply E_Ass.
    rewrite Heqv. reflexivity.
  - (* <- *)
    inversion Hceval. subst. apply E_Ass.
    rewrite Heqv. reflexivity.  Qed.

(** The congruence property for loops is a little more interesting,
    since it requires induction.

    _Theorem_: Equivalence is a congruence for [WHILE] -- that is, if
    [b1] is equivalent to [b1'] and [c1] is equivalent to [c1'], then
    [WHILE b1 DO c1 END] is equivalent to [WHILE b1' DO c1' END].

    _Proof_: Suppose [b1] is equivalent to [b1'] and [c1] is
    equivalent to [c1'].  We must show, for every [st] and [st'], that
    [st =[ WHILE b1 DO c1 END ]=> st'] iff [st =[ WHILE b1' DO c1'
    END ]=> st'].  We consider the two directions separately.

      - ([->]) We show that [st =[ WHILE b1 DO c1 END ]=> st'] implies
        [st =[ WHILE b1' DO c1' END ]=> st'], by induction on a
        derivation of [st =[ WHILE b1 DO c1 END ]=> st'].  The only
        nontrivial cases are when the final rule in the derivation is
        [E_WhileFalse] or [E_WhileTrue].

          - [E_WhileFalse]: In this case, the form of the rule gives us
            [beval st b1 = false] and [st = st'].  But then, since
            [b1] and [b1'] are equivalent, we have [beval st b1' =
            false], and [E_WhileFalse] applies, giving us
            [st =[ WHILE b1' DO c1' END ]=> st'], as required.

          - [E_WhileTrue]: The form of the rule now gives us [beval st
            b1 = true], with [st =[ c1 ]=> st'0] and [st'0 =[ WHILE
            b1 DO c1 END ]=> st'] for some state [st'0], with the
            induction hypothesis [st'0 =[ WHILE b1' DO c1' END ]=>
            st'].

            Since [c1] and [c1'] are equivalent, we know that [st =[
            c1' ]=> st'0].  And since [b1] and [b1'] are equivalent,
            we have [beval st b1' = true].  Now [E_WhileTrue] applies,
            giving us [st =[ WHILE b1' DO c1' END ]=> st'], as
            required.

      - ([<-]) Similar. [] *)

Theorem CWhile_congruence : forall b1 b1' c1 c1',
  bequiv b1 b1' -> cequiv c1 c1' ->
  cequiv (WHILE b1 DO c1 END) (WHILE b1' DO c1' END).
Proof.
  (* WORKED IN CLASS *)
  unfold bequiv,cequiv.
  intros b1 b1' c1 c1' Hb1e Hc1e st st'.
  split; intros Hce.
  - (* -> *)
    remember (WHILE b1 DO c1 END)%imp as cwhile
      eqn:Heqcwhile.
    induction Hce; inversion Heqcwhile; subst.
    + (* E_WhileFalse *)
      apply E_WhileFalse. rewrite <- Hb1e. apply H.
    + (* E_WhileTrue *)
      apply E_WhileTrue with (st' := st').
      * (* show loop runs *) rewrite <- Hb1e. apply H.
      * (* body execution *)
        apply (Hc1e st st').  apply Hce1.
      * (* subsequent loop execution *)
        apply IHHce2. reflexivity.
  - (* <- *)
    remember (WHILE b1' DO c1' END)%imp as c'while
      eqn:Heqc'while.
    induction Hce; inversion Heqc'while; subst.
    + (* E_WhileFalse *)
      apply E_WhileFalse. rewrite -> Hb1e. apply H.
    + (* E_WhileTrue *)
      apply E_WhileTrue with (st' := st').
      * (* show loop runs *) rewrite -> Hb1e. apply H.
      * (* body execution *)
        apply (Hc1e st st').  apply Hce1.
      * (* subsequent loop execution *)
        apply IHHce2. reflexivity.  Qed.

(** **** Exercise: 3 stars, standard, optional (CSeq_congruence)  *)
Theorem CSeq_congruence : forall c1 c1' c2 c2',
  cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv (c1;;c2) (c1';;c2').
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, standard (CIf_congruence)  *)
Theorem CIf_congruence : forall b b' c1 c1' c2 c2',
  bequiv b b' -> cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv (TEST b THEN c1 ELSE c2 FI)
         (TEST b' THEN c1' ELSE c2' FI).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** For example, here are two equivalent programs and a proof of their
    equivalence... *)

Example congruence_example:
  cequiv
    (* Program 1: *)
    (X ::= 0;;
     TEST X = 0
     THEN
       Y ::= 0
     ELSE
       Y ::= 42
     FI)
    (* Program 2: *)
    (X ::= 0;;
     TEST X = 0
     THEN
       Y ::= X - X   (* <--- Changed here *)
     ELSE
       Y ::= 42
     FI).
Proof.
  apply CSeq_congruence.
  - apply refl_cequiv.
  - apply CIf_congruence.
    + apply refl_bequiv.
    + apply CAss_congruence. unfold aequiv. simpl.
      * symmetry. apply minus_diag.
    + apply refl_cequiv.
Qed.

(** **** Exercise: 3 stars, advanced, optional (not_congr)  

    We've shown that the [cequiv] relation is both an equivalence and
    a congruence on commands.  Can you think of a relation on commands
    that is an equivalence but _not_ a congruence? *)

(* FILL IN HERE 

    [] *)

(* ################################################################# *)
(** * Program Transformations *)

(** A _program transformation_ is a function that takes a program as
    input and produces some variant of the program as output.
    Compiler optimizations such as constant folding are a canonical
    example, but there are many others. *)

(** A program transformation is _sound_ if it preserves the
    behavior of the original program. *)

Definition atrans_sound (atrans : aexp -> aexp) : Prop :=
  forall (a : aexp),
    aequiv a (atrans a).

Definition btrans_sound (btrans : bexp -> bexp) : Prop :=
  forall (b : bexp),
    bequiv b (btrans b).

Definition ctrans_sound (ctrans : com -> com) : Prop :=
  forall (c : com),
    cequiv c (ctrans c).

(* ================================================================= *)
(** ** The Constant-Folding Transformation *)

(** An expression is _constant_ when it contains no variable
    references.

    Constant folding is an optimization that finds constant
    expressions and replaces them by their values. *)

Fixpoint fold_constants_aexp (a : aexp) : aexp :=
  match a with
  | ANum n       => ANum n
  | AId x        => AId x
  | APlus a1 a2  =>
    match (fold_constants_aexp a1, 
           fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (n1 + n2)
    | (a1', a2') => APlus a1' a2'
    end
  | AMinus a1 a2 =>
    match (fold_constants_aexp a1, 
           fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (n1 - n2)
    | (a1', a2') => AMinus a1' a2'
    end
  | AMult a1 a2  =>
    match (fold_constants_aexp a1, 
           fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (n1 * n2)
    | (a1', a2') => AMult a1' a2'
    end
  end.

Example fold_aexp_ex1 :
    fold_constants_aexp ((1 + 2) * X) 
  = (3 * X)%imp.
Proof. reflexivity. Qed.

(** Note that this version of constant folding doesn't eliminate
    trivial additions, etc. -- we are focusing attention on a single
    optimization for the sake of simplicity.  It is not hard to
    incorporate other ways of simplifying expressions; the definitions
    and proofs just get longer. *)

Example fold_aexp_ex2 :
  fold_constants_aexp (X - ((0 * 6) + Y))%imp = (X - (0 + Y))%imp.
Proof. reflexivity. Qed.

(** Not only can we lift [fold_constants_aexp] to [bexp]s (in the
    [BEq] and [BLe] cases); we can also look for constant _boolean_
    expressions and evaluate them in-place. *)

Fixpoint fold_constants_bexp (b : bexp) : bexp :=
  match b with
  | BTrue        => BTrue
  | BFalse       => BFalse
  | BEq a1 a2  =>
      match (fold_constants_aexp a1, 
             fold_constants_aexp a2) with
      | (ANum n1, ANum n2) =>
          if n1 =? n2 then BTrue else BFalse
      | (a1', a2') =>
          BEq a1' a2'
      end
  | BLe a1 a2  =>
      match (fold_constants_aexp a1, 
             fold_constants_aexp a2) with
      | (ANum n1, ANum n2) =>
          if n1 <=? n2 then BTrue else BFalse
      | (a1', a2') =>
          BLe a1' a2'
      end
  | BNot b1  =>
      match (fold_constants_bexp b1) with
      | BTrue => BFalse
      | BFalse => BTrue
      | b1' => BNot b1'
      end
  | BAnd b1 b2  =>
      match (fold_constants_bexp b1, 
             fold_constants_bexp b2) with
      | (BTrue, BTrue) => BTrue
      | (BTrue, BFalse) => BFalse
      | (BFalse, BTrue) => BFalse
      | (BFalse, BFalse) => BFalse
      | (b1', b2') => BAnd b1' b2'
      end
  end.

Example fold_bexp_ex1 :
  fold_constants_bexp (true && ~(false && true))%imp 
  = true.
Proof. reflexivity. Qed.

Example fold_bexp_ex2 :
  fold_constants_bexp ((X = Y) && (0 = (2 - (1 + 1))))%imp
  = ((X = Y) && true)%imp.
Proof. reflexivity. Qed.

(** To fold constants in a command, we apply the appropriate folding
    functions on all embedded expressions. *)

Open Scope imp.
Fixpoint fold_constants_com (c : com) : com :=
  match c with
  | SKIP      =>
      SKIP
  | x ::= a   =>
      x ::= (fold_constants_aexp a)
  | c1 ;; c2  =>
      (fold_constants_com c1) ;; (fold_constants_com c2)
  | TEST b THEN c1 ELSE c2 FI =>
      match fold_constants_bexp b with
      | BTrue  => fold_constants_com c1
      | BFalse => fold_constants_com c2
      | b' => TEST b' THEN fold_constants_com c1
                     ELSE fold_constants_com c2 FI
      end
  | WHILE b DO c END =>
      match fold_constants_bexp b with
      | BTrue => WHILE BTrue DO SKIP END
      | BFalse => SKIP
      | b' => WHILE b' DO (fold_constants_com c) END
      end
  end.
Close Scope imp.

Example fold_com_ex1 :
  fold_constants_com
    (* Original program: *)
    (X ::= 4 + 5;;
     Y ::= X - 3;;
     TEST (X - Y) = (2 + 4) THEN SKIP
     ELSE Y ::= 0 FI;;
     TEST 0 <= (4 - (2 + 1)) THEN Y ::= 0
     ELSE SKIP FI;;
     WHILE Y = 0 DO
       X ::= X + 1
     END)%imp
  = (* After constant folding: *)
    (X ::= 9;;
     Y ::= X - 3;;
     TEST (X - Y) = 6 THEN SKIP 
     ELSE Y ::= 0 FI;;
     Y ::= 0;;
     WHILE Y = 0 DO
       X ::= X + 1
     END)%imp.
Proof. reflexivity. Qed.

(* ================================================================= *)
(** ** Soundness of Constant Folding *)

(** Now we need to show that what we've done is correct. *)

(** Here's the proof for arithmetic expressions: *)

Theorem fold_constants_aexp_sound :
  atrans_sound fold_constants_aexp.
Proof.
  unfold atrans_sound. intros a. unfold aequiv. intros st.
  induction a; simpl;
    (* ANum and AId follow immediately *)
    try reflexivity;
    (* APlus, AMinus, and AMult follow from the IH
       and the observation that
              aeval st (APlus a1 a2)
            = ANum ((aeval st a1) + (aeval st a2))
            = aeval st (ANum ((aeval st a1) + (aeval st a2)))
       (and similarly for AMinus/minus and AMult/mult) *)
    try (destruct (fold_constants_aexp a1);
         destruct (fold_constants_aexp a2);
         rewrite IHa1; rewrite IHa2; reflexivity). Qed.

(** **** Exercise: 3 stars, standard, optional (fold_bexp_Eq_informal)  

    Here is an informal proof of the [BEq] case of the soundness
    argument for boolean expression constant folding.  Read it
    carefully and compare it to the formal proof that follows.  Then
    fill in the [BLe] case of the formal proof (without looking at the
    [BEq] case, if possible).

   _Theorem_: The constant folding function for booleans,
   [fold_constants_bexp], is sound.

   _Proof_: We must show that [b] is equivalent to [fold_constants_bexp b],
   for all boolean expressions [b].  Proceed by induction on [b].  We
   show just the case where [b] has the form [BEq a1 a2].

   In this case, we must show

       beval st (BEq a1 a2)
     = beval st (fold_constants_bexp (BEq a1 a2)).

   There are two cases to consider:

     - First, suppose [fold_constants_aexp a1 = ANum n1] and
       [fold_constants_aexp a2 = ANum n2] for some [n1] and [n2].

       In this case, we have

           fold_constants_bexp (BEq a1 a2)
         = if n1 =? n2 then BTrue else BFalse

       and

           beval st (BEq a1 a2)
         = (aeval st a1) =? (aeval st a2).

       By the soundness of constant folding for arithmetic
       expressions (Lemma [fold_constants_aexp_sound]), we know

           aeval st a1
         = aeval st (fold_constants_aexp a1)
         = aeval st (ANum n1)
         = n1

       and

           aeval st a2
         = aeval st (fold_constants_aexp a2)
         = aeval st (ANum n2)
         = n2,

       so

           beval st (BEq a1 a2)
         = (aeval a1) =? (aeval a2)
         = n1 =? n2.

       Also, it is easy to see (by considering the cases [n1 = n2] and
       [n1 <> n2] separately) that

           beval st (if n1 =? n2 then BTrue else BFalse)
         = if n1 =? n2 then beval st BTrue else beval st BFalse
         = if n1 =? n2 then true else false
         = n1 =? n2.

       So

           beval st (BEq a1 a2)
         = n1 =? n2.
         = beval st (if n1 =? n2 then BTrue else BFalse),

       as required.

     - Otherwise, one of [fold_constants_aexp a1] and
       [fold_constants_aexp a2] is not a constant.  In this case, we
       must show

           beval st (BEq a1 a2)
         = beval st (BEq (fold_constants_aexp a1)
                         (fold_constants_aexp a2)),

       which, by the definition of [beval], is the same as showing

           (aeval st a1) =? (aeval st a2)
         = (aeval st (fold_constants_aexp a1)) =?
                   (aeval st (fold_constants_aexp a2)).

       But the soundness of constant folding for arithmetic
       expressions ([fold_constants_aexp_sound]) gives us

         aeval st a1 = aeval st (fold_constants_aexp a1)
         aeval st a2 = aeval st (fold_constants_aexp a2),

       completing the case.  [] *)

Theorem fold_constants_bexp_sound:
  btrans_sound fold_constants_bexp.
Proof.
  unfold btrans_sound. intros b. unfold bequiv. intros st.
  induction b;
    (* BTrue and BFalse are immediate *)
    try reflexivity.
  - (* BEq *)
    simpl.

(** (Doing induction when there are a lot of constructors makes
    specifying variable names a chore, but Coq doesn't always
    choose nice variable names.  We can rename entries in the
    context with the [rename] tactic: [rename a into a1] will
    change [a] to [a1] in the current goal and context.) *)

    remember (fold_constants_aexp a1) as a1' eqn:Heqa1'.
    remember (fold_constants_aexp a2) as a2' eqn:Heqa2'.
    replace (aeval st a1) with (aeval st a1') by
       (subst a1'; rewrite <- fold_constants_aexp_sound; reflexivity).
    replace (aeval st a2) with (aeval st a2') by
       (subst a2'; rewrite <- fold_constants_aexp_sound; reflexivity).
    destruct a1'; destruct a2'; try reflexivity.

    (* The only interesting case is when both a1 and a2
       become constants after folding *)
      simpl. destruct (n =? n0); reflexivity.
  - (* BLe *)
    (* FILL IN HERE *) admit.
  - (* BNot *)
    simpl. remember (fold_constants_bexp b) as b' eqn:Heqb'.
    rewrite IHb.
    destruct b'; reflexivity.
  - (* BAnd *)
    simpl.
    remember (fold_constants_bexp b1) as b1' eqn:Heqb1'.
    remember (fold_constants_bexp b2) as b2' eqn:Heqb2'.
    rewrite IHb1. rewrite IHb2.
    destruct b1'; destruct b2'; reflexivity.
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, standard (fold_constants_com_sound)  

    Complete the [WHILE] case of the following proof. *)

Theorem fold_constants_com_sound :
  ctrans_sound fold_constants_com.
Proof.
  unfold ctrans_sound. intros c.
  induction c; simpl.
  - (* SKIP *) apply refl_cequiv.
  - (* ::= *) apply CAss_congruence.
              apply fold_constants_aexp_sound.
  - (* ;; *) apply CSeq_congruence; assumption.
  - (* TEST *)
    assert (bequiv b (fold_constants_bexp b)). {
      apply fold_constants_bexp_sound. }
    destruct (fold_constants_bexp b) eqn:Heqb;
      try (apply CIf_congruence; assumption).
      (* (If the optimization doesn't eliminate the if, then the
          result is easy to prove from the IH and
          [fold_constants_bexp_sound].) *)
    + (* b always true *)
      apply trans_cequiv with c1; try assumption.
      apply TEST_true; assumption.
    + (* b always false *)
      apply trans_cequiv with c2; try assumption.
      apply TEST_false; assumption.
  - (* WHILE *)
    (* FILL IN HERE *) Admitted.
(** [] *)

(* ----------------------------------------------------------------- *)
(** *** Soundness of (0 + n) Elimination, Redux *)

(** **** Exercise: 4 stars, advanced, optional (optimize_0plus)  

    Recall the definition [optimize_0plus] from the [Imp] chapter of _Logical
    Foundations_:

    Fixpoint optimize_0plus (e:aexp) : aexp :=
      match e with
      | ANum n =>
          ANum n
      | APlus (ANum 0) e2 =>
          optimize_0plus e2
      | APlus e1 e2 =>
          APlus (optimize_0plus e1) (optimize_0plus e2)
      | AMinus e1 e2 =>
          AMinus (optimize_0plus e1) (optimize_0plus e2)
      | AMult e1 e2 =>
          AMult (optimize_0plus e1) (optimize_0plus e2)
      end.

   Note that this function is defined over the old [aexp]s,
   without states.

   Write a new version of this function that accounts for variables,
   plus analogous ones for [bexp]s and commands:

     optimize_0plus_aexp
     optimize_0plus_bexp
     optimize_0plus_com

   Prove that these three functions are sound, as we did for
   [fold_constants_*].  Make sure you use the congruence lemmas in
   the proof of [optimize_0plus_com] -- otherwise it will be _long_!

   Then define an optimizer on commands that first folds
   constants (using [fold_constants_com]) and then eliminates [0 + n]
   terms (using [optimize_0plus_com]).

   - Give a meaningful example of this optimizer's output.

   - Prove that the optimizer is sound.  (This part should be _very_
     easy.)  *)

(* FILL IN HERE 

    [] *)

(* ################################################################# *)
(** * Proving Inequivalence *)

(** Suppose that [c1] is a command of the form [X ::= a1;; Y ::= a2]
    and [c2] is the command [X ::= a1;; Y ::= a2'], where [a2'] is
    formed by substituting [a1] for all occurrences of [X] in [a2].
    For example, [c1] and [c2] might be:

       c1  =  (X ::= 42 + 53;;
               Y ::= Y + X)
       c2  =  (X ::= 42 + 53;;
               Y ::= Y + (42 + 53))

    Clearly, this _particular_ [c1] and [c2] are equivalent.  Is this
    true in general? *)

(** We will see in a moment that it is not, but it is worthwhile
    to pause, now, and see if you can find a counter-example on your
    own. *)

(** More formally, here is the function that substitutes an arithmetic
    expression [u] for each occurrence of a given variable [x] in
    another expression [a]: *)

Fixpoint subst_aexp (x : string) (u : aexp) (a : aexp) : aexp :=
  match a with
  | ANum n       =>
      ANum n
  | AId x'       =>
      if eqb_string x x' then u else AId x'
  | APlus a1 a2  =>
      APlus (subst_aexp x u a1) (subst_aexp x u a2)
  | AMinus a1 a2 =>
      AMinus (subst_aexp x u a1) (subst_aexp x u a2)
  | AMult a1 a2  =>
      AMult (subst_aexp x u a1) (subst_aexp x u a2)
  end.

Example subst_aexp_ex :
  subst_aexp X (42 + 53) (Y + X)%imp
  = (Y + (42 + 53))%imp.
Proof. reflexivity.  Qed.

(** And here is the property we are interested in, expressing the
    claim that commands [c1] and [c2] as described above are
    always equivalent.  *)

Definition subst_equiv_property := forall x1 x2 a1 a2,
  cequiv (x1 ::= a1;; x2 ::= a2)
         (x1 ::= a1;; x2 ::= subst_aexp x1 a1 a2).

(** Sadly, the property does _not_ always hold -- i.e., it is not the
    case that, for all [x1], [x2], [a1], and [a2],

      cequiv (x1 ::= a1;; x2 ::= a2)
             (x1 ::= a1;; x2 ::= subst_aexp x1 a1 a2).

    To see this, suppose (for a contradiction) that for all [x1], [x2],
    [a1], and [a2], we have

      cequiv (x1 ::= a1;; x2 ::= a2)
             (x1 ::= a1;; x2 ::= subst_aexp x1 a1 a2).

    Consider the following program:

      X ::= X + 1;; Y ::= X

    Note that

      empty_st =[ X ::= X + 1;; Y ::= X ]=> st1,

    where [st1 = (Y !-> 1 ; X !-> 1)].

    By assumption, we know that

      cequiv (X ::= X + 1;;
              Y ::= X)
             (X ::= X + 1;;
              Y ::= X + 1)

    so, by the definition of [cequiv], we have

      empty_st =[ X ::= X + 1;; Y ::= X + 1 ]=> st1.

    But we can also derive

      empty_st =[ X ::= X + 1;; Y ::= X + 1 ]=> st2,

    where [st2 = (Y !-> 2 ; X !-> 1)].  But [st1 <> st2], which is a
    contradiction, since [ceval] is deterministic!  [] *)

Theorem subst_inequiv :
  ~ subst_equiv_property.
Proof.
  unfold subst_equiv_property.
  intros Contra.

  (* Here is the counterexample: assuming that [subst_equiv_property]
     holds allows us to prove that these two programs are
     equivalent... *)
  remember (X ::= X + 1;;
            Y ::= X)%imp
      as c1.
  remember (X ::= X + 1;;
            Y ::= X + 1)%imp
      as c2.
  assert (cequiv c1 c2) by (subst; apply Contra).

  (* ... allows us to show that the command [c2] can terminate
     in two different final states:
        st1 = (Y !-> 1 ; X !-> 1)
        st2 = (Y !-> 2 ; X !-> 1). *)
  remember (Y !-> 1 ; X !-> 1) as st1.
  remember (Y !-> 2 ; X !-> 1) as st2.
  assert (H1 : empty_st =[ c1 ]=> st1);
  assert (H2 : empty_st =[ c2 ]=> st2);
  try (subst;
       apply E_Seq with (st' := (X !-> 1));
       apply E_Ass; reflexivity).
  apply H in H1.

  (* Finally, we use the fact that evaluation is deterministic
     to obtain a contradiction. *)
  assert (Hcontra : st1 = st2)
    by (apply (ceval_deterministic c2 empty_st); assumption).
  assert (Hcontra' : st1 Y = st2 Y)
    by (rewrite Hcontra; reflexivity).
  subst. inversion Hcontra'.  Qed.

(** **** Exercise: 4 stars, standard, optional (better_subst_equiv)  

    The equivalence we had in mind above was not complete nonsense --
    it was actually almost right.  To make it correct, we just need to
    exclude the case where the variable [X] occurs in the
    right-hand-side of the first assignment statement. *)

Inductive var_not_used_in_aexp (x : string) : aexp -> Prop :=
  | VNUNum : forall n, var_not_used_in_aexp x (ANum n)
  | VNUId : forall y, x <> y -> var_not_used_in_aexp x (AId y)
  | VNUPlus : forall a1 a2,
      var_not_used_in_aexp x a1 ->
      var_not_used_in_aexp x a2 ->
      var_not_used_in_aexp x (APlus a1 a2)
  | VNUMinus : forall a1 a2,
      var_not_used_in_aexp x a1 ->
      var_not_used_in_aexp x a2 ->
      var_not_used_in_aexp x (AMinus a1 a2)
  | VNUMult : forall a1 a2,
      var_not_used_in_aexp x a1 ->
      var_not_used_in_aexp x a2 ->
      var_not_used_in_aexp x (AMult a1 a2).

Lemma aeval_weakening : forall x st a ni,
  var_not_used_in_aexp x a ->
  aeval (x !-> ni ; st) a = aeval st a.
Proof.
  (* FILL IN HERE *) Admitted.

(** Using [var_not_used_in_aexp], formalize and prove a correct version
    of [subst_equiv_property]. *)

(* FILL IN HERE 

    [] *)

(** **** Exercise: 3 stars, standard (inequiv_exercise)  

    Prove that an infinite loop is not equivalent to [SKIP] *)

Theorem inequiv_exercise:
  ~ cequiv (WHILE true DO SKIP END) SKIP.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################################# *)
(** * Extended Exercise: Nondeterministic Imp *)

(** As we have seen (in theorem [ceval_deterministic] in the [Imp]
    chapter), Imp's evaluation relation is deterministic.  However,
    _non_-determinism is an important part of the definition of many
    real programming languages. For example, in many imperative
    languages (such as C and its relatives), the order in which
    function arguments are evaluated is unspecified.  The program
    fragment

      x = 0;;
      f(++x, x)

    might call [f] with arguments [(1, 0)] or [(1, 1)], depending how
    the compiler chooses to order things.  This can be a little
    confusing for programmers, but it gives the compiler writer useful
    freedom.

    In this exercise, we will extend Imp with a simple
    nondeterministic command and study how this change affects
    program equivalence.  The new command has the syntax [HAVOC X],
    where [X] is an identifier. The effect of executing [HAVOC X] is
    to assign an _arbitrary_ number to the variable [X],
    nondeterministically. For example, after executing the program:

      HAVOC Y;;
      Z ::= Y * 2

    the value of [Y] can be any number, while the value of [Z] is
    twice that of [Y] (so [Z] is always even). Note that we are not
    saying anything about the _probabilities_ of the outcomes -- just
    that there are (infinitely) many different outcomes that can
    possibly happen after executing this nondeterministic code.

    In a sense, a variable on which we do [HAVOC] roughly corresponds
    to an uninitialized variable in a low-level language like C.  After
    the [HAVOC], the variable holds a fixed but arbitrary number.  Most
    sources of nondeterminism in language definitions are there
    precisely because programmers don't care which choice is made (and
    so it is good to leave it open to the compiler to choose whichever
    will run faster).

    We call this new language _Himp_ (``Imp extended with [HAVOC]''). *)

Module Himp.

(** To formalize Himp, we first add a clause to the definition of
    commands. *)

Inductive com : Type :=
  | CSkip : com
  | CAss : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CHavoc : string -> com.                (* <--- NEW *)

Notation "'SKIP'" :=
  CSkip : imp_scope.
Notation "X '::=' a" :=
  (CAss X a) (at level 60) : imp_scope.
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity) : imp_scope.
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity) : imp_scope.
Notation "'TEST' e1 'THEN' e2 'ELSE' e3 'FI'" :=
  (CIf e1 e2 e3) (at level 80, right associativity) : imp_scope.
Notation "'HAVOC' l" :=
  (CHavoc l) (at level 60) : imp_scope.

(** **** Exercise: 2 stars, standard (himp_ceval)  

    Now, we must extend the operational semantics. We have provided
   a template for the [ceval] relation below, specifying the big-step
   semantics. What rule(s) must be added to the definition of [ceval]
   to formalize the behavior of the [HAVOC] command? *)

Reserved Notation "st '=[' c ']=>' st'" (at level 40).

Open Scope imp_scope.
Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ SKIP ]=> st
  | E_Ass  : forall st a1 n x,
      aeval st a1 = n ->
      st =[ x ::= a1 ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st  =[ c1 ]=> st'  ->
      st' =[ c2 ]=> st'' ->
      st  =[ c1 ;; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ TEST b THEN c1 ELSE c2 FI ]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ TEST b THEN c1 ELSE c2 FI ]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ WHILE b DO c END ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st  =[ c ]=> st' ->
      st' =[ WHILE b DO c END ]=> st'' ->
      st  =[ WHILE b DO c END ]=> st''
(* FILL IN HERE *)

  where "st =[ c ]=> st'" := (ceval c st st').
Close Scope imp_scope.

(** As a sanity check, the following claims should be provable for
    your definition: *)

Example havoc_example1 : empty_st =[ (HAVOC X)%imp ]=> (X !-> 0).
Proof.
(* FILL IN HERE *) Admitted.

Example havoc_example2 :
  empty_st =[ (SKIP;; HAVOC Z)%imp ]=> (Z !-> 42).
Proof.
(* FILL IN HERE *) Admitted.

(* Do not modify the following line: *)
Definition manual_grade_for_Check_rule_for_HAVOC : option (nat*string) := None.
(** [] *)

(** Finally, we repeat the definition of command equivalence from above: *)

Definition cequiv (c1 c2 : com) : Prop := forall st st' : state,
  st =[ c1 ]=> st' <-> st =[ c2 ]=> st'.

(** Let's apply this definition to prove some nondeterministic
    programs equivalent / inequivalent. *)

(** **** Exercise: 3 stars, standard (havoc_swap)  

    Are the following two programs equivalent? *)

Definition pXY :=
  (HAVOC X;; HAVOC Y)%imp.

Definition pYX :=
  (HAVOC Y;; HAVOC X)%imp.

(** If you think they are equivalent, prove it. If you think they are
    not, prove that. *)

Theorem pXY_cequiv_pYX :
  cequiv pXY pYX \/ ~cequiv pXY pYX.
Proof. (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 4 stars, standard, optional (havoc_copy)  

    Are the following two programs equivalent? *)

Definition ptwice :=
  (HAVOC X;; HAVOC Y)%imp.

Definition pcopy :=
  (HAVOC X;; Y ::= X)%imp.

(** If you think they are equivalent, then prove it. If you think they
    are not, then prove that.  (Hint: You may find the [assert] tactic
    useful.) *)

Theorem ptwice_cequiv_pcopy :
  cequiv ptwice pcopy \/ ~cequiv ptwice pcopy.
Proof. (* FILL IN HERE *) Admitted.
(** [] *)

(** The definition of program equivalence we are using here has some
    subtle consequences on programs that may loop forever.  What
    [cequiv] says is that the set of possible _terminating_ outcomes
    of two equivalent programs is the same. However, in a language
    with nondeterminism, like Himp, some programs always terminate,
    some programs always diverge, and some programs can
    nondeterministically terminate in some runs and diverge in
    others. The final part of the following exercise illustrates this
    phenomenon.
*)

(** **** Exercise: 4 stars, advanced (p1_p2_term)  

    Consider the following commands: *)

Definition p1 : com :=
  (WHILE ~ (X = 0) DO
    HAVOC Y;;
    X ::= X + 1
  END)%imp.

Definition p2 : com :=
  (WHILE ~ (X = 0) DO
    SKIP
  END)%imp.

(** Intuitively, [p1] and [p2] have the same termination behavior:
    either they loop forever, or they terminate in the same state they
    started in.  We can capture the termination behavior of [p1] and
    [p2] individually with these lemmas: *)

Lemma p1_may_diverge : forall st st', st X <> 0 ->
  ~ st =[ p1 ]=> st'.
Proof. (* FILL IN HERE *) Admitted.

Lemma p2_may_diverge : forall st st', st X <> 0 ->
  ~ st =[ p2 ]=> st'.
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 4 stars, advanced (p1_p2_equiv)  

    Use these two lemmas to prove that [p1] and [p2] are actually
    equivalent. *)

Theorem p1_p2_equiv : cequiv p1 p2.
Proof. (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 4 stars, advanced (p3_p4_inequiv)  

    Prove that the following programs are _not_ equivalent.  (Hint:
    What should the value of [Z] be when [p3] terminates?  What about
    [p4]?) *)

Definition p3 : com :=
  (Z ::= 1;;
  WHILE ~(X = 0) DO
    HAVOC X;;
    HAVOC Z
  END)%imp.

Definition p4 : com :=
  (X ::= 0;;
  Z ::= 1)%imp.

Theorem p3_p4_inequiv : ~ cequiv p3 p4.
Proof. (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 5 stars, advanced, optional (p5_p6_equiv)  

    Prove that the following commands are equivalent.  (Hint: As
    mentioned above, our definition of [cequiv] for Himp only takes
    into account the sets of possible terminating configurations: two
    programs are equivalent if and only if the set of possible terminating
    states is the same for both programs when given a same starting state
    [st].  If [p5] terminates, what should the final state be? Conversely,
    is it always possible to make [p5] terminate?) *)

Definition p5 : com :=
  (WHILE ~(X = 1) DO
    HAVOC X
  END)%imp.

Definition p6 : com :=
  (X ::= 1)%imp.

Theorem p5_p6_equiv : cequiv p5 p6.
Proof. (* FILL IN HERE *) Admitted.
(** [] *)

End Himp.

(* ################################################################# *)
(** * Additional Exercises *)

(** **** Exercise: 4 stars, standard, optional (for_while_equiv)  

    This exercise extends the optional [add_for_loop] exercise from
    the [Imp] chapter, where you were asked to extend the language
    of commands with C-style [for] loops.  Prove that the command:

      for (c1 ; b ; c2) {
          c3
      }

    is equivalent to:

       c1 ;
       WHILE b DO
         c3 ;
         c2
       END
*)
(* FILL IN HERE 

    [] *)

(** **** Exercise: 3 stars, standard, optional (swap_noninterfering_assignments)  

    (Hint: You'll need [functional_extensionality] for this one.) *)

Theorem swap_noninterfering_assignments: forall l1 l2 a1 a2,
  l1 <> l2 ->
  var_not_used_in_aexp l1 a2 ->
  var_not_used_in_aexp l2 a1 ->
  cequiv
    (l1 ::= a1;; l2 ::= a2)
    (l2 ::= a2;; l1 ::= a1).
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 4 stars, advanced, optional (capprox)  

    In this exercise we define an asymmetric variant of program
    equivalence we call _program approximation_. We say that a
    program [c1] _approximates_ a program [c2] when, for each of
    the initial states for which [c1] terminates, [c2] also terminates
    and produces the same final state. Formally, program approximation
    is defined as follows: *)

Definition capprox (c1 c2 : com) : Prop := forall (st st' : state),
  st =[ c1 ]=> st' -> st =[ c2 ]=> st'.

(** For example, the program

  c1 = WHILE ~(X = 1) DO
         X ::= X - 1
       END

    approximates [c2 = X ::= 1], but [c2] does not approximate [c1]
    since [c1] does not terminate when [X = 0] but [c2] does.  If two
    programs approximate each other in both directions, then they are
    equivalent. *)

(** Find two programs [c3] and [c4] such that neither approximates
    the other. *)

Definition c3 : com
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
Definition c4 : com
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Theorem c3_c4_different : ~ capprox c3 c4 /\ ~ capprox c4 c3.
Proof. (* FILL IN HERE *) Admitted.

(** Find a program [cmin] that approximates every other program. *)

Definition cmin : com
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Theorem cmin_minimal : forall c, capprox cmin c.
Proof. (* FILL IN HERE *) Admitted.

(** Finally, find a non-trivial property which is preserved by
    program approximation (when going from left to right). *)

Definition zprop (c : com) : Prop
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Theorem zprop_preserving : forall c c',
  zprop c -> capprox c c' -> zprop c'.
Proof. (* FILL IN HERE *) Admitted.
(** [] *)

(* Thu Feb 7 20:09:23 EST 2019 *)
