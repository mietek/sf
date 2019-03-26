(** * Types: Type Systems *)

(** Our next major topic is _type systems_ -- static program
    analyses that classify expressions according to the "shapes" of
    their results.  We'll begin with a typed version of the simplest
    imaginable language, to introduce the basic ideas of types and
    typing rules and the fundamental theorems about type systems:
    _type preservation_ and _progress_.  In chapter [Stlc] we'll move
    on to the _simply typed lambda-calculus_, which lives at the core
    of every modern functional programming language (including
    Coq!). *)

Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Arith.Arith.
From PLF Require Import Maps.
From PLF Require Import Imp.
From PLF Require Import Smallstep.

Hint Constructors multi.

(* ################################################################# *)
(** * Typed Arithmetic Expressions *)

(** To motivate the discussion of type systems, let's begin as
    usual with a tiny toy language.  We want it to have the potential
    for programs to go wrong because of runtime type errors, so we
    need something a tiny bit more complex than the language of
    constants and addition that we used in chapter [Smallstep]: a
    single kind of data (e.g., numbers) is too simple, but just two
    kinds (numbers and booleans) gives us enough material to tell an
    interesting story.

    The language definition is completely routine. *)

(* ================================================================= *)
(** ** Syntax *)

(** Here is the syntax, informally:

    t ::= tru
        | fls
        | test t then t else t
        | zro
        | scc t
        | prd t
        | iszro t

    And here it is formally: *)

Inductive tm : Type :=
  | tru : tm
  | fls : tm
  | test : tm -> tm -> tm -> tm
  | zro : tm
  | scc : tm -> tm
  | prd : tm -> tm
  | iszro : tm -> tm.

(** _Values_ are [tru], [fls], and numeric values... *)

Inductive bvalue : tm -> Prop :=
  | bv_tru : bvalue tru
  | bv_fls : bvalue fls.

Inductive nvalue : tm -> Prop :=
  | nv_zro : nvalue zro
  | nv_scc : forall t, nvalue t -> nvalue (scc t).

Definition value (t : tm) := bvalue t \/ nvalue t.

Hint Constructors bvalue nvalue.
Hint Unfold value.
Hint Unfold update.

(* ================================================================= *)
(** ** Operational Semantics *)

(** Here is the single-step relation, first informally... 

                   -------------------------------                  (ST_TestTru)
                   test tru then t1 else t2 --> t1

                   -------------------------------                  (ST_TestFls)
                   test fls then t1 else t2 --> t2

                               t1 --> t1'
            ----------------------------------------------------       (ST_Test)
            test t1 then t2 else t3 --> test t1' then t2 else t3

                             t1 --> t1'
                         ------------------                             (ST_Scc)
                         scc t1 --> scc t1'

                           ---------------                           (ST_PrdZro)
                           prd zro --> zro

                         numeric value v1
                        -------------------                          (ST_PrdScc)
                        prd (scc v1) --> v1

                              t1 --> t1'
                         ------------------                             (ST_Prd)
                         prd t1 --> prd t1'

                          -----------------                        (ST_IszroZro)
                          iszro zro --> tru

                         numeric value v1
                      ----------------------                       (ST_IszroScc)
                      iszro (scc v1) --> fls

                            t1 --> t1'
                       ----------------------                         (ST_Iszro)
                       iszro t1 --> iszro t1'
*)

(** ... and then formally: *)

Reserved Notation "t1 '-->' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_TestTru : forall t1 t2,
      (test tru t1 t2) --> t1
  | ST_TestFls : forall t1 t2,
      (test fls t1 t2) --> t2
  | ST_Test : forall t1 t1' t2 t3,
      t1 --> t1' ->
      (test t1 t2 t3) --> (test t1' t2 t3)
  | ST_Scc : forall t1 t1',
      t1 --> t1' ->
      (scc t1) --> (scc t1')
  | ST_PrdZro :
      (prd zro) --> zro
  | ST_PrdScc : forall t1,
      nvalue t1 ->
      (prd (scc t1)) --> t1
  | ST_Prd : forall t1 t1',
      t1 --> t1' ->
      (prd t1) --> (prd t1')
  | ST_IszroZro :
      (iszro zro) --> tru
  | ST_IszroScc : forall t1,
       nvalue t1 ->
      (iszro (scc t1)) --> fls
  | ST_Iszro : forall t1 t1',
      t1 --> t1' ->
      (iszro t1) --> (iszro t1')

where "t1 '-->' t2" := (step t1 t2).

Hint Constructors step.

(** Notice that the [step] relation doesn't care about whether the
    expression being stepped makes global sense -- it just checks that
    the operation in the _next_ reduction step is being applied to the
    right kinds of operands.  For example, the term [scc tru] cannot
    take a step, but the almost as obviously nonsensical term

       scc (test tru then tru else tru)

    can take a step (once, before becoming stuck). *)

(* ================================================================= *)
(** ** Normal Forms and Values *)

(** The first interesting thing to notice about this [step] relation
    is that the strong progress theorem from the [Smallstep] chapter
    fails here.  That is, there are terms that are normal forms (they
    can't take a step) but not values (because we have not included
    them in our definition of possible "results of reduction").  Such
    terms are _stuck_. *)

Notation step_normal_form := (normal_form step).

Definition stuck (t : tm) : Prop :=
  step_normal_form t /\ ~ value t.

Hint Unfold stuck.

(** **** Exercise: 2 stars, standard (some_term_is_stuck)  *)
Example some_term_is_stuck :
  exists t, stuck t.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** However, although values and normal forms are _not_ the same in
    this language, the set of values is a subset of the set of normal
    forms.  This is important because it shows we did not accidentally
    define things so that some value could still take a step. *)

(** **** Exercise: 3 stars, standard (value_is_nf)  *)
Lemma value_is_nf : forall t,
  value t -> step_normal_form t.
Proof.
  (* FILL IN HERE *) Admitted.

(** (Hint: You will reach a point in this proof where you need to
    use an induction to reason about a term that is known to be a
    numeric value.  This induction can be performed either over the
    term itself or over the evidence that it is a numeric value.  The
    proof goes through in either case, but you will find that one way
    is quite a bit shorter than the other.  For the sake of the
    exercise, try to complete the proof both ways.) 

    [] *)

(** **** Exercise: 3 stars, standard, optional (step_deterministic)  

    Use [value_is_nf] to show that the [step] relation is also
    deterministic. *)

Theorem step_deterministic:
  deterministic step.
Proof with eauto.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** Typing *)

(** The next critical observation is that, although this
    language has stuck terms, they are always nonsensical, mixing
    booleans and numbers in a way that we don't even _want_ to have a
    meaning.  We can easily exclude such ill-typed terms by defining a
    _typing relation_ that relates terms to the types (either numeric
    or boolean) of their final results.  *)

Inductive ty : Type :=
  | Bool : ty
  | Nat : ty.

(** In informal notation, the typing relation is often written
    [|- t \in T] and pronounced "[t] has type [T]."  The [|-] symbol
    is called a "turnstile."  Below, we're going to see richer typing
    relations where one or more additional "context" arguments are
    written to the left of the turnstile.  For the moment, the context
    is always empty. 

    
                           ---------------                     (T_Tru)
                           |- tru \in Bool

                          ---------------                      (T_Fls)
                          |- fls \in Bool

             |- t1 \in Bool    |- t2 \in T    |- t3 \in T
             --------------------------------------------     (T_Test)
                    |- test t1 then t2 else t3 \in T

                             --------------                    (T_Zro)
                             |- zro \in Nat

                            |- t1 \in Nat
                          -----------------                    (T_Scc)
                          |- scc t1 \in Nat

                            |- t1 \in Nat
                          -----------------                    (T_Prd)
                          |- prd t1 \in Nat

                            |- t1 \in Nat
                        --------------------                 (T_IsZro)
                        |- iszro t1 \in Bool
*)

Reserved Notation "'|-' t '\in' T" (at level 40).

Inductive has_type : tm -> ty -> Prop :=
  | T_Tru :
       |- tru \in Bool
  | T_Fls :
       |- fls \in Bool
  | T_Test : forall t1 t2 t3 T,
       |- t1 \in Bool ->
       |- t2 \in T ->
       |- t3 \in T ->
       |- test t1 t2 t3 \in T
  | T_Zro :
       |- zro \in Nat
  | T_Scc : forall t1,
       |- t1 \in Nat ->
       |- scc t1 \in Nat
  | T_Prd : forall t1,
       |- t1 \in Nat ->
       |- prd t1 \in Nat
  | T_Iszro : forall t1,
       |- t1 \in Nat ->
       |- iszro t1 \in Bool

where "'|-' t '\in' T" := (has_type t T).

Hint Constructors has_type.

Example has_type_1 :
  |- test fls zro (scc zro) \in Nat.
Proof.
  apply T_Test.
    - apply T_Fls.
    - apply T_Zro.
    - apply T_Scc.
       + apply T_Zro.
Qed.

(** (Since we've included all the constructors of the typing relation
    in the hint database, the [auto] tactic can actually find this
    proof automatically.) *)

(** It's important to realize that the typing relation is a
    _conservative_ (or _static_) approximation: it does not consider
    what happens when the term is reduced -- in particular, it does
    not calculate the type of its normal form. *)

Example has_type_not :
  ~ ( |- test fls zro tru \in Bool ).
Proof.
  intros Contra. solve_by_inverts 2.  Qed.

(** **** Exercise: 1 star, standard, optional (scc_hastype_nat__hastype_nat)  *)
Example scc_hastype_nat__hastype_nat : forall t,
  |- scc t \in Nat ->
  |- t \in Nat.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ----------------------------------------------------------------- *)
(** *** Canonical forms *)

(** The following two lemmas capture the fundamental property that the
    definitions of boolean and numeric values agree with the typing
    relation. *)

Lemma bool_canonical : forall t,
  |- t \in Bool -> value t -> bvalue t.
Proof.
  intros t HT [Hb | Hn].
  - assumption.
  - induction Hn; inversion HT; auto.
Qed.

Lemma nat_canonical : forall t,
  |- t \in Nat -> value t -> nvalue t.
Proof.
  intros t HT [Hb | Hn].
  - inversion Hb; subst; inversion HT.
  - assumption.
Qed.

(* ================================================================= *)
(** ** Progress *)

(** The typing relation enjoys two critical properties.  The first is
    that well-typed normal forms are not stuck -- or conversely, if a
    term is well typed, then either it is a value or it can take at
    least one step.  We call this _progress_. *)

(** **** Exercise: 3 stars, standard (finish_progress)  *)
Theorem progress : forall t T,
  |- t \in T ->
  value t \/ exists t', t --> t'.

(** Complete the formal proof of the [progress] property.  (Make sure
    you understand the parts we've given of the informal proof in the
    following exercise before starting -- this will save you a lot of
    time.) *)
Proof with auto.
  intros t T HT.
  induction HT...
  (* The cases that were obviously values, like T_Tru and
     T_Fls, were eliminated immediately by auto *)
  - (* T_Test *)
    right. inversion IHHT1; clear IHHT1.
    + (* t1 is a value *)
    apply (bool_canonical t1 HT1) in H.
    inversion H; subst; clear H.
      exists t2...
      exists t3...
    + (* t1 can take a step *)
      inversion H as [t1' H1].
      exists (test t1' t2 t3)...
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, advanced (finish_progress_informal)  

    Complete the corresponding informal proof: *)

(** _Theorem_: If [|- t \in T], then either [t] is a value or else
    [t --> t'] for some [t']. *)

(** _Proof_: By induction on a derivation of [|- t \in T].

    - If the last rule in the derivation is [T_Test], then [t = test t1
      then t2 else t3], with [|- t1 \in Bool], [|- t2 \in T] and [|- t3
      \in T].  By the IH, either [t1] is a value or else [t1] can step
      to some [t1'].

      - If [t1] is a value, then by the canonical forms lemmas
        and the fact that [|- t1 \in Bool] we have that [t1]
        is a [bvalue] -- i.e., it is either [tru] or [fls].
        If [t1 = tru], then [t] steps to [t2] by [ST_TestTru],
        while if [t1 = fls], then [t] steps to [t3] by
        [ST_TestFls].  Either way, [t] can step, which is what
        we wanted to show.

      - If [t1] itself can take a step, then, by [ST_Test], so can
        [t].

    - (* FILL IN HERE *)
 *)
(* Do not modify the following line: *)
Definition manual_grade_for_finish_progress_informal : option (nat*string) := None.
(** [] *)

(** This theorem is more interesting than the strong progress theorem
    that we saw in the [Smallstep] chapter, where _all_ normal forms
    were values.  Here a term can be stuck, but only if it is ill
    typed. *)

(* ================================================================= *)
(** ** Type Preservation *)

(** The second critical property of typing is that, when a well-typed
    term takes a step, the result is also a well-typed term. *)

(** **** Exercise: 2 stars, standard (finish_preservation)  *)
Theorem preservation : forall t t' T,
  |- t \in T ->
  t --> t' ->
  |- t' \in T.

(** Complete the formal proof of the [preservation] property.  (Again,
    make sure you understand the informal proof fragment in the
    following exercise first.) *)

Proof with auto.
  intros t t' T HT HE.
  generalize dependent t'.
  induction HT;
         (* every case needs to introduce a couple of things *)
         intros t' HE;
         (* and we can deal with several impossible
            cases all at once *)
         try solve_by_invert.
    - (* T_Test *) inversion HE; subst; clear HE.
      + (* ST_TESTTru *) assumption.
      + (* ST_TestFls *) assumption.
      + (* ST_Test *) apply T_Test; try assumption.
        apply IHHT1; assumption.
    (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, advanced (finish_preservation_informal)  

    Complete the following informal proof: *)

(** _Theorem_: If [|- t \in T] and [t --> t'], then [|- t' \in T]. *)

(** _Proof_: By induction on a derivation of [|- t \in T].

    - If the last rule in the derivation is [T_Test], then [t = test t1
      then t2 else t3], with [|- t1 \in Bool], [|- t2 \in T] and [|- t3
      \in T].

      Inspecting the rules for the small-step reduction relation and
      remembering that [t] has the form [test ...], we see that the
      only ones that could have been used to prove [t --> t'] are
      [ST_TestTru], [ST_TestFls], or [ST_Test].

      - If the last rule was [ST_TestTru], then [t' = t2].  But we
        know that [|- t2 \in T], so we are done.

      - If the last rule was [ST_TestFls], then [t' = t3].  But we
        know that [|- t3 \in T], so we are done.

      - If the last rule was [ST_Test], then [t' = test t1' then t2
        else t3], where [t1 --> t1'].  We know [|- t1 \in Bool] so,
        by the IH, [|- t1' \in Bool].  The [T_Test] rule then gives us
        [|- test t1' then t2 else t3 \in T], as required.

    - (* FILL IN HERE *)
*)
(* Do not modify the following line: *)
Definition manual_grade_for_finish_preservation_informal : option (nat*string) := None.
(** [] *)

(** **** Exercise: 3 stars, standard (preservation_alternate_proof)  

    Now prove the same property again by induction on the
    _evaluation_ derivation instead of on the typing derivation.
    Begin by carefully reading and thinking about the first few
    lines of the above proofs to make sure you understand what
    each one is doing.  The set-up for this proof is similar, but
    not exactly the same. *)

Theorem preservation' : forall t t' T,
  |- t \in T ->
  t --> t' ->
  |- t' \in T.
Proof with eauto.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** The preservation theorem is often called _subject reduction_,
    because it tells us what happens when the "subject" of the typing
    relation is reduced.  This terminology comes from thinking of
    typing statements as sentences, where the term is the subject and
    the type is the predicate. *)

(* ================================================================= *)
(** ** Type Soundness *)

(** Putting progress and preservation together, we see that a
    well-typed term can never reach a stuck state.  *)

Definition multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

Corollary soundness : forall t t' T,
  |- t \in T ->
  t -->* t' ->
  ~(stuck t').
Proof.
  intros t t' T HT P. induction P; intros [R S].
  destruct (progress x T HT); auto.
  apply IHP.  apply (preservation x y T HT H).
  unfold stuck. split; auto.   Qed.

(* ================================================================= *)
(** ** Additional Exercises *)

(** **** Exercise: 2 stars, standard, recommended (subject_expansion)  

    Having seen the subject reduction property, one might
    wonder whether the opposity property -- subject _expansion_ --
    also holds.  That is, is it always the case that, if [t --> t']
    and [|- t' \in T], then [|- t \in T]?  If so, prove it.  If
    not, give a counter-example.  (You do not need to prove your
    counter-example in Coq, but feel free to do so.)

    (* FILL IN HERE *)
*)
(* Do not modify the following line: *)
Definition manual_grade_for_subject_expansion : option (nat*string) := None.
(** [] *)

(** **** Exercise: 2 stars, standard (variation1)  

    Suppose that we add this new rule to the typing relation:

      | T_SccBool : forall t,
           |- t \in Bool ->
           |- scc t \in Bool

   Which of the following properties remain true in the presence of
   this rule?  For each one, write either "remains true" or
   else "becomes false." If a property becomes false, give a
   counterexample.
      - Determinism of [step]
            (* FILL IN HERE *)
      - Progress
            (* FILL IN HERE *)
      - Preservation
            (* FILL IN HERE *)
*)
(* Do not modify the following line: *)
Definition manual_grade_for_variation1 : option (nat*string) := None.
(** [] *)

(** **** Exercise: 2 stars, standard (variation2)  

    Suppose, instead, that we add this new rule to the [step] relation:

      | ST_Funny1 : forall t2 t3,
           (test tru t2 t3) --> t3

   Which of the above properties become false in the presence of
   this rule?  For each one that does, give a counter-example.
            (* FILL IN HERE *)
*)
(* Do not modify the following line: *)
Definition manual_grade_for_variation2 : option (nat*string) := None.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (variation3)  

    Suppose instead that we add this rule:

      | ST_Funny2 : forall t1 t2 t2' t3,
           t2 --> t2' ->
           (test t1 t2 t3) --> (test t1 t2' t3)

   Which of the above properties become false in the presence of
   this rule?  For each one that does, give a counter-example.
            (* FILL IN HERE *)

    [] *)

(** **** Exercise: 2 stars, standard, optional (variation4)  

    Suppose instead that we add this rule:

      | ST_Funny3 :
          (prd fls) --> (prd (prd fls))

   Which of the above properties become false in the presence of
   this rule?  For each one that does, give a counter-example.
(* FILL IN HERE *)

    [] *)

(** **** Exercise: 2 stars, standard, optional (variation5)  

    Suppose instead that we add this rule:

      | T_Funny4 :
            |- zro \in Bool

   Which of the above properties become false in the presence of
   this rule?  For each one that does, give a counter-example.
(* FILL IN HERE *)

    [] *)

(** **** Exercise: 2 stars, standard, optional (variation6)  

    Suppose instead that we add this rule:

      | T_Funny5 :
            |- prd zro \in Bool

   Which of the above properties become false in the presence of
   this rule?  For each one that does, give a counter-example.
(* FILL IN HERE *)

    [] *)

(** **** Exercise: 3 stars, standard, optional (more_variations)  

    Make up some exercises of your own along the same lines as
    the ones above.  Try to find ways of selectively breaking
    properties -- i.e., ways of changing the definitions that
    break just one of the properties and leave the others alone.
*)
(* FILL IN HERE 

    [] *)

(** **** Exercise: 1 star, standard (remove_prdzro)  

    The reduction rule [ST_PrdZro] is a bit counter-intuitive: we
    might feel that it makes more sense for the predecessor of [zro] to
    be undefined, rather than being defined to be [zro].  Can we
    achieve this simply by removing the rule from the definition of
    [step]?  Would doing so create any problems elsewhere?

(* FILL IN HERE *)
*)
(* Do not modify the following line: *)
Definition manual_grade_for_remove_predzro : option (nat*string) := None.
(** [] *)

(** **** Exercise: 4 stars, advanced (prog_pres_bigstep)  

    Suppose our evaluation relation is defined in the big-step style.
    State appropriate analogs of the progress and preservation
    properties. (You do not need to prove them.)

    Can you see any limitations of either of your properties?  Do they
    allow for nonterminating commands?  Why might we prefer the
    small-step semantics for stating preservation and progress?

(* FILL IN HERE *)
*)
(* Do not modify the following line: *)
Definition manual_grade_for_prog_pres_bigstep : option (nat*string) := None.
(** [] *)



(* Thu Feb 7 20:09:24 EST 2019 *)
