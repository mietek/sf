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

Require Import Coq.Arith.Arith.
Require Import SfLib.
Require Import Maps.
Require Import Imp.
Require Import Smallstep.

Hint Constructors multi.

(* ###################################################################### *)
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

(* ###################################################################### *)
(** ** Syntax *)

(** Here is the syntax, informally:

    t ::= true
        | false
        | if t then t else t
        | 0
        | succ t
        | pred t
        | iszero t

    And here it is formally: *)

Inductive tm : Type :=
  | ttrue : tm
  | tfalse : tm
  | tif : tm -> tm -> tm -> tm
  | tzero : tm
  | tsucc : tm -> tm
  | tpred : tm -> tm
  | tiszero : tm -> tm.

(** _Values_ are [true], [false], and numeric values... *)

Inductive bvalue : tm -> Prop :=
  | bv_true : bvalue ttrue
  | bv_false : bvalue tfalse.

Inductive nvalue : tm -> Prop :=
  | nv_zero : nvalue tzero
  | nv_succ : forall t, nvalue t -> nvalue (tsucc t).

Definition value (t:tm) := bvalue t \/ nvalue t.

Hint Constructors bvalue nvalue.
Hint Unfold value.
Hint Unfold update.

(* ###################################################################### *)
(** ** Operational Semantics *)

(** And here is the single-step relation, first informally... *)
(**

                    ------------------------------                  (ST_IfTrue)
                    if true then t1 else t2 ==> t1

                   -------------------------------                 (ST_IfFalse)
                   if false then t1 else t2 ==> t2

                              t1 ==> t1'
            ------------------------------------------------            (ST_If)
            if t1 then t2 else t3 ==> if t1' then t2 else t3

                              t1 ==> t1'
                         --------------------                         (ST_Succ)
                         succ t1 ==> succ t1'

                             ------------                         (ST_PredZero)
                             pred 0 ==> 0

                           numeric value v1
                        ---------------------                     (ST_PredSucc)
                        pred (succ v1) ==> v1

                              t1 ==> t1'
                         --------------------                         (ST_Pred)
                         pred t1 ==> pred t1'

                          -----------------                     (ST_IszeroZero)
                          iszero 0 ==> true

                           numeric value v1
                      --------------------------                (ST_IszeroSucc)
                      iszero (succ v1) ==> false

                              t1 ==> t1'
                       ------------------------                     (ST_Iszero)
                       iszero t1 ==> iszero t1'

*)

(** ... and then formally: *)

Reserved Notation "t1 '==>' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_IfTrue : forall t1 t2,
      (tif ttrue t1 t2) ==> t1
  | ST_IfFalse : forall t1 t2,
      (tif tfalse t1 t2) ==> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 ==> t1' ->
      (tif t1 t2 t3) ==> (tif t1' t2 t3)
  | ST_Succ : forall t1 t1',
      t1 ==> t1' ->
      (tsucc t1) ==> (tsucc t1')
  | ST_PredZero :
      (tpred tzero) ==> tzero
  | ST_PredSucc : forall t1,
      nvalue t1 ->
      (tpred (tsucc t1)) ==> t1
  | ST_Pred : forall t1 t1',
      t1 ==> t1' ->
      (tpred t1) ==> (tpred t1')
  | ST_IszeroZero :
      (tiszero tzero) ==> ttrue
  | ST_IszeroSucc : forall t1,
       nvalue t1 ->
      (tiszero (tsucc t1)) ==> tfalse
  | ST_Iszero : forall t1 t1',
      t1 ==> t1' ->
      (tiszero t1) ==> (tiszero t1')

where "t1 '==>' t2" := (step t1 t2).

Hint Constructors step.

(** Notice that the [step] relation doesn't care about whether
    expressions make global sense -- it just checks that the operation
    in the _next_ reduction step is being applied to the right kinds
    of operands.  For example, the term [succ true] (i.e., 
    [tsucc ttrue] in the formal syntax) cannot take a step, but the
    almost-as-obviously nonsensical term

       succ (if true then true else true)

    can take a step (once, before becoming stuck). *)

(* ###################################################################### *)
(** ** Normal Forms and Values *)

(** The first interesting thing to notice about this [step] relation
    is that the strong progress theorem from the [Smallstep] chapter
    fails here.  That is, there are terms that are normal forms (they
    can't take a step) but not values (because we have not included
    them in our definition of possible "results of reduction").  Such
    terms are _stuck_. *)

Notation step_normal_form := (normal_form step).

Definition stuck (t:tm) : Prop :=
  step_normal_form t /\ ~ value t.

Hint Unfold stuck.

(** **** Exercise: 2 stars (some_term_is_stuck)  *)
Example some_term_is_stuck :
  exists t, stuck t.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** However, although values and normal forms are not the same in this
    language, the set of values is included in the set of normal
    forms.  This is important because it shows we did not accidentally
    define things so that some value could still take a step. *)

(** **** Exercise: 3 stars, advanced (value_is_nf)  *)
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
    exercise, try to complete the proof both ways.) *)
(** [] *)

(** **** Exercise: 3 stars, optional (step_deterministic)  *)
(** Use [value_is_nf] to show that the [step] relation is also
    deterministic. *)

Theorem step_deterministic:
  deterministic step.
Proof with eauto.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ###################################################################### *)
(** ** Typing *)

(** The next critical observation is that, although this
    language has stuck terms, they are always nonsensical, mixing
    booleans and numbers in a way that we don't even _want_ to have a
    meaning.  We can easily exclude such ill-typed terms by defining a
    _typing relation_ that relates terms to the types (either numeric
    or boolean) of their final results.  *)

Inductive ty : Type :=
  | TBool : ty
  | TNat : ty.

(** In informal notation, the typing relation is often written
    [|- t \in T] and pronounced "[t] has type [T]."  The [|-] symbol
    is called a "turnstile."  Below, we're going to see richer typing
    relations where one or more additional "context" arguments are
    written to the left of the turnstile.  For the moment, the context
    is always empty. *)
(** 
                           ----------------                            (T_True)
                           |- true \in Bool

                          -----------------                           (T_False)
                          |- false \in Bool

             |- t1 \in Bool    |- t2 \in T    |- t3 \in T
             --------------------------------------------                (T_If)
                    |- if t1 then t2 else t3 \in T

                             ------------                              (T_Zero)
                             |- 0 \in Nat

                            |- t1 \in Nat
                          ------------------                           (T_Succ)
                          |- succ t1 \in Nat

                            |- t1 \in Nat
                          ------------------                           (T_Pred)
                          |- pred t1 \in Nat

                            |- t1 \in Nat
                        ---------------------                        (T_IsZero)
                        |- iszero t1 \in Bool

*)

Reserved Notation "'|-' t '\in' T" (at level 40).

Inductive has_type : tm -> ty -> Prop :=
  | T_True :
       |- ttrue \in TBool
  | T_False :
       |- tfalse \in TBool
  | T_If : forall t1 t2 t3 T,
       |- t1 \in TBool ->
       |- t2 \in T ->
       |- t3 \in T ->
       |- tif t1 t2 t3 \in T
  | T_Zero :
       |- tzero \in TNat
  | T_Succ : forall t1,
       |- t1 \in TNat ->
       |- tsucc t1 \in TNat
  | T_Pred : forall t1,
       |- t1 \in TNat ->
       |- tpred t1 \in TNat
  | T_Iszero : forall t1,
       |- t1 \in TNat ->
       |- tiszero t1 \in TBool

where "'|-' t '\in' T" := (has_type t T).

Hint Constructors has_type.

Example has_type_1 :
  |- tif tfalse tzero (tsucc tzero) \in TNat.
Proof.
  apply T_If.
    - apply T_False.
    - apply T_Zero.
    - apply T_Succ.
       + apply T_Zero.
Qed.

(** (Since we've included all the constructors of the typing relation
    in the hint database, the [auto] tactic can actually find this
    proof automatically.) *)

(** It's important to realize that the typing relation is a
    _conservative_ (or _static_) approximation: it does not consider
    what happens when the term is reduced -- in particular, it does
    not calculate the type of its normal form. *)

Example has_type_not :
  ~ (|- tif tfalse tzero ttrue \in TBool).
Proof.
  intros Contra. solve by inversion 2.  Qed.

(** **** Exercise: 1 star, optional (succ_hastype_nat__hastype_nat)  *)
Example succ_hastype_nat__hastype_nat : forall t,
  |- tsucc t \in TNat ->
  |- t \in TNat.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ###################################################################### *)
(** *** Canonical forms *)

(** The following two lemmas capture the fundamental property that the
    definitions of boolean and numeric values agree with the typing
    relation. *)

Lemma bool_canonical : forall t,
  |- t \in TBool -> value t -> bvalue t.
Proof.
  intros t HT HV.
  inversion HV; auto.
  induction H; inversion HT; auto.
Qed.

Lemma nat_canonical : forall t,
  |- t \in TNat -> value t -> nvalue t.
Proof.
  intros t HT HV.
  inversion HV.
  inversion H; subst; inversion HT.
  auto.
Qed.

(* ###################################################################### *)
(** ** Progress *)

(** The typing relation enjoys two critical properties.  The first is
    that well-typed normal forms are not stuck -- or conversely, if a
    term is well typed, then either it is a value or it can take at
    least one step. *)

Theorem progress : forall t T,
  |- t \in T ->
  value t \/ exists t', t ==> t'.

(** **** Exercise: 3 stars (finish_progress)  *)
(** Complete the formal proof of the [progress] property.  (Make sure
    you understand the informal proof fragment in the following
    exercise before starting -- this will save you a lot of time.) *)

Proof with auto.
  intros t T HT.
  induction HT...
  (* The cases that were obviously values, like T_True and
     T_False, were eliminated immediately by auto *)
  - (* T_If *)
    right. inversion IHHT1; clear IHHT1.
    + (* t1 is a value *)
    apply (bool_canonical t1 HT1) in H.
    inversion H; subst; clear H.
      exists t2...
      exists t3...
    + (* t1 can take a step *)
      inversion H as [t1' H1].
      exists (tif t1' t2 t3)...
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, advanced (finish_progress_informal)  *)
(** Complete the corresponding informal proof: *)

(** _Theorem_: If [|- t \in T], then either [t] is a value or else
    [t ==> t'] for some [t']. *)

(** _Proof_: By induction on a derivation of [|- t \in T].

      - If the last rule in the derivation is [T_If], then [t = if t1
        then t2 else t3], with [|- t1 \in Bool], [|- t2 \in T] and [|- t3
        \in T].  By the IH, either [t1] is a value or else [t1] can step
        to some [t1'].

            - If [t1] is a value, then by the canonical forms lemmas
              and the fact that [|- t1 \in Bool] we have that [t1]
              is a [bvalue] -- i.e., it is either [true] or [false].
              If [t1 = true], then [t] steps to [t2] by [ST_IfTrue],
              while if [t1 = false], then [t] steps to [t3] by
              [ST_IfFalse].  Either way, [t] can step, which is what
              we wanted to show.

            - If [t1] itself can take a step, then, by [ST_If], so can
              [t].

      - (* FILL IN HERE *)
[] *)

(** This theorem is more interesting than the strong progress theorem
    that we saw in the [Smallstep] chapter, where _all_ normal forms
    were values.  Here, a term can be stuck, but only if it is ill
    typed. *)

(** **** Exercise: 1 star (step_review)  *)
(** Quick review: answer _true_ or _false_.  In this language...
      - Every well-typed normal form is a value.

      - Every value is a normal form.

      - The single-step reduction relation is
        a partial function (i.e., it is deterministic).

      - The single-step reduction relation is a _total_ function.

*)
(** [] *)

(* ###################################################################### *)
(** ** Type Preservation *)

(** The second critical property of typing is that, when a well-typed
    term takes a step, the result is also a well-typed term. *)

Theorem preservation : forall t t' T,
  |- t \in T ->
  t ==> t' ->
  |- t' \in T.

(** **** Exercise: 2 stars (finish_preservation)  *)
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
         try (solve by inversion).
    - (* T_If *) inversion HE; subst; clear HE.
      + (* ST_IFTrue *) assumption.
      + (* ST_IfFalse *) assumption.
      + (* ST_If *) apply T_If; try assumption.
        apply IHHT1; assumption.
    (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, advanced (finish_preservation_informal)  *)
(** Complete the following informal proof: *)

(** _Theorem_: If [|- t \in T] and [t ==> t'], then [|- t' \in T]. *)

(** _Proof_: By induction on a derivation of [|- t \in T].

      - If the last rule in the derivation is [T_If], then [t = if t1
        then t2 else t3], with [|- t1 \in Bool], [|- t2 \in T] and [|- t3
        \in T].

        Inspecting the rules for the small-step reduction relation and
        remembering that [t] has the form [if ...], we see that the
        only ones that could have been used to prove [t ==> t'] are
        [ST_IfTrue], [ST_IfFalse], or [ST_If].

           - If the last rule was [ST_IfTrue], then [t' = t2].  But we
             know that [|- t2 \in T], so we are done.

           - If the last rule was [ST_IfFalse], then [t' = t3].  But we
             know that [|- t3 \in T], so we are done.

           - If the last rule was [ST_If], then [t' = if t1' then t2
             else t3], where [t1 ==> t1'].  We know [|- t1 \in Bool] so,
             by the IH, [|- t1' \in Bool].  The [T_If] rule then gives us
             [|- if t1' then t2 else t3 \in T], as required.

      - (* FILL IN HERE *)
[] *)

(** **** Exercise: 3 stars (preservation_alternate_proof)  *)
(** Now prove the same property again by induction on the
    _evaluation_ derivation instead of on the typing derivation.
    Begin by carefully reading and thinking about the first few
    lines of the above proofs to make sure you understand what
    each one is doing.  The set-up for this proof is similar, but
    not exactly the same. *)

Theorem preservation' : forall t t' T,
  |- t \in T ->
  t ==> t' ->
  |- t' \in T.
Proof with eauto.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** The preservation theorem is often called _subject reduction_,
    because it tells us what happens when the "subject" of the typing
    relation is reduced.  This terminology comes from thinking of
    typing statements as sentences, where the term is the subject and
    the type is the predicate. *)

(* ###################################################################### *)
(** ** Type Soundness *)

(** Putting progress and preservation together, it follows that a
    well-typed term can never reach a stuck state.  *)

Definition multistep := (multi step).
Notation "t1 '==>*' t2" := (multistep t1 t2) (at level 40).

Corollary soundness : forall t t' T,
  |- t \in T ->
  t ==>* t' ->
  ~(stuck t').
Proof.
  intros t t' T HT P. induction P; intros [R S].
  destruct (progress x T HT); auto.
  apply IHP.  apply (preservation x y T HT H).
  unfold stuck. split; auto.   Qed.

(* ###################################################################### *)
(** * Aside: the [normalize] Tactic *)

(** When experimenting with definitions of programming languages
    in Coq, we often want to see what a particular concrete term steps
    to -- i.e., we want to find proofs for goals of the form [t ==>*
    t'], where [t] is a completely concrete term and [t'] is unknown.
    These proofs are quite tedious to do by hand.  Consider, for
    example, reducing an arithmetic expression using the small-step
    relation [astep]. *)

Notation " t '/' st '==>a*' t' " := (multi (astep st) t t')
                                    (at level 40, st at level 39).

Example astep_example1 :
  (APlus (ANum 3) (AMult (ANum 3) (ANum 4))) / empty_state
  ==>a* (ANum 15).
Proof.
  apply multi_step with (APlus (ANum 3) (ANum 12)).
    apply AS_Plus2.
      apply av_num.
      apply AS_Mult.
  apply multi_step with (ANum 15).
    apply AS_Plus.
  apply multi_refl.
Qed.

(** We repeatedly apply [multi_step] until we get to a normal
    form. The proofs for the intermediate steps are simple enough that
    [auto], with appropriate hints, can solve them. *)

Hint Constructors astep aval.
Example astep_example1' :
  (APlus (ANum 3) (AMult (ANum 3) (ANum 4))) / empty_state
  ==>a* (ANum 15).
Proof.
  eapply multi_step. auto. simpl.
  eapply multi_step. auto. simpl.
  apply multi_refl.
Qed.

(** The following custom [Tactic Notation] definition captures this
    pattern.  In addition, before each step, we print out the current
    goal, so that we can follow how the term is being reduced. *)

Tactic Notation "print_goal" := match goal with |- ?x => idtac x end.
Tactic Notation "normalize" :=
   repeat (print_goal; eapply multi_step ;
             [ (eauto 10; fail) | (instantiate; simpl)]);
   apply multi_refl.

Example astep_example1'' :
  (APlus (ANum 3) (AMult (ANum 3) (ANum 4))) / empty_state
  ==>a* (ANum 15).
Proof.
  normalize.
  (* At this point in the proof script, the Coq response shows
     a trace of how the expression reduced...
   (APlus (ANum 3) (AMult (ANum 3) (ANum 4)) / empty_state ==>a* ANum 15)
   (multi (astep empty_state) (APlus (ANum 3) (ANum 12)) (ANum 15))
   (multi (astep empty_state) (ANum 15) (ANum 15))    *)
Qed.

(** The [normalize] tactic also provides a simple way to calculate
    what the normal form of a term is, by proving a goal with an
    existentially bound variable. *)

Example astep_example1''' : exists e',
  (APlus (ANum 3) (AMult (ANum 3) (ANum 4))) / empty_state
  ==>a* e'.
Proof.
  eapply ex_intro. normalize.

(* This time, the trace will be:

    (APlus (ANum 3) (AMult (ANum 3) (ANum 4)) / empty_state ==>a* ??)
    (multi (astep empty_state) (APlus (ANum 3) (ANum 12)) ??)
    (multi (astep empty_state) (ANum 15) ??)

   where ?? is the variable ``guessed'' by eapply.
*)
Qed.

(** **** Exercise: 1 star (normalize_ex)  *)
Theorem normalize_ex : exists e',
  (AMult (ANum 3) (AMult (ANum 2) (ANum 1))) / empty_state
  ==>a* e'.
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 1 star, optional (normalize_ex')  *)
(** For comparison, prove it using [apply] instead of [eapply]. *)

Theorem normalize_ex' : exists e',
  (AMult (ANum 3) (AMult (ANum 2) (ANum 1))) / empty_state
  ==>a* e'.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ###################################################################### *)
(** ** Additional Exercises *)

(** **** Exercise: 2 stars, recommended (subject_expansion)  *)
(** Having seen the subject reduction property, one might
    wonder whether the opposity property -- subject _expansion_ --
    also holds.  That is, is it always the case that, if [t ==> t']
    and [|- t' \in T], then [|- t \in T]?  If so, prove it.  If
    not, give a counter-example.  (You do not need to prove your
    counter-example in Coq, but feel free to do so.)

    (* FILL IN HERE *)
[] *)

(** **** Exercise: 2 stars (variation1)  *)
(** Suppose, that we add this new rule to the typing relation:

      | T_SuccBool : forall t,
           |- t \in TBool ->
           |- tsucc t \in TBool

   Which of the following properties remain true in the presence of
   this rule?  For each one, write either "remains true" or
   else "becomes false." If a property becomes false, give a
   counterexample.
      - Determinism of [step]

      - Progress

      - Preservation

[] *)

(** **** Exercise: 2 stars (variation2)  *)
(** Suppose, instead, that we add this new rule to the [step] relation:

      | ST_Funny1 : forall t2 t3,
           (tif ttrue t2 t3) ==> t3

   Which of the above properties become false in the presence of
   this rule?  For each one that does, give a counter-example.

[] *)

(** **** Exercise: 2 stars, optional (variation3)  *)
(** Suppose instead that we add this rule:

      | ST_Funny2 : forall t1 t2 t2' t3,
           t2 ==> t2' ->
           (tif t1 t2 t3) ==> (tif t1 t2' t3)

   Which of the above properties become false in the presence of
   this rule?  For each one that does, give a counter-example.

[] *)

(** **** Exercise: 2 stars, optional (variation4)  *)
(** Suppose instead that we add this rule:

      | ST_Funny3 :
          (tpred tfalse) ==> (tpred (tpred tfalse))

   Which of the above properties become false in the presence of
   this rule?  For each one that does, give a counter-example.

[] *)

(** **** Exercise: 2 stars, optional (variation5)  *)
(** Suppose instead that we add this rule:

      | T_Funny4 :
            |- tzero \in TBool

   Which of the above properties become false in the presence of
   this rule?  For each one that does, give a counter-example.

[] *)

(** **** Exercise: 2 stars, optional (variation6)  *)
(** Suppose instead that we add this rule:

      | T_Funny5 :
            |- tpred tzero \in TBool

   Which of the above properties become false in the presence of
   this rule?  For each one that does, give a counter-example.

[] *)

(** **** Exercise: 3 stars, optional (more_variations)  *)
(** Make up some exercises of your own along the same lines as
    the ones above.  Try to find ways of selectively breaking
    properties -- i.e., ways of changing the definitions that
    break just one of the properties and leave the others alone.
[] *)

(** **** Exercise: 1 star (remove_predzero)  *)
(** The reduction rule [E_PredZero] is a bit counter-intuitive: we
    might feel that it makes more sense for the predecessor of zero to
    be undefined, rather than being defined to be zero.  Can we
    achieve this simply by removing the rule from the definition of
    [step]?  Would doing so create any problems elsewhere?

(* FILL IN HERE *)
[] *)

(** **** Exercise: 4 stars, advanced (prog_pres_bigstep)  *)
(** Suppose our evaluation relation is defined in the big-step style.
    What are the appropriate analogs of the progress and preservation
    properties?  (You do not need to prove them.)

(* FILL IN HERE *)
[] *)

(** $Date: 2016-05-26 17:51:14 -0400 (Thu, 26 May 2016) $ *)
