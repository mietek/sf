(** * Maps: Total and Partial Maps *)

(** Maps (or dictionaries) are ubiquitous data structures, both in
    software construction generally and in the theory of programming
    languages in particular; we're going to need them in many places
    in the coming chapters.  They also make a nice case study using
    ideas we've seen in previous chapters, including building data
    structures out of higher-order functions (from [Basics] and
    [Poly]) and the use of reflection to streamline proofs (from
    [IndProp]).

    We'll define two flavors of maps: _total_ maps, which include a
    "default" element to be returned when a key being looked up
    doesn't exist, and _partial_ maps, which return an [option] to
    indicate success or failure.  The latter is defined in terms of
    the former, using [None] as the default element. *)

(* ################################################################# *)
(** * The Coq Standard Library *)

(** One small digression before we start.

    Unlike the chapters we have seen so far, this one does not
    [Require Import] the chapter before it (and, transitively, all the
    earlier chapters).  Instead, in this chapter and from now, on
    we're going to import the definitions and theorems we need
    directly from Coq's standard library stuff.  You should not notice
    much difference, though, because we've been careful to name our
    own definitions and theorems the same as their counterparts in the
    standard library, wherever they overlap. *)

Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Logic.FunctionalExtensionality.

(** Documentation for the standard library can be found at
    http://coq.inria.fr/library/.  

    The [SearchAbout] command is a good way to look for theorems 
    involving objects of specific types. *)

(* ################################################################# *)
(** * Identifiers *)

(** First, we need a type for the keys that we use to index into our
    maps.  For this purpose, we again use the type [id] from the
    [Lists] chapter.  To make this chapter self contained, we repeat
    its definition here, together with the equality comparison
    function for [id]s and its fundamental property. *)

Inductive id : Type :=
  | Id : nat -> id.

Definition beq_id x y :=
  match x,y with
    | Id n1, Id n2 => beq_nat n1 n2
  end.

Theorem beq_id_refl : forall id, true = beq_id id id.
Proof.
  intros [n]. simpl. rewrite <- beq_nat_refl.
  reflexivity. Qed.

(** The following useful property of [beq_id] follows from an
    analogous lemma about numbers: *)

Theorem beq_id_true_iff : forall x y : id,
  beq_id x y = true <-> x = y.
Proof.
   intros [n1] [n2].
   unfold beq_id.
   rewrite beq_nat_true_iff.
   split.
   - (* -> *) intros H. rewrite H. reflexivity.
   - (* <- *) intros H. inversion H. reflexivity.
Qed.

(** Similarly: *)

Theorem beq_id_false_iff : forall x y : id,
  beq_id x y = false
  <-> x <> y.
Proof.
  intros x y. rewrite <- beq_id_true_iff.
  rewrite not_true_iff_false. reflexivity. Qed.

(** This useful variant follows just by rewriting: *)

Theorem false_beq_id : forall x y : id,
   x <> y
   -> beq_id x y = false.
Proof.
  intros x y. rewrite beq_id_false_iff.
  intros H. apply H. Qed.

(* ################################################################# *)
(** * Total Maps *)

(** Our main job in this chapter will be to build a definition of
    partial maps that is similar in behavior to the one we saw in the
    [Lists] chapter, plus accompanying lemmas about their behavior.

    This time around, though, we're going to use _functions_, rather
    than lists of key-value pairs, to build maps.  The advantage of
    this representation is that it offers a more _extensional_ view of
    maps, where two maps that respond to queries in the same way will
    be represented as literally the same thing (the same function),
    rather than just "equivalent" data structures.  This, in turn,
    simplifies proofs that use maps.

    We build partial maps in two steps.  First, we define a type of
    _total maps_ that return a default value when we look up a key
    that is not present in the map. *)

Definition total_map (A:Type) := id -> A.

(** Intuitively, a total map over an element type [A] _is_ just a
    function that can be used to look up [id]s, yielding [A]s.

    The function [t_empty] yields an empty total map, given a default
    element; this map always returns the default element when applied
    to any id. *)

Definition t_empty {A:Type} (v : A) : total_map A :=
  (fun _ => v).

(** More interesting is the [update] function, which (as before) takes
    a map [m], a key [x], and a value [v] and returns a new map that
    takes [x] to [v] and takes every other key to whatever [m] does. *)

Definition t_update {A:Type} (m : total_map A)
                    (x : id) (v : A) :=
  fun x' => if beq_id x x' then v else m x'.

(** This definition is a nice example of higher-order programming.
    The [t_update] function takes a _function_ [m] and yields a new
    function [fun x' => ...] that behaves like the desired map.

    For example, we can build a map taking [id]s to [bool]s, where [Id
    3] is mapped to [true] and every other key is mapped to [false],
    like this: *)

Definition examplemap :=
  t_update (t_update (t_empty false) (Id 1) false)
           (Id 3) true.

(** This completes the definition of total maps.  Note that we don't
    need to define a [find] operation because it is just function
    application! *)

Example update_example1 : examplemap (Id 0) = false.
Proof. reflexivity. Qed.

Example update_example2 : examplemap (Id 1) = false.
Proof. reflexivity. Qed.

Example update_example3 : examplemap (Id 2) = false.
Proof. reflexivity. Qed.

Example update_example4 : examplemap (Id 3) = true.
Proof. reflexivity. Qed.

(** To use maps in later chapters, we'll need several fundamental
    facts about how they behave.  Even if you don't work the following
    exercises, make sure you thoroughly understand the statements of
    the lemmas!  (Some of the proofs require the functional
    extensionality axiom, which is discussed in the [Logic]
    chapter and included in the Coq standard library.) *)

(** **** Exercise: 1 star, optional (t_apply_empty)  *)
(** First, the empty map returns its default element for all keys: *)
Lemma t_apply_empty:  forall A x v, @t_empty A v x = v.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, optional (t_update_eq)  *)
(** Next, if we update a map [m] at a key [x] with a new value [v]
    and then look up [x] in the map resulting from the [update], we
    get back [v]: *)

Lemma t_update_eq : forall A (m: total_map A) x v,
  (t_update m x v) x = v.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, optional (t_update_neq)  *)
(** On the other hand, if we update a map [m] at a key [x1] and then
    look up a _different_ key [x2] in the resulting map, we get the
    same result that [m] would have given: *)

Theorem t_update_neq : forall (X:Type) v x1 x2
                         (m : total_map X),
  x1 <> x2 ->
  (t_update m x1 v) x2 = m x2.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, optional (t_update_shadow)  *)
(** If we update a map [m] at a key [x] with a value [v1] and then
    update again with the same key [x] and another value [v2], the
    resulting map behaves the same (gives the same result when applied
    to any key) as the simpler map obtained by performing just
    the second [update] on [m]: *)

Lemma t_update_shadow : forall A (m: total_map A) v1 v2 x,
    t_update (t_update m x v1) x v2
  = t_update m x v2.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** For the final two lemmas about total maps, it's convenient to use
    the reflection idioms introduced in chapter [IndProp].  We begin
    by proving a fundamental _reflection lemma_ relating the equality
    proposition on [id]s with the boolean function [beq_id]. *)

(** **** Exercise: 2 stars (beq_idP)  *)
(** Use the proof of [beq_natP] in chapter [IndProp] as a template to
    prove the following: *)

Lemma beq_idP : forall x y, reflect (x = y) (beq_id x y).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** Now, given [id]s [x1] and [x2], we can use the [destruct (beq_idP
    x1 x2)] to simultaneously perform case analysis on the result of
    [beq_id x1 x2] and generate hypotheses about the equality (in the
    sense of [=]) of [x1] and [x2]. *)

(** **** Exercise: 2 stars (t_update_same)  *)
(** Using the example in chapter [IndProp] as a template, use
    [beq_idP] to prove the following theorem, which states that if we
    update a map to assign key [x] the same value as it already has in
    [m], then the result is equal to [m]: *)

Theorem t_update_same : forall X x (m : total_map X),
  t_update m x (m x) = m.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, recommended (t_update_permute)  *)
(** Use [beq_idP] to prove one final property of the [update]
    function: If we update a map [m] at two distinct keys, it doesn't
    matter in which order we do the updates. *)

Theorem t_update_permute : forall (X:Type) v1 v2 x1 x2
                             (m : total_map X),
  x2 <> x1 ->
    (t_update (t_update m x2 v2) x1 v1)
  = (t_update (t_update m x1 v1) x2 v2).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################################# *)
(** * Partial maps *)

(** Finally, we define _partial maps_ on top of total maps.  A partial
    map with elements of type [A] is simply a total map with elements
    of type [option A] and default element [None]. *)

Definition partial_map (A:Type) := total_map (option A).

Definition empty {A:Type} : partial_map A :=
  t_empty None.

Definition update {A:Type} (m : partial_map A)
                  (x : id) (v : A) :=
  t_update m x (Some v).

(** We can now lift all of the basic lemmas about total maps to
    partial maps.  *)

Lemma apply_empty : forall A x, @empty A x = None.
Proof.
  intros. unfold empty. rewrite t_apply_empty.
  reflexivity.
Qed.

Lemma update_eq : forall A (m: partial_map A) x v,
  (update m x v) x = Some v.
Proof.
  intros. unfold update. rewrite t_update_eq.
  reflexivity.
Qed.

Theorem update_neq : forall (X:Type) v x1 x2
                       (m : partial_map X),
  x2 <> x1 ->
  (update m x2 v) x1 = m x1.
Proof.
  intros X v x1 x2 m H.
  unfold update. rewrite t_update_neq. reflexivity.
  apply H. Qed.

Lemma update_shadow : forall A (m: partial_map A) v1 v2 x,
  update (update m x v1) x v2 = update m x v2.
Proof.
  intros A m v1 v2 x1. unfold update. rewrite t_update_shadow.
  reflexivity.
Qed.

Theorem update_same : forall X v x (m : partial_map X),
  m x = Some v ->
  update m x v = m.
Proof.
  intros X v x m H. unfold update. rewrite <- H.
  apply t_update_same.
Qed.

Theorem update_permute : forall (X:Type) v1 v2 x1 x2
                                (m : partial_map X),
  x2 <> x1 ->
    (update (update m x2 v2) x1 v1)
  = (update (update m x1 v1) x2 v2).
Proof.
  intros X v1 v2 x1 x2 m. unfold update.
  apply t_update_permute.
Qed.

(** $Date: 2015-12-11 17:17:29 -0500 (Fri, 11 Dec 2015) $ *)

