(** * BagPerm:  Insertion Sort With Bags *)

(** We have seen how to specify algorithms on "collections", such as
    sorting algorithms, using [Permutation]s.  Instead of using
    permutations, another way to specify these algorithms is to use
    _bags_ (also called _multisets_), which we introduced in [Lists].
    A _set_ of values is like a list with no repeats where
    the order does not matter.  A _multiset_ is like a list, possibly
    with repeats, where the order does not matter.  Whereas the principal
    query on a set is whether a given element appears in it, the
    principal query on a bag is _how many_ times a given element appears 
    in it. *)

From Coq Require Import Strings.String. (* for manual grading *)
From Coq Require Import Setoid Morphisms.
From VFA Require Import Perm.
From VFA Require Import Sort.

(** To keep this chapter more self-contained, 
we restate the critical definitions from [Lists].  *)
Definition bag := list nat.

Fixpoint count (v:nat) (s:bag) : nat :=
  match s with
  | nil => 0
  | h :: t =>
      (if h =? v then 1 else 0) + count v t
  end.

(** We will say two bags are _equivalent_ if they have the same number
    of copies of every possible element. *)

Definition bag_eqv (b1 b2: bag) : Prop :=
  forall n, count n b1 = count n b2. 

(** **** Exercise: 2 stars, standard (bag_eqv_properties)  *)

(* It is easy to prove [bag_eqv] is an equivalence relation. *)

Lemma bag_eqv_refl : forall b, bag_eqv b b.
Proof.
(* FILL IN HERE *) Admitted.

Lemma bag_eqv_sym: forall b1 b2, bag_eqv b1 b2 -> bag_eqv b2 b1. 
Proof.
(* FILL IN HERE *) Admitted.

Lemma bag_eqv_trans: forall b1 b2 b3, bag_eqv b1 b2 -> bag_eqv b2 b3 -> bag_eqv b1 b3.
Proof.
(* FILL IN HERE *) Admitted.

(** The following little lemma is handy in a couple of places. *)

Lemma bag_eqv_cons : forall x b1 b2, bag_eqv b1 b2 -> bag_eqv (x::b1) (x::b2).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################################# *)
(** * Correctness *)

(** A sorting algorithm must rearrange the elements into a list that
    is totally ordered.  But let's say that a different way: the
    algorithm must produce a list _with the same multiset of values_,
    and this list must be totally ordered. *)

Definition is_a_sorting_algorithm' (f: list nat -> list nat) :=
  forall al, bag_eqv al (f al) /\ sorted (f al).

(** **** Exercise: 3 stars, standard (insert_bag) 

    First, prove the auxiliary lemma [insert_bag], which will be
    useful for proving [sort_bag] below.  Your proof will be by
    induction.  *)

Lemma insert_bag: forall x l, bag_eqv (x::l) (insert x l).
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard (sort_bag) 

    Now prove that sort preserves bag contents. *)
Theorem sort_bag: forall l, bag_eqv l (sort l).
(* FILL IN HERE *) Admitted.
(** [] *)

(** Now we wrap it all up.  *)

Theorem insertion_sort_correct:
  is_a_sorting_algorithm' sort.
Proof.
split. apply sort_bag. apply sort_sorted.
Qed.

(** **** Exercise: 1 star, standard (permutations_vs_multiset) 

    Compare your proofs of [insert_perm, sort_perm] with your proofs
    of [insert_bag, sort_bag].  Which proofs are simpler?

      - [ ] easier with permutations,
      - [ ] easier with multisets
      - [ ] about the same.

   Regardless of "difficulty", which do you prefer / find easier to
   think about?
      - [ ] permutations or
      - [ ] multisets

   Put an X in one box in each list. *)
(* Do not modify the following line: *)
Definition manual_grade_for_permutations_vs_multiset : option (nat*string) := None.
(** [] *)

(* ################################################################# *)
(** * Permutations and Multisets *)

(** The two specifications of insertion sort are equivalent.  One
    reason is that permutations and multisets are closely related.
    We're going to prove:

       [Permutation al bl <-> bag_eqv al bl.] *)

(** **** Exercise: 3 stars, standard (perm_bag) 

    The forward direction is straighforward, by induction on the evidence for
    [Permutation]: *)
Lemma perm_bag:
  forall al bl : list nat,
   Permutation al bl -> bag_eqv al bl. 
(* FILL IN HERE *) Admitted.
(** [] *)

(** The other direction,
    [bag_eqv al bl -> Permutation al bl],
    is surprisingly difficult.  
    This proof approach is due to Zhong Sheng Hu.
    The first three lemmas are used to prove the fourth one. *)

(** **** Exercise: 2 stars, advanced (bag_nil_inv)  *)
Lemma bag_nil_inv : forall b, bag_eqv [] b -> b = []. 
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, advanced (bag_cons_inv)  *)
Lemma bag_cons_inv : forall l x n,
    S n = count x l ->
    exists l1 l2,
      l = l1 ++ x :: l2
      /\ count x (l1 ++ l2) = n.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, advanced (count_insert_other)  *)
Lemma count_insert_other : forall l1 l2 x y,
    y <> x -> count y (l1 ++ x :: l2) = count y (l1 ++ l2).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, advanced (bag_perm)  *)
Lemma bag_perm:
  forall al bl, bag_eqv al bl -> Permutation al bl.
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################################# *)
(** * The Main Theorem: Equivalence of Multisets and Permutations *)
Theorem bag_eqv_iff_perm:
  forall al bl, bag_eqv al bl <-> Permutation al bl.
Proof.
  intros. split. apply bag_perm. apply perm_bag.
Qed.

(** Therefore, it doesn't matter whether you prove your sorting
    algorithm using the Permutations method or the multiset method. *)

Corollary sort_specifications_equivalent:
    forall sort, is_a_sorting_algorithm sort <->  is_a_sorting_algorithm' sort.
Proof.
  unfold is_a_sorting_algorithm, is_a_sorting_algorithm'.
  split; intros;
  destruct (H al); split; auto;
  apply bag_eqv_iff_perm; auto.
Qed.

(** $Date$ *)

(* 2020-08-07 17:08 *)
