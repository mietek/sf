(** * Selection:  Selection Sort *)

(** If you don't recall selection sort or haven't seen it in
    a while, see Wikipedia or read any standard textbook; some
    suggestions can be found in [Sort]. *)

(** The specification for sorting algorithms we developed in
    [Sort] can also be used to verify selection sort.  The
    selection-sort program itself is interesting, because writing it
    in Coq will cause us to explore a new technique for convincing Coq
    that a function terminates. *)

(** A couple of notes on efficiency:

    - Selection sort, like insertion sort, runs in quadratic time.
      But selection sort typically makes many more comparisons than
      insertion sort, so insertion sort is usually preferable for
      sorting small inputs.  Selection sort can beat insertion sort if
      the cost of swapping elements is vastly higher than the cost of
      comparing them, but that doesn't apply to functional lists.

    - What you should really never use is bubble sort.  "Bubble sort
      would be the wrong way to go."  Everybody should know that!  See
      this video for a definitive statement:
        https://www.youtube.com/watch?v=k4RRi_ntQc8&t=34 *)

From VFA Require Import Perm.
Hint Constructors Permutation.
From Coq Require Export Lists.List.  (* for exercise involving [List.length] *)

(* ################################################################# *)
(** * The Selection-Sort Program  *)

(** Selection sort on lists is more challenging to code in Coq
    than insertion sort was. First, we write a helper function
    to select the smallest element. *)

(* [select x l] is [(y, l')], where [y] is the smallest element
   of [x :: l], and [l'] is all the remaining elements of [x :: l]
   in their original order. *)
Fixpoint select (x: nat) (l: list nat) : nat * list nat :=
  match l with
  | [] => (x, [])
  | h :: t =>
    if x <=? h
    then let (j, l') := select x t
         in (j, h :: l')
    else let (j, l') := select h t
         in (j, x :: l')
  end.

(** Selection sort should repeatedly extract the smallest element and
    make a list of the results. But the following attempted definition
    fails: *)

Fail Fixpoint selsort (l : list nat) : list nat :=
  match l with
  | [] => []
  | x :: r => let (y, r') := select x r
            in y :: selsort r'
  end.

(** Coq rejects [selsort] because it doesn't satisfy Coq's
    requirements for termination.  The problem is that the recursive
    call in [selsort] is not _structurally decreasing_: the argument
    [r'] at the call site is not known to be a smaller part of the
    original input [l]. Indeed, [select] might not return such a list.
    For example, [select 1 [0; 2]] is [(0, [1; 2]], but [[1; 2]] is
    not a part of [[0; 2]]. *)

(** There are severals ways to fix this problem. One programming
    pattern is to provide _fuel_: an extra argument that has no use in
    the algorithm except to bound the amount of recursion.  The [n]
    argument, below, is the fuel. When it reaches [0], the recursion
    terminates. *)

Fixpoint selsort (l : list nat) (n : nat) : list nat :=
  match l, n with
  | _, O => []  (* ran out of fuel *)
  | [], _ => []
  | x :: r, S n' => let (y, r') := select x r
                  in y :: selsort r' n'
end.

(** If fuel runs out, we get the wrong output. *)

Example out_of_fuel: selsort [3;1;4;1;5] 3 <> [1;1;3;4;5].
Proof.
  simpl. intro. discriminate.
Qed.

(** Extra fuel isn't a problem though. *)

Example extra_fuel: selsort [3;1;4;1;5] 10 = [1;1;3;4;5].
Proof.
  simpl. reflexivity.
Qed.

(** The exact amount of fuel needed is the length of the input list.
    So that's how we define [selection_sort]: *)

Definition selection_sort (l : list nat) : list nat :=
  selsort l (length l).

Example sort_pi :
  selection_sort [3;1;4;1;5;9;2;6;5;3;5] = [1;1;2;3;3;4;5;5;5;6;9].
Proof.
  unfold selection_sort.
  simpl. reflexivity.
Qed.

(* ################################################################# *)
(** * Proof of Correctness *)

(** We begin by repeating from [Sort] the specification of a
    correct sorting algorithm: it rearranges the elements into a list
    that is totally ordered. *)

Inductive sorted: list nat -> Prop :=
 | sorted_nil: sorted []
 | sorted_1: forall i, sorted [i]
 | sorted_cons: forall i j l, i <= j -> sorted (j :: l) -> sorted (i :: j :: l).

Hint Constructors sorted.

Definition is_a_sorting_algorithm (f: list nat -> list nat) := forall al,
    Permutation al (f al) /\ sorted (f al).

(** In the following exercises, you will prove that selection sort
    is a correct sorting algorithm.  You might wish to keep track
    of the lemmas you have proved, so that you can spot places to
    use them later. *)

(** Depending on the path you have followed through _Software
    Foundations_ it might have been a while since you have worked with
    pairs.  Here's a brief reminder of how [destruct] can be used to
    break a pair apart into its components.  A similar technique
    will be needed in many of the following proofs. *)
Example pairs_example : forall (a c x : nat) (b d l : list nat),
    (a, b) = (let (c, d) := select x l in (c, d)) ->
    (a, b) = select x l.
Proof.
  intros. destruct (select x l) eqn:E. auto.
Qed.

(** **** Exercise: 3 stars, standard (select_perm)  *)

(** Prove that [select] returns a permutation of its
    input. Proceed by induction on [l].  The [inv] tactic defined at
    the end of [Perm] will be helpful. *)

Lemma select_perm: forall x l y r,
    (y, r) = select x l -> Permutation (x :: l) (y :: r).
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 3 stars, standard (selsort_perm)  *)

(** Prove that if you provide sufficient fuel, [selsort] produces a
    permutation.  Proceed by induction on [n]. *)

Lemma selsort_perm: forall n l,
    length l = n -> Permutation l (selsort l n).
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 1 star, standard (selection_sort_perm)  *)

(** Prove that [selection_sort] produces a permutation. *)

Lemma selection_sort_perm: forall l,
    Permutation l (selection_sort l).
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 2 stars, standard (select_rest_length)  *)

(** Prove that [select] returns a list that has the correct
    length. You can do this without induction if you make use of
    [select_perm]. *)

Lemma select_rest_length : forall x l y r,
    select x l = (y, r) -> length l = length r.
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 3 stars, standard (select_fst_leq)  *)

(** Prove that the first component of [select x _] is no bigger than
    [x]. Proceed by induction on [al]. *)

Lemma select_fst_leq: forall al bl x y,
    select x al = (y, bl) ->
    y <= x.
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 3 stars, standard (select_smallest)  *)

(** Prove that the first component of [select _ _] is no bigger
    than any of the elements in the second component. To represent
    that concept of comparing an element to a list, we introduce
    a new notation: *)

Definition le_all x xs := Forall (fun y => x <= y) xs.
Infix "<=*" := le_all (at level 70, no associativity).

(** Proceed by induction on [al]. *)

Lemma select_smallest: forall al bl x y,
    select x al = (y, bl) ->
    y <=* bl.
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 3 stars, standard (select_in)  *)

(** Prove that the element returned by [select] must be one of the
    elements in its input. Proceed by induction on [al]. *)

Lemma select_in : forall al bl x y,
    select x al = (y, bl) ->
    In y (x :: al).
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 3 stars, standard (cons_of_small_maintains_sort)  *)

(** Prove that adding an element to the beginning of a
    selection-sorted list maintains sortedness, as long as the element
    is small enough and enough fuel is provided. Proceed by induction
    on [bl]. *)

Lemma cons_of_small_maintains_sort: forall bl y n,
    n = length bl ->
    y <=* bl ->
    sorted (selsort bl n) ->
    sorted (y :: selsort bl n).
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 3 stars, standard (selsort_sorted)  *)

(** Prove that [selsort] produced a sorted list when given
    sufficient fuel.  Proceed by induction on [n].  This proof
    will make use of a few previous lemmas. *)

Lemma selsort_sorted : forall n al,
    length al = n -> sorted (selsort al n).
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 1 star, standard (selection_sort_sorted)  *)

(** Prove that [selection_sort] produces a sorted list. *)

Lemma selection_sort_sorted : forall al,
    sorted (selection_sort al).
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 1 star, standard (selection_sort_is_correct)  *)

(** Finish the proof of correctness! *)

Theorem selection_sort_is_correct :
  is_a_sorting_algorithm selection_sort.
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 5 stars, advanced, optional (selection_sort_is_correct_multiset)  *)

(** Uncomment the next line, and prove the correctness of
    [selection_sort] using multisets instead of permutations.  We
    haven't tried this yet!  Send us your proof so we can add it as a
    solution. *)

(* From VFA Require Import Multiset. *)

(** [] *)

(* ################################################################# *)
(** * Recursive Functions That are Not Structurally Recursive *)

(** We used fuel above to create a structurally recursive
    version of [selsort] that Coq would accept as terminating.  The
    amount of fuel decreased at each call, until it reached zero.
    Since the fuel argument was structurally decreasing, Coq accepted
    the definition.  But it complicated the implementation of
    [selsort] and the proofs about it.

    Coq provides an experimental command [Function] that implements a
    similar idea as fuel, but without requiring the function
    definition to be structurally recursive.  Instead, the function is
    annotated with a _measure_ that is decreasing at each recursive
    call. To activate this experimental command, we need to load a
    library. *)

Require Import Recdef.  (* needed for [measure] feature *)

(** Now we can add a [measure] annotation on the definition of
    [selsort] to tell Coq that each recursive call decreases the
    length of [l]: *)

Function selsort' l {measure length l} :=
  match l with
  | [] => []
  | x :: r => let (y, r') := select x r
            in y :: selsort' r'
end.

(** The [measure] annotation takes two parameters, a measure
    function and an argument name.  Above, the function is [length]
    and the argument is [l].  The function must return a [nat] when
    applied to the argument.  Coq then challenges us to prove that
    [length] applied to [l] is actually decreasing at every recursive
    call. *)

Proof.
  intros.
  assert (Hperm: Permutation (x :: r) (y :: r')).
  { apply select_perm. auto. }
  apply Permutation_length in Hperm.
  inv Hperm. simpl. omega.
Defined.

(** The proof must end with [Defined] instead of [Qed].  That
    ensures the function's body can be used in computation.  For
    example, the following unit test succeeds, but try changing
    [Defined] to [Qed] and see how it gets stuck. *)

Example selsort'_example : selsort' [3;1;4;1;5;9;2;6;5] = [1;1;2;3;4;5;5;6;9].
Proof. reflexivity. Qed.

(** The definition of [selsort'] is completed by the [Function]
    command using a helper function that it generates,
    [selsort'_terminate].  Neither of them is going to be useful to
    unfold in proofs: *)

Print selsort'.
Print selsort'_terminate.

(** Instead, anywhere you want to unfold or simplify [selsort'], you
    should now rewrite with [selsort'_equation], which was
    automatically defined by the [Function] command: *)

Check selsort'_equation.

(** **** Exercise: 2 stars, standard (selsort'_perm)  *)

(** Hint: Follow the same strategy as [selsort_perm]. In our solution,
    there was only a one-line change. *)

Lemma selsort'_perm : forall n l,
    length l = n -> Permutation l (selsort' l).
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 5 stars, advanced, optional (selsort'_correct)  *)

(** Prove the correctness of [selsort']. We haven't tried this yet!
    Send us your proof so we can add it as a solution. *)

(** [] *)



(* 2020-08-07 17:08 *)
