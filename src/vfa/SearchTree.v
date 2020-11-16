(** * SearchTree: Binary Search Trees *)

(** We have implemented maps twice so far: with lists in
    [Lists], and with higher-order functions in [Maps].
    Those are simple but inefficient implementations: looking up the
    value bound to a given key takes time linear in the number of
    bindings, both in the worst and expected case. *)

(** If the type of keys can be totally ordered -- that is, it supports
    a well-behaved [<=] comparison -- then maps can be implemented with
    _binary search trees_ (BSTs).  Insert and lookup operations on
    BSTs take time proportional to the height of the tree.  If the
    tree is balanced, the operations therefore take logarithmic time. *)

(** If you don't recall BSTs or haven't seen them in a while, see
    Wikipedia or read any standard textbook; for example:

    - Section 3.2 of _Algorithms, Fourth Edition_, by Sedgewick and
      Wayne, Addison Wesley 2011; or

    - Chapter 12 of _Introduction to Algorithms, 3rd Edition_, by
      Cormen, Leiserson, and Rivest, MIT Press 2009. *)

From Coq Require Import String.  (* for an example, and manual grading *)
From Coq Require Import Logic.FunctionalExtensionality.
From VFA Require Import Perm.
From VFA Require Import Maps.
From VFA Require Import Sort.

(* ################################################################# *)
(** * BST Implementation *)

(** We use [nat] as the key type in our implementation of BSTs,
    since it has a convenient total order [<=?] with lots of theorems
    and automation available. *)

Definition key := nat.

(** [E] represents the empty map.  [T l k v r] represents the
    map that binds [k] to [v], along with all the bindings in [l] and
    [r].  No key may be bound more than once in the map. *)

Inductive tree (V : Type) : Type :=
| E
| T (l : tree V) (k : key) (v : V) (r : tree V).

Arguments E {V}.
Arguments T {V}.

(** An example tree:

      4 -> "four"
      /        \
     /          \
  2 -> "two"   5 -> "five"
*)

Definition ex_tree : tree string :=
  (T (T E 2 "two" E) 4 "four" (T E 5 "five" E))%string.

(** [empty_tree] contains no bindings. *)

Definition empty_tree {V : Type} : tree V :=
  E.

(** [bound k t] is whether [k] is bound in [t]. *)

Fixpoint bound {V : Type} (x : key) (t : tree V) :=
  match t with
  | E => false
  | T l y v r => if x <? y then bound x l
                else if x >? y then bound x r
                     else true
  end.

(** [lookup d k t] is the value bound to [k] in [t], or is default
    value [d] if [k] is not bound in [t]. *)

Fixpoint lookup {V : Type} (d : V) (x : key) (t : tree V) : V :=
  match t with
  | E => d
  | T l y v r => if x <? y then lookup d x l
                else if x >? y then lookup d x r
                     else v
  end.

(** [insert k v t] is the map containing all the bindings of [t] along
    with a binding of [k] to [v]. *)

Fixpoint insert {V : Type} (x : key) (v : V) (t : tree V) : tree V :=
  match t with
  | E => T E x v E
  | T l y v' r => if x <? y then T (insert x v l) y v' r
                 else if x >? y then T l y v' (insert x v r)
                      else T l x v r
  end.

(** Note that [insert] is a _functional_ aka _persistent_
    implementation: [t] is not changed. *)

Module Tests.

(** Here are some unit tests to check that BSTs behave the way we
    expect. *)

  Open Scope string_scope.

  Example bst_ex1 :
    insert 5 "five" (insert 2 "two" (insert 4 "four" empty_tree)) = ex_tree.
  Proof. reflexivity. Qed.

  Example bst_ex2 : lookup "" 5 ex_tree = "five".
  Proof. reflexivity. Qed.

  Example bst_ex3 : lookup "" 3 ex_tree = "".
  Proof. reflexivity. Qed.

  Example bst_ex4 : bound 3 ex_tree = false.
  Proof. reflexivity. Qed.

End Tests.

(** Although we can spot-check the behavior of BST operations with
    unit tests like these, we of course should prove general theorems
    about their correctness.  We will do that later in the chapter. *)

(* ################################################################# *)
(** * BST Invariant *)

(** The implementations of [lookup] and [insert] assume that
    values of type [tree] obey the _BST invariant_: for any non-empty
    node with key [k], all the values of the left subtree are less
    than [k] and all the values of the right subtree are greater than
    [k].  But that invariant is not part of the definition of
    [tree]. For example, the following tree is not a BST: *)

Module NotBst.
  Open Scope string_scope.

  Definition t : tree string :=
    T (T E 5 "five" E) 4 "four" (T E 2 "two" E).

  (** The [insert] function we wrote above would never produce
      such a tree, but we can still construct it by manually applying
      [T]. When we try to lookup [2] in that tree, we get the wrong
      answer, because [lookup] assumes [2] is in the left subtree: *)

  Example not_bst_lookup_wrong :
    lookup "" 2 t <> "two".
  Proof.
    simpl. unfold not. intros contra. discriminate.
  Qed.
End NotBst.

(** So, let's formalize the BST invariant. Here's one way to do
    so.  First, we define a helper [ForallT] to express that idea that
    a predicate holds at every node of a tree: *)

Fixpoint ForallT {V : Type} (P: key -> V -> Prop) (t: tree V) : Prop :=
  match t with
  | E => True
  | T l k v r => P k v /\ ForallT P l /\ ForallT P r
  end.

(** Second, we define the BST invariant:

    - An empty tree is a BST.

    - A non-empty tree is a BST if all its left nodes have a lesser
      key, its right nodes have a greater key, and the left and
      right subtrees are themselves BSTs. *)

Inductive BST {V : Type} : tree V -> Prop :=
| BST_E : BST E
| BST_T : forall l x v r,
    ForallT (fun y _ => y < x) l ->
    ForallT (fun y _ => y > x) r ->
    BST l ->
    BST r ->
    BST (T l x v r).

Hint Constructors BST.

(** Let's check that [BST] correctly classifies a couple of example
    trees: *)

Example is_BST_ex :
  BST ex_tree.
Proof.
  unfold ex_tree.
  repeat (constructor; try omega).
Qed.

Example not_BST_ex :
  ~ BST NotBst.t.
Proof.
  unfold NotBst.t. intros contra.
  inv contra. inv H3. omega.
Qed.

(** **** Exercise: 1 star, standard (empty_tree_BST)  *)

(** Prove that the empty tree is a BST. *)

Theorem empty_tree_BST : forall (V : Type),
    BST (@empty_tree V).
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 4 stars, standard (insert_BST)  *)

(** Prove that [insert] produces a BST, assuming it is given one.

    Start by proving this helper lemma, which says that [insert]
    preserves any node predicate. Proceed by induction on [t]. *)

Lemma ForallT_insert : forall (V : Type) (P : key -> V -> Prop) (t : tree V),
    ForallT P t -> forall (k : key) (v : V),
      P k v -> ForallT P (insert k v t).
Proof.
  (* FILL IN HERE *) Admitted.

(** Now prove the main theorem. Proceed by induction on the evidence
    that [t] is a BST. *)

Theorem insert_BST : forall (V : Type) (k : key) (v : V) (t : tree V),
    BST t -> BST (insert k v t).
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)

(** Since [empty_tree] and [insert] are the only operations that
    create BSTs, we are guaranteed that any [tree] is a BST -- unless
    it was constructed manually with [T].  It would therefore make
    sense to limit the use of [T] to only within the tree operations,
    rather than expose it.  Coq, like OCaml and other functional
    languages, can do this with its module system.  See [ADT] for
    details. *)

(* ################################################################# *)
(** * Correctness of BST Operations *)

(** To prove the correctness of [lookup] and [bound], we need
    specifications for them.  We'll study two different techniques for
    that in this chapter. *)

(** The first is called _algebraic specification_.  With it, we write
    down equations relating the results of operations.  For example,
    we could write down equations like the following to specify the
    [+] and [*] operations:

      (a + b) + c = a + (b + c)
      a + b = b + a
      a + 0 = a
      (a * b) * c = a * (b * c)
      a * b = b * a
      a * 1 = a
      a * 0 = 0
      a * (b + c) = a * b + a * c

    For BSTs, let's examine how [lookup] should interact with
    when applied to other operations.  It is easy to see what needs to
    be true for [empty_tree]: looking up any value at all in the empty
    tree should fail and return the default value:

      lookup d k empty_tree = d

    What about non-empty trees?  The only way to build a non-empty
    tree is by applying [insert k v t] to an existing tree [t]. So it
    suffices to describe the behavior of [lookup] on the result of an
    arbitrary [insert] operation. There are two cases.  If we look up
    the same key that was just inserted, we should get the value that
    was inserted with it:

      lookup d k (insert k v t) = v

    If we look up a different key than was just inserted, the insert
    should not affect the answer -- which should be the same as if we
    did the lookup in the original tree before the insert occured:

      lookup d k' (insert k v t) = lookup d k' t      if k <> k'

    These three basic equations specify the correct behavior of maps.
    Let's prove that they hold. *)

Theorem lookup_empty : forall (V : Type) (d : V) (k : key),
    lookup d k empty_tree = d.
Proof.
  auto.
Qed.

Theorem lookup_insert_eq : forall (V : Type) (t : tree V) (d : V) (k : key) (v : V),
    lookup d k (insert k v t)  = v.
Proof.
  induction t; intros; simpl.
  - bdestruct (k <? k); try omega; auto.
  - bdestruct (k <? k0); bdestruct (k0 <? k); simpl; try omega; auto.
    + bdestruct (k <? k0); bdestruct (k0 <? k); try omega; auto.
    + bdestruct (k <? k0); bdestruct (k0 <? k); try omega; auto.
    + bdestruct (k0 <? k0); try omega; auto.
Qed.

(** The basic method of that proof is to repeatedly [bdestruct]
    everything in sight, followed by generous use of [omega] and
    [auto]. Let's automate that. *)

Ltac bdestruct_guard :=
  match goal with
  | |- context [ if ?X =? ?Y then _ else _ ] => bdestruct (X =? Y)
  | |- context [ if ?X <=? ?Y then _ else _ ] => bdestruct (X <=? Y)
  | |- context [ if ?X <? ?Y then _ else _ ] => bdestruct (X <? Y)
  end.

Ltac bdall :=
  repeat (simpl; bdestruct_guard; try omega; auto).

Theorem lookup_insert_eq' :
  forall (V : Type) (t : tree V) (d : V) (k : key) (v : V),
    lookup d k (insert k v t) = v.
Proof.
  induction t; intros; bdall.
Qed.

(** The tactic immediately pays off in proving the third
    equation. *)

Theorem lookup_insert_neq :
  forall (V : Type) (t : tree V) (d : V) (k k' : key) (v : V),
   k <> k' -> lookup d k' (insert k v t) = lookup d k' t.
Proof.
  induction t; intros; bdall.
Qed.

(** Perhaps surprisingly, the proofs of these results do not
    depend on whether [t] satisfies the BST invariant.  That's because
    [lookup] and [insert] follow the same path through the tree, so
    even if nodes are in the "wrong" place, they are consistently
    "wrong". *)

(** **** Exercise: 3 stars, standard, optional (bound_correct)  *)

(** Specify and prove the correctness of [bound]. State and prove
    three theorems, inspired by those we just proved for [lookup]. If
    you have the right theorem statements, the proofs should all be
    quite easy -- thanks to [bdall]. *)

(* FILL IN HERE *)

(* Do not modify the following line: *)
Definition manual_grade_for_bound_correct : option (nat*string) := None.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (bound_default)  *)

(** Prove that if [bound] returns [false], then [lookup] returns
    the default value. Proceed by induction on the tree. *)

Theorem bound_default :
  forall (V : Type) (k : key) (d : V) (t : tree V),
    bound k t = false ->
    lookup d k t = d.
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)

(* ################################################################# *)
(** * BSTs vs. Higher-order Functions (Optional) *)

(** The three theorems we just proved for [lookup] should seem
    familiar: we proved equivalent theorems in [Maps] for maps
    defined as higher-order functions. *)

(** - [lookup_empty] and [t_apply_empty] both state that the empty map
      binds all keys to the default value. *)

Check lookup_empty : forall (V : Type) (d : V) (k : key),
    lookup d k empty_tree = d.

Check t_apply_empty : forall (V : Type) (k : key) (d : V),
    t_empty d k = d.

(** - [lookup_insert_eq] and [t_update_eq] both state that updating a map
      then looking for the updated key produces the updated value. *)

Check lookup_insert_eq : forall (V : Type) (t : tree V) (d : V) (k : key) (v : V),
    lookup d k (insert k v t) = v.

Check t_update_eq : forall (V : Type) (m : total_map V) (k : key) (v : V),
    (t_update m k v) k = v.

(** - [lookup_insert_neq] and [t_update_neq] both state that updating
      a map then looking for a different key produces the same value
      as the original map. *)

Check lookup_insert_neq :
  forall (V : Type) (t : tree V) (d : V) (k k' : key) (v : V),
    k <> k' -> lookup d k' (insert k v t) = lookup d k' t.

Check t_update_neq : forall (V : Type) (v : V) (k k' : key) (m : total_map V),
    k <> k' -> (t_update m k v) k' = m k'.

(** In [Maps], we also proved three other theorems about the
    behavior of functional maps on various combinations of updates and
    lookups: *)

Check t_update_shadow : forall (V : Type) (m : total_map V) (v1 v2 : V) (k : key),
    t_update (t_update m k v1) k v2 = t_update m k v2.

Check t_update_same : forall (V : Type) (k : key) (m : total_map V),
    t_update m k (m k) = m.

Check t_update_permute :
  forall (V : Type) (v1 v2 : V) (k1 k2 : key) (m : total_map V),
    k2 <> k1 ->
    t_update (t_update m k2 v2) k1 v1 = t_update (t_update m k1 v1) k2 v2.

(** Let's prove analogues to these three theorems for search trees.

    Hint: you do not need to unfold the definitions of [empty_tree],
    [insert], or [lookup].  Instead, use [lookup_insert_eq] and
    [lookup_insert_neq]. *)

(** **** Exercise: 2 stars, standard, optional (lookup_insert_shadow)  *)

Lemma lookup_insert_shadow :
  forall (V : Type) (t : tree V) (v v' d: V) (k k' : key),
    lookup d k' (insert k v (insert k v' t)) = lookup d k' (insert k v t).
Proof.
  intros. bdestruct (k =? k').
  (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 2 stars, standard, optional (lookup_insert_same)  *)

Lemma lookup_insert_same :
  forall (V : Type) (k k' : key) (d : V) (t : tree V),
    lookup d k' (insert k (lookup d k t) t) = lookup d k' t.
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 2 stars, standard, optional (lookup_insert_permute)  *)

Lemma lookup_insert_permute :
  forall (V : Type) (v1 v2 d : V) (k1 k2 k': key) (t : tree V),
    k1 <> k2 ->
    lookup d k' (insert k1 v1 (insert k2 v2 t))
    = lookup d k' (insert k2 v2 (insert k1 v1 t)).
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)

(** Our ability to prove these lemmas without reference to the
    underlying tree implementation demonstrates they hold for any map
    implementation that satisfies the three basic equations. *)

(** Each of these lemmas just proved was phrased as an equality
    between the results of looking up an arbitrary key [k'] in two
    maps.  But the lemmas for the function-based maps were phrased as
    direct equalities between the maps themselves.

    Could we state the tree lemmas with direct equalities?  For
    [insert_shadow], the answer is yes: *)

Lemma insert_shadow_equality : forall (V : Type) (t : tree V) (k : key) (v v' : V),
    insert k v (insert k v' t) = insert k v t.
Proof.
  induction t; intros; bdall.
  - rewrite IHt1; auto.
  - rewrite IHt2; auto.
Qed.

(** But the other two direct equalities on BSTs do not necessarily
    hold. *)

(** **** Exercise: 3 stars, standard, optional (direct_equalities_break)  *)

(** Prove that the other equalities do not hold.  Hint: find a counterexample
    first on paper, then use the [exists] tactic to instantiate the theorem
    on your counterexample.  The simpler your counterexample, the simpler
    the rest of the proof will be. *)

Lemma insert_same_equality_breaks :
  exists (V : Type) (d : V) (t : tree V) (k : key),
      insert k (lookup d k t) t <> t.
Proof.
  (* FILL IN HERE *) Admitted.

Lemma insert_permute_equality_breaks :
  exists (V : Type) (v1 v2 : V) (k1 k2 : key) (t : tree V),
    k1 <> k2 /\ insert k1 v1 (insert k2 v2 t) <> insert k2 v2 (insert k1 v1 t).
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)

(* ################################################################# *)
(** * Converting a BST to a List *)

(** Let's add a new operation to our BST: converting it to an
    _association list_ that contains the key--value bindings from the
    tree stored as pairs.  If that list is sorted by the keys, then
    any two trees that represent the same map would be converted to
    the same list. Here's a function that does so with an in-order
    traversal of the tree: *)

Fixpoint elements {V : Type} (t : tree V) : list (key * V) :=
  match t with
  | E => []
  | T l k v r => elements l ++ [(k, v)] ++ elements r
  end.

Example elements_ex :
    elements ex_tree = [(2, "two"); (4, "four"); (5, "five")]%string.
Proof. reflexivity. Qed.

(** Here are three desirable properties for [elements]:

    1. The list has the same bindings as the tree.

    2. The list is sorted by keys.

    3. The list contains no duplicates.

    Let's formally specify and verify them. *)

(* ================================================================= *)
(** ** Part 1: Same Bindings *)

(** We want to show that a binding is in [elements t] iff it's in
    [t]. We'll prove the two directions of that bi-implication
    separately:

    - [elements] is _complete_: if a binding is in [t] then it's in
      [elements t].

    - [elements] is _correct_: if a binding is in [elements t] then
      it's in [t].  *)

(** Getting the specification of completeness right is a little
    tricky.  It's tempting to start off with something too simple like
    this: *)

Definition elements_complete_broken_spec :=
  forall (V : Type) (k : key) (v d : V) (t : tree V),
    BST t ->
    lookup d k t = v ->
    In (k, v) (elements t).

(** The problem with that specification is how it handles the default
    element [d]: the specification would incorrectly require [elements
    t] to contain a binding [(k, d)] for all keys [k] unbound in
    [t]. That would force [elements t] to be infinitely long, since
    it would have to contain a binding for every natural number. We can
    observe this problem right away if we begin the proof: *)

Theorem elements_complete_broken : elements_complete_broken_spec.
Proof.
  unfold elements_complete_broken_spec. intros. induction t.
  - (* t = E *) simpl.
    (** We have nothing to work with, since [elements E] is [[]]. *)
Abort.

(** The solution is to check first to see whether [k] is bound in [t].
    Only bound keys need be in the list of elements: *)

Definition elements_complete_spec :=
  forall (V : Type) (k : key) (v d : V) (t : tree V),
    BST t ->
    bound k t = true ->
    lookup d k t = v ->
    In (k, v) (elements t).

(** **** Exercise: 3 stars, standard (elements_complete)  *)

(** Prove that [elements] is complete. Proceed by induction on [t]. *)

Theorem elements_complete : elements_complete_spec.
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)

(** The specification for correctness likewise mentions that the
    key must be bound: *)

Definition elements_correct_spec :=
  forall (V : Type) (k : key) (v d : V) (t : tree V),
    BST t ->
    In (k, v) (elements t) ->
    bound k t = true /\ lookup d k t = v.

(** Proving correctness requires more work than completeness.

    [BST] uses [ForallT] to say that all nodes in the left/right
    subtree have smaller/greater keys than the root.  We need to
    relate [ForallT], which expresses that all nodes satisfy a
    property, to [Forall], which expresses that all list elements
    satisfy a property.

    We begin with this lemma about [Forall], which is missing from the
    standard library. *)

Lemma Forall_app : forall (A: Type) (P : A -> Prop) (l1 l2 : list A),
    Forall P l1 -> Forall P l2 -> Forall P (l1 ++ l2).
Proof.
  induction l1; intros; simpl; auto; inv H; constructor; auto.
Qed.

(** **** Exercise: 2 stars, standard (elements_preserves_forall)  *)

(** Prove that if a property [P] holds of every node in a tree [t],
    then that property holds of every pair in [elements t]. Proceed
    by induction on [t].

    There is a little mismatch between the type of [P] in [ForallT]
    and the type of the property accepted by [Forall], so we have to
    _uncurry_ [P] when we pass it to [Forall]. (See [Poly] for
    more about uncurrying.) The single quote used below is the Coq
    syntax for doing a pattern match in the function arguments. *)

Definition uncurry {X Y Z : Type} (f : X -> Y -> Z) '(a, b) :=
  f a b.

Hint Transparent uncurry.

Lemma elements_preserves_forall : forall (V : Type) (P : key -> V -> Prop) (t : tree V),
    ForallT P t ->
    Forall (uncurry P) (elements t).
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 2 stars, standard (elements_preserves_relation)  *)

(** Prove that if all the keys in [t] are in a relation [R] with a
    distinguished key [k'], then any key [k] in [elements t] is also
    related by [R] to [k']. For example, [R] could be [<], in which
    case the lemma says that if all the keys in [t] are less than
    [k'], then all the keys in [elements t] are also less than
    [k'].

    Hint: you don't need induction.  Immediately look for a way
    to use [elements_preserves_forall] and library theorem
    [Forall_forall]. *)

Lemma elements_preserves_relation :
  forall (V : Type) (k k' : key) (v : V) (t : tree V) (R : key -> key -> Prop),
    ForallT (fun y _ => R y k') t
    -> In (k, v) (elements t)
    -> R k k'.
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 4 stars, standard (elements_correct)  *)

(** Prove that [elements] is correct. Proceed by induction on the
    evidence that [t] is a BST. *)

Theorem elements_correct : elements_correct_spec.
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)

(** The inverses of completeness and correctness also should hold:

    - inverse completeness: if a binding is not in [t] then it's not
      in [elements t].

    - inverse correctness: if a binding is not in [elements t] then
      it's not in [t].

    Let's prove that they do. *)

(** **** Exercise: 2 stars, advanced (elements_complete_inverse)  *)

(** This inverse doesn't require induction.  Look for a way to use
    [elements_correct] to quickly prove the result. *)

Theorem elements_complete_inverse :
  forall (V : Type) (k : key) (v : V) (t : tree V),
    BST t ->
    bound k t = false ->
    ~ In (k, v) (elements t).
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 4 stars, advanced (elements_correct_inverse)  *)

(** Prove the inverse.  First, prove this helper lemma by induction on
    [t]. *)

Lemma bound_value : forall (V : Type) (k : key) (t : tree V),
    bound k t = true -> exists v, forall d, lookup d k t = v.
Proof.
  (* FILL IN HERE *) Admitted.

(** Prove the main result.  You don't need induction. *)

Theorem elements_correct_inverse :
  forall (V : Type) (k : key) (t : tree V),
    BST t ->
    (forall v, ~ In (k, v) (elements t)) ->
    bound k t = false.
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)

(* ================================================================= *)
(** ** Part 2: Sorted (Advanced) *)

(** We want to show that [elements] is sorted by keys.  We follow a
    proof technique contributed by Lydia Symmons et al.*)

(** **** Exercise: 3 stars, advanced (sorted_app)  *)

(** Prove that inserting an intermediate value between two lists
    maintains sortedness. Proceed by induction on the evidence
    that [l1] is sorted. *)

Lemma sorted_app: forall l1 l2 x,
  Sort.sorted l1 -> Sort.sorted l2 ->
  Forall (fun n => n < x) l1 -> Forall (fun n => n > x) l2 ->
  Sort.sorted (l1 ++ x :: l2).
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 4 stars, advanced (sorted_elements)  *)

(** The keys in an association list are the first elements of every
    pair: *)

Definition list_keys {V : Type} (lst : list (key * V)) :=
  map fst lst.

(** Prove that [elements t] is sorted by keys. Proceed by induction
    on the evidence that [t] is a BST. *)

Theorem sorted_elements : forall (V : Type) (t : tree V),
    BST t -> Sort.sorted (list_keys (elements t)).
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)

(* ================================================================= *)
(** ** Part 3: No Duplicates (Advanced and Optional) *)

(** We want to show that [elements t] contains no duplicate
    bindings. Tree [t] itself cannot contain any duplicates, so the
    list that [elements] produces shouldn't either. The standard
    library already contains a helpful inductive proposition,
    [NoDup]. *)

Print NoDup.

(** The library is missing a theorem, though, about [NoDup] and [++].
    To state that theorem, we first need to formalize what it means
    for two lists to be disjoint: *)

Definition disjoint {X:Type} (l1 l2: list X) := forall (x : X),
    In x l1 -> ~ In x l2.

(** **** Exercise: 3 stars, advanced, optional (NoDup_append)  *)

(** Prove that if two lists are disjoint, appending them preserves
    [NoDup].  Hint: You might already have proved this theorem in an
    advanced exercise in [IndProp]. *)

Lemma NoDup_append : forall (X:Type) (l1 l2: list X),
  NoDup l1 -> NoDup l2 -> disjoint l1 l2 ->
  NoDup (l1 ++ l2).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 4 stars, advanced, optional (elements_nodup_keys)  *)

(** Prove that there are no duplicate keys in the list returned
    by [elements]. Proceed by induction on the evidence that [t] is a
    BST. Make use of library theorems about [map] as needed. *)

Theorem elements_nodup_keys : forall (V : Type) (t : tree V),
    BST t ->
    NoDup (list_keys (elements t)).
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)

(** That concludes the proof of correctness of [elements]. *)

(* ################################################################# *)
(** * A Faster [elements] Implementation *)

(** The implemention of [elements] is inefficient because of how
    it uses the [++] operator.  On a balanced tree its running time is
    linearithmic, because it does a linear number of concatentations
    at each level of the tree. On an unbalanced tree it's quadratic
    time.  Here's a tail-recursive implementation than runs in linear
    time, regardless of whether the tree is balanced: *)

Fixpoint fast_elements_tr {V : Type} (t : tree V)
         (acc : list (key * V)) : list (key * V) :=
  match t with
  | E => acc
  | T l k v r => fast_elements_tr l ((k, v) :: fast_elements_tr r acc)
  end.

Definition fast_elements {V : Type} (t : tree V) : list (key * V) :=
  fast_elements_tr t [].

(** **** Exercise: 3 stars, standard (fast_elements_eq_elements)  *)

(** Prove that [fast_elements] and [elements] compute the same
    function. *)

Lemma fast_elements_tr_helper :
  forall (V : Type) (t : tree V) (lst : list (key * V)),
    fast_elements_tr t lst = elements t ++ lst.
Proof.
  (* FILL IN HERE *) Admitted.

Lemma fast_elements_eq_elements : forall (V : Type) (t : tree V),
    fast_elements t = elements t.
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)

(** Since the two implementations compute the same function, all
    the results we proved about the correctness of [elements]
    also hold for [fast_elements].  For example: *)

Corollary fast_elements_correct :
  forall (V : Type) (k : key) (v d : V) (t : tree V),
    BST t ->
    In (k, v) (fast_elements t) ->
    bound k t = true /\ lookup d k t = v.
Proof.
  intros. rewrite fast_elements_eq_elements in *.
  apply elements_correct; assumption.
Qed.

(** This corollary illustrates a general technique:  prove the correctness
    of a simple, slow implementation; then prove that the slow version
    is functionally equivalent to a fast implementation.  The proof of
    correctness for the fast implementation then comes "for free". *)

(* ################################################################# *)
(** * An Algebraic Specification of [elements] *)

(** The verification of [elements] we did above did not adhere to the
    algebraic specification approach, which would suggest that we look
    for equations of the form

      elements empty_tree = ...
      elements (insert k v t) = ... (elements t) ...

    The first of these is easy; we can trivially prove the following:
    *)

Lemma elements_empty : forall (V : Type),
    @elements V empty_tree = [].
Proof.
  intros. simpl. reflexivity.
Qed.

(** But for the second equation, we have to express the result of
    inserting [(k, v)] into the elements list for [t], accounting for
    ordering and the possibility that [t] may already contain a pair
    [(k, v')] which must be replaced.  The following rather ugly
    function will do the trick: *)

Fixpoint kvs_insert {V : Type} (k : key) (v : V) (kvs : list (key * V)) :=
  match kvs with
  | [] => [(k, v)]
  | (k', v') :: kvs' =>
    if k <? k' then (k, v) :: kvs
    else if k >? k' then (k', v') :: kvs_insert k v kvs'
         else (k, v) :: kvs'
  end.

(** That's not satisfactory, because the definition of
    [kvs_insert] is so complex. Moreover, this equation doesn't tell
    us anything directly about the overall properties of [elements t]
    for a given tree [t].  Nonetheless, we can proceed with a rather
    ugly verification. *)

(** **** Exercise: 3 stars, standard, optional (kvs_insert_split)  *)
Lemma kvs_insert_split :
  forall (V : Type) (v v0 : V) (e1 e2 : list (key * V)) (k k0 : key),
    Forall (fun '(k',_) => k' < k0) e1 ->
    Forall (fun '(k',_) => k' > k0) e2 ->
    kvs_insert k v (e1 ++ (k0,v0):: e2) =
    if k <? k0 then
      (kvs_insert k v e1) ++ (k0,v0)::e2
    else if k >? k0 then
           e1 ++ (k0,v0)::(kvs_insert k v e2)
         else
           e1 ++ (k,v)::e2.
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (kvs_insert_elements)  *)
Lemma kvs_insert_elements : forall (V : Type) (t : tree V),
    BST t ->
    forall (k : key) (v : V),
      elements (insert k v t) = kvs_insert k v (elements t).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################################# *)
(** * Model-based Specifications *)

(** At the outset, we mentioned studying two techniques for
    specifying the correctness of BST operations in this chapter.  The
    first was algebraic specification.

    Another approach to proving correctness of search trees is to
    relate them to our existing implementation of functional partial
    maps, as developed in [Maps]. To prove the correctness of a
    search-tree algorithm, we can prove:

    - Any search tree corresponds to some functional partial map,
      using a function or relation that we write down.

    - The [lookup] operation on trees gives the same result as the
      [find] operation on the corresponding map.

    - Given a tree and corresponding map, if we [insert] on the tree
      and [update] the map with the same key and value, the resulting
      tree and map are in correspondence.

    This approach is sometimes called _model-based specification_: we
    show that our implementation of a data type corresponds to a more
    more abstract _model_ type that we already understand. To reason
    about programs that use the implementation, it suffices to reason
    about the behavior of the abstract type, which may be
    significantly easier.  For example, we can take advantage of laws
    that we proved for the abstract type, like [update_eq] for
    functional maps, without having to prove them again for the
    concrete tree type.

    We also need to be careful here, because the type of functional
    maps as defined in [Maps] do not actually behave quite like
    our tree-based maps. For one thing, functional maps can be defined
    on an infinite number of keys, and there is no mechanism for
    enumerating over the key set. To maintain correspondence with our
    finite trees, we need to make sure that we consider only
    functional maps built by finitely many applications of constructor
    functions ([empty] and [update]). Also, thanks to functional
    extensionality, functional maps obey stronger equality laws than
    our trees do (as we investigated in the [direct_equalities]
    exercise above), so we should not be misled into thinking that
    every fact we can prove about abstract maps necessarily holds for
    concrete ones.

    Compared to the algebraic-specification approach described earlier
    in this chapter, the model-based approach can save some proof
    effort, especially if we already have a well-developed theory for
    the abstract model type.  On the other hand, we have to give an
    explicit _abstraction_ relation between trees and maps, and show
    that it is maintained by all operations. In the end, about the
    same amount of work is needed to show correctness, though the work
    shows up in different places depending on how the abstraction
    relation is defined. *)

(** We now give a model-based specification for trees in terms
    of functional partial maps. It is based on a simple abstraction
    relation that builds a functional map element by element. *)

Fixpoint map_of_list {V : Type} (el : list (key * V)) : partial_map V :=
  match el with
  | [] => empty
  | (k, v) :: el' => update (map_of_list el') k v
  end.

Definition Abs {V : Type} (t : tree V) : partial_map V :=
  map_of_list (elements t).

(** In general, model-based specifications may use an abstraction
    relation, allowing each concrete value to be related to multiple
    abstract values.  But in this case a simple abstraction _function_
    will do, assigning a unique abstract value to each concrete
    one. *)

(** One small difference between trees and functional maps is that
    applying the latter returns an [option V] which might be [None],
    whereas [lookup] returns a default value if key is not bound
    lookup fails.  We can easily provide a function on functional
    partial maps having the latter behavior. *)

Definition find {V : Type} (d : V) (k : key) (m : partial_map V) : V :=
  match m k with
  | Some v => v
  | None => d
  end.

(** We also need a [bound] operation on maps. *)

Definition map_bound {V : Type} (k : key) (m : partial_map V) : bool :=
  match m k with
  | Some _ => true
  | None => false
  end.

(** We now proceed to prove that each operation preserves (or establishes)
    the abstraction relationship in an appropriate way:

    concrete        abstract
    --------        --------
    empty_tree      empty
    bound           map_bound
    lookup          find
    insert          update
*)

(** The following lemmas will be useful, though you are not required
    to prove them. They can all be proved by induction on the list. *)

(** **** Exercise: 2 stars, standard, optional (in_fst)  *)
Lemma in_fst : forall (X Y : Type) (lst : list (X * Y)) (x : X) (y : Y),
    In (x, y) lst -> In x (map fst lst).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (in_map_of_list)  *)
Lemma in_map_of_list : forall (V : Type) (el : list (key * V)) (k : key) (v : V),
    NoDup (map fst el) ->
    In (k,v) el -> (map_of_list el) k = Some v.
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (not_in_map_of_list)  *)
Lemma not_in_map_of_list : forall (V : Type) (el : list (key * V)) (k : key),
    ~ In k (map fst el) -> (map_of_list el) k = None.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

Lemma empty_relate : forall (V : Type),
    @Abs V empty_tree = empty.
Proof.
  reflexivity.
Qed.

(** **** Exercise: 3 stars, standard, optional (bound_relate)  *)

Theorem bound_relate : forall (V : Type) (t : tree V) (k : key),
    BST t ->
    map_bound k (Abs t) = bound k t.
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 3 stars, standard, optional (lookup_relate)  *)

Lemma lookup_relate : forall (V : Type) (t : tree V) (d : V) (k : key),
    BST t -> find d k (Abs t) = lookup d k t.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (insert_relate)  *)
Lemma insert_relate : forall (V : Type) (t : tree V) (k : key) (v : V),
  BST t -> Abs (insert k v t) = update (Abs t) k v.
Proof.
  (* TODO: find a direct proof that doesn't rely on [kvs_insert_elements] *)
    unfold Abs.
  intros.
  rewrite kvs_insert_elements; auto.
  remember (elements t) as l.
  clear -l. (* clear everything not about [l] *)
  (* Hint: proceed by induction on [l]. *)
    (* FILL IN HERE *) Admitted.
(** [] *)

(** The previous three lemmas are in essence saying that the following
    diagrams commute.

             bound k
      t -------------------+
      |                    |
  Abs |                    |
      V                    V
      m -----------------> b
           map_bound k

            lookup d k
      t -----------------> v
      |                    |
  Abs |                    | Some
      V                    V
      m -----------------> Some v
             find d k

            insert k v
      t -----------------> t'
      |                    |
  Abs |                    | Abs
      V                    V
      m -----------------> m'
            update' k v

    Where we define:

      update' k v m = update m k v

*)

(** Functional partial maps lack a way to extract or iterate
    over their elements, so we cannot give an analogous abstract
    operation for [elements]. Instead, we can prove this trivial
    little lemma. *)

Lemma elements_relate : forall (V : Type) (t : tree V),
  BST t ->
  map_of_list (elements t) = Abs t.
Proof.
  unfold Abs. intros. reflexivity.
Qed.

(* ################################################################# *)
(** * An Alternative Abstraction Relation (Optional, Advanced) *)

(** There is often more than one way to specify a suitable abstraction
    relation between given concrete and abstract datatypes. The
    following exercises explore another way to relate search trees to
    functional partial maps without using [elements] as an
    intermediate step.

    We extend our definition of functional partial maps by adding a
    new primitive for combining two partial maps, which we call
    [union].  Our intention is that it only be used to combine maps
    with disjoint key sets; to keep the operation symmetric, we make
    the result be undefined on any key they have in common.  *)

Definition union {X} (m1 m2: partial_map X) : partial_map X :=
  fun k =>
    match (m1 k, m2 k) with
    | (None, None) => None
    | (None, Some v) => Some v
    | (Some v, None) => Some v
    | (Some _, Some _) => None
    end.

(** We can prove some simple properties of lookup and update on unions,
    which will prove useful later. *)

(** **** Exercise: 2 stars, standard, optional (union_collapse)  *)
Lemma union_left : forall {X} (m1 m2: partial_map X) k,
    m2 k = None -> union m1 m2 k = m1 k.
Proof.
(* FILL IN HERE *) Admitted.

Lemma union_right : forall {X} (m1 m2: partial_map X) k,
    m1 k = None ->
    union m1 m2 k = m2 k.
Proof.
(* FILL IN HERE *) Admitted.

Lemma union_both : forall {X} (m1 m2 : partial_map X) k v1 v2,
    m1 k = Some v1 ->
    m2 k = Some v2 ->
    union m1 m2 k = None.
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (union_update)  *)
Lemma union_update_right : forall {X} (m1 m2: partial_map X) k v,
    m1 k = None ->
    update (union m1 m2) k v = union m1 (update m2 k v).
Proof.
(* FILL IN HERE *) Admitted.

Lemma union_update_left : forall {X} (m1 m2: partial_map X) k v,
    m2 k = None ->
    update (union m1 m2) k v = union (update m1 k v) m2.
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

(** We can now write a direct conversion function from trees to maps
    based on the structure of the tree, and prove a basic property
    preservation result. *)

Fixpoint map_of_tree {V : Type} (t: tree V) : partial_map V :=
  match t with
  | E => empty
  | T l k v r => update (union (map_of_tree l) (map_of_tree r)) k v
  end.

(** **** Exercise: 3 stars, advanced, optional (map_of_tree_prop)  *)
Lemma map_of_tree_prop : forall (V : Type) (P : key -> V -> Prop) (t : tree V),
    ForallT P t ->
    forall k v, (map_of_tree t) k = Some v ->
           P k v.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** Finally, we define our new abstraction function, and prove the
    same lemmas as before. *)

Definition Abs' {V : Type} (t: tree V) : partial_map V :=
  map_of_tree t.

Lemma empty_relate' : forall (V : Type),
    @Abs' V empty_tree = empty.
Proof.
  reflexivity.
Qed.

(** **** Exercise: 3 stars, advanced, optional (bound_relate')  *)
Theorem bound_relate' : forall (V : Type) (t : tree V) (k : key),
    BST t ->
    map_bound k (Abs' t) = bound k t.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, advanced, optional (lookup_relate')  *)
Lemma lookup_relate' : forall (V : Type) (d : V) (t : tree V) (k : key),
    BST t -> find d k (Abs' t) = lookup d k t.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 4 stars, advanced, optional (insert_relate')  *)
Lemma insert_relate' : forall (V : Type) (k : key) (v : V) (t : tree V),
   BST t -> Abs' (insert k v t) = update (Abs' t) k v.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** The [elements_relate] lemma, which was trivial for our previous [Abs]
    function, is considerably harder this time.  We suggest starting with
    an auxiliary lemma. *)

(** **** Exercise: 3 stars, advanced, optional (map_of_list_app)  *)
Lemma map_of_list_app : forall (V : Type) (el1 el2: list (key * V)),
   disjoint (map fst el1) (map fst el2) ->
   map_of_list (el1 ++ el2) = union (map_of_list el1) (map_of_list el2).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 4 stars, advanced, optional (elements_relate')  *)
Lemma elements_relate' : forall (V : Type) (t : tree V),
  BST t ->
  map_of_list (elements t) = Abs' t.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################################# *)
(** * Efficiency of Search Trees *)

(** All the theory we've developed so far has been about correctness.
    But the reason we use binary search trees is that they are
    efficient.  That is, if there are [N] elements in a (reasonably
    well balanced) BST, each insertion or lookup takes about [log N]
    time.

    What could go wrong?

     1. The search tree might not be balanced.  In that case, each
        insertion or lookup will take as much as linear time.

        - SOLUTION: use an algorithm that ensures the trees stay
          balanced.  We'll do that in [Redblack].

     2. Our keys are natural numbers, and Coq's [nat] type takes linear
        time per comparison.  That is, computing (j <? k) takes time
        proportional to the value of [k-j].

        - SOLUTION: represent keys by a data type that has a more
          efficient comparison operator.  We used [nat] in this chapter
          because it's something easy to work with.

     3. There's no notion of running time in Coq.  That is, we can't
        say what it means that a Coq function "takes N steps to
        evaluate."  Therefore, we can't prove that binary search trees
        are efficient.

        - SOLUTION 1: Don't prove (in Coq) that they're efficient;
          just prove that they are correct.  Prove things about their
          efficiency the old-fashioned way, on pencil and paper.

        - SOLUTION 2: Prove in Coq some facts about the height of the
          trees, which have direct bearing on their efficiency.  We'll
          explore that in [Redblack].

        - SOLUTION 3: Apply bleeding-edge frameworks for reasoning
          about run-time of programs represented in Coq.

      4. Our functions in Coq are models of implementations in "real"
         programming languages.  What if the real implementations
         differ from the Coq models?

         - SOLUTION: Use Coq's [extraction] feature to derive the real
	   implementation (in Ocaml or Haskell) automatically from the
	   Coq function.  Or, use Coq's [Compute] or [Eval
	   native_compute] feature to compile and run the programs
	   efficiently inside Coq.  We'll explore [extraction] in a
	   [Extract]. *)

(* 2020-08-07 17:08 *)
