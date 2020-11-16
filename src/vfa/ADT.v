(** * ADT: Abstract Data Types *)

(** An _abstract data type_ (ADT) can be defined as a set of values
    together with some operations.  From the perspective of formal
    verification, the specifications of those operations should also
    be a part of an ADT.

    When we implemented BSTs in [SearchTree], we saw that
    maintaining a representation invariant was important to rule out
    trees that could never be constructed through operations of the
    data structure.  That invariant became a precondition for many
    operations, though there was no need for _clients_ of the data
    structure to know any details of the invariant.

    In this chapter we'll study a little of Coq's _module system_,
    which enables hiding some details of the implementation of an ADT,
    while also exposing the formal specification of the ADT.

    Some prior knowledge of an ML-style module system, especially
    OCaml's, will be helpful.  Here are some sources that cover it:

    - _Introduction to Objective Caml_, chapters 12 and 13.  Jason
      Hickey, 2008.  Available from
      https://ocaml.org/learn/books.html.

    - The OCaml System Manual, chapter 2.  Xavier Leroy et al.,
      2020. Available from
      http://caml.inria.fr/pub/docs/manual-ocaml/.  *)

From Coq Require Import String.  (* for manual grading *)
From VFA Require Import Perm.
From VFA Require Import Maps.
From VFA Require Import SearchTree.

(* ################################################################# *)
(** * The Table ADT *)

(** An _association table_ is an ADT that binds keys to values.  There
    are many other names for this concept, including _map_.  We've
    already used that name before, though, for a specific data
    structure using higher-order functions.  So for clarity in this
    chapter we use _table_.

    Below is a Coq [Module Type] that declares an _interface_ for the
    table ADT. A _parameter_ is like a definition, except it declares
    only the type of an identifier, not the value to which it is
    bound.  An _axiom_ is similarly like a theorem, except no proof is
    provided. *)

Module Type Table.

  (** A [table] is a binding from keys to values. It is _total_,
      meaning it binds all keys. *)
  Parameter table : Type.

  (** Keys are natural numbers. *)
  Definition key := nat.

  (** Values are an arbitrary type [V]. *)
  Parameter V : Type.

  (** The default value to which keys are bound. *)
  Parameter default : V.

  (** [empty] is the table that binds all keys to the default value. *)
  Parameter empty : table.

  (** [get k t] is the value [v] to which [k] is bound in [t]. *)
  Parameter get : key -> table -> V.

  (** [set k v t] is the table that binds [k] to [v] and otherwise has
      the same bindings as [t]. *)
  Parameter set : key -> V -> table -> table.

  (** The following three axioms are an equational specification for
      the table ADT. *)

  Axiom get_empty_default : forall (k : key),
      get k empty = default.

  Axiom get_set_same : forall (k : key) (v : V) (t : table),
      get k (set k v t) = v.

  Axiom get_set_other : forall (k k' : key) (v : V) (t : table),
      k <> k' -> get k' (set k v t) = get k' t.

End Table.

(* ################################################################# *)
(** * Implementing [Table] with Functions *)

(** We can _implement_ [Table] with a [Module] that is
    parameterized on the type of values -- or, rather, parameterized
    on a module that contains such a type.  A parameterized module is
    also called a _functor_.

    Module type [ValType] says that there must be a type named [V],
    with a default value provided: *)

Module Type ValType.
  Parameter V : Type.
  Parameter default : V.
End ValType.

(** Functor [FunTable] takes as input a module of type
    [ValType], which must therefore contain a type [V].  As output,
    [FunTable] produces a module of type [Table].  By writing [<:
    Table], below, we ask Coq to check that the output module contains
    all the components required by [Table]. *)

Module FunTable (VT : ValType) <: Table.

  Definition V := VT.V.
  Definition default := VT.default.
  Definition key := nat.

  (** A [table] is a function from keys to values. *)
  Definition table := key -> V.

  Definition empty : table :=
    fun _ => default.

  Definition get (k : key) (t : table) : V :=
    t k.

  Definition set (k : key) (v : V) (t : table) : table :=
    fun k' => if k =? k' then v else t k'.

  (** The implementation must prove the theorems that the interface
      specified as axioms. *)

  Theorem get_empty_default: forall (k : key),
      get k empty = default.
  Proof. intros. unfold get, empty. reflexivity. Qed.

  Theorem get_set_same: forall (k : key) (v : V) (t : table),
      get k (set k v t) = v.
  Proof. intros. unfold get, set. bdall. Qed.

  Theorem get_set_other: forall (k k' : key) (v : V) (t : table),
      k <> k' -> get k' (set k v t) = get k' t.
  Proof. intros. unfold get, set. bdall. Qed.
End FunTable.

(** As an example, let's instantiate [FunTable] with strings as
    values. *)

Module StringVal.
  Definition V := string.
  Definition default := ""%string.
End StringVal.

Module FunTableExamples.

  Module StringFunTable := FunTable StringVal.
  Import StringFunTable.
  Open Scope string_scope.

  Example ex1 : get 0 empty = "".
  Proof. reflexivity. Qed.

  Example ex2 : get 0 (set 0 "A" empty) = "A".
  Proof. reflexivity. Qed.

  Example ex3 : get 1 (set 0 "A" empty) = "".
  Proof. reflexivity. Qed.

End FunTableExamples.

(** **** Exercise: 2 stars, standard, optional (NatFunTableExamples)  *)

(** Define a module that uses [FunTable] to implement a table mapping
    keys to values, where the values have type [nat], with a default of [0].
    Write unit tests to check the operation of [get] and [set]. *)

Module NatFunTableExamples.
  (* FILL IN HERE *)
End NatFunTableExamples.

(** [] *)

(* ################################################################# *)
(** * Implementing [Table] with Lists *)

(** **** Exercise: 3 stars, standard (lists_table)  *)

(** Use association lists to implement [Table]. *)

Module ListsTable (VT : ValType) <: Table.

  Definition V := VT.V.
  Definition default := VT.default.
  Definition key := nat.
  Definition table := list (key * V).

  Definition empty : table := [].

  Fixpoint get (k : key) (t : table) : V
    (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

  Definition set (k : key) (v : V) (t : table) : table
    (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

  Theorem get_empty_default: forall (k : key),
      get k empty = default.
  Proof.
    (* FILL IN HERE *) Admitted.

  Theorem get_set_same: forall (k : key) (v : V) (t : table),
      get k (set k v t) = v.
  Proof.
    (* FILL IN HERE *) Admitted.

  Theorem get_set_other: forall (k k' : key) (v : V) (t : table),
      k <> k' -> get k' (set k v t) = get k' t.
  Proof.
    (* FILL IN HERE *) Admitted.

End ListsTable.

(** Instantiate your table and prove the following facts. *)

Module StringListsTableExamples.

  Module StringListsTable := ListsTable StringVal.
  Import StringListsTable.
  Open Scope string_scope.

  Example ex1 : get 0 empty = "".
  Proof.
    (* FILL IN HERE *) Admitted.

  Example ex2 : get 0 (set 0 "A" empty) = "A".
  Proof.
    (* FILL IN HERE *) Admitted.

  Example ex3 : get 1 (set 0 "A" empty) = "".
  Proof.
    (* FILL IN HERE *) Admitted.

End StringListsTableExamples.

(** [] *)

(* ################################################################# *)
(** * Implementing [Table] with BSTs *)

(** Tables implemented with functions and association lists are, of course,
    inefficient.  For a more efficient implementation, we can use BSTs. *)

Module TreeTable (VT : ValType) <: Table.

  Definition V := VT.V.
  Definition default := VT.default.
  Definition key := nat.
  Definition table := tree V.

  Definition empty : table :=
    @empty_tree V.

  Definition get (k : key) (t: table) : V :=
    lookup default k t.

  Definition set (k : key) (v : V) (t : table) : table :=
    insert k v t.

  (** The three basic equations we proved about [tree] in
      [SearchTree] make short work of the theorems we need to
      prove for [Table]. *)

  Theorem get_empty_default: forall (k : key),
      get k empty = default.
  Proof.
    apply lookup_empty.
  Qed.

  Theorem get_set_same: forall (k : key) (v : V) (t : table),
      get k (set k v t) = v.
  Proof.
    intros. unfold get, set. apply lookup_insert_eq.
  Qed.

  Theorem get_set_other: forall (k k' : key) (v : V) (t : table),
      k <> k' -> get k' (set k v t) = get k' t.
  Proof.
    intros. unfold get, set. apply lookup_insert_neq. assumption.
  Qed.

End TreeTable.

(* ################################################################# *)
(** * Tables with an [elements] Operation *)

(** Now let's consider a richer interface [ETable] for Tables that support
    [bound] and [elements] operation. *)

(* ================================================================= *)
(** ** A First Attempt at [ETable] *)

Module Type ETable_first_attempt.

  (** [Include], as the name suggests, includes all the declarations
      from [Table].  Not only does that save keystrokes, it also means
      if we ever update [Table] to have new operations or new types,
      they automatically get included here, too. *)
  Include Table.

  Parameter bound : key -> table -> bool.
  Parameter elements : table -> list (key * V).

  Axiom elements_complete : forall (k : key) (v : V) (t : table),
      bound k t = true ->
      get k t = v ->
      In (k, v) (elements t).

  Axiom elements_correct : forall (k : key) (v : V) (t : table),
      In (k, v) (elements t) ->
      bound k t = true /\ get k t = v.

End ETable_first_attempt.

(** We proved in [SearchTree] that the BST [elements] operation is
    correct and complete.  So we ought to be able to implement
    [ETable] with BSTs.  Let's try. *)

Module TreeETable_first_attempt (VT : ValType) <: ETable_first_attempt.

  (** Include all the definitions from [TreeTable], instantiated on
      [VT]. *)
  Include TreeTable VT.

  (** Thanks to the [Include], we now have all the tree operations
      defined "for free" in this module.  For example: *)
  Check get : key -> table -> V.

  Definition bound (k : key) (t : table) : bool :=
    SearchTree.bound k t.

  Definition elements (t : table) : list (key * V) :=
    SearchTree.elements t.

  Theorem elements_complete : forall (k : key) (v : V) (t : table),
      bound k t = true ->
      get k t = v ->
      In (k, v) (elements t).
  Proof.
    intros k v t Hbound Hlookup. unfold get in Hlookup.
    (** [pose proof t as H] is equivalent to [assert (H : ...the type
        of t...). { apply t. }] but saves some keystrokes. *)
    pose proof (SearchTree.elements_complete) as Hcomplete.
    unfold elements_complete_spec in Hcomplete.
    apply Hcomplete with default.
    - (** Stuck! We don't know that [t] satisfies the BST invariant. *)
  Admitted.

  Theorem elements_correct : forall (k : key) (v : V) (t : table),
      In (k, v) (elements t) ->
      bound k t = true /\ get k t = v.
  Proof.
    intros k v t Hin.
    pose proof (SearchTree.elements_correct) as Hcorrect.
    unfold elements_correct_spec in Hcorrect.
    apply Hcorrect.
    - (** Again stuck because of the BST invariant. *)
  Admitted.

End TreeETable_first_attempt.

(* ================================================================= *)
(** ** A Revised [ETable] *)

(** To prove that [elements] is correct, we need to know that
    trees satisfy the BST invariant. So, we declare a function
    [rep_ok] in the interface, and use it as a precondition for values
    of type [table]. We also add axioms to state that the ADT
    operations produce values that satisfy the representation
    invariant, i.e., it is a postcondition. And, we add a
    specification of [bound]. *)

Module Type ETable.

  Include Table.

  Parameter rep_ok : table -> Prop.
  Parameter bound : key -> table -> bool.
  Parameter elements : table -> list (key * V).

  (** [empty] and [set] produce valid representations. *)

  Axiom empty_ok : rep_ok empty.

  Axiom set_ok : forall (k : key) (v : V) (t : table),
      rep_ok t -> rep_ok (set k v t).

  (** The specification of [bound]: *)

  Axiom bound_empty : forall (k : key),
      bound k empty = false.

  Axiom bound_set_same : forall (k : key) (v : V) (t : table),
      bound k (set k v t) = true.

  Axiom bound_set_other : forall (k k' : key) (v : V) (t : table),
      k <> k' -> bound k' (set k v t) = bound k' t.

  (** The specification of [elements]: *)

  Axiom elements_complete : forall (k : key) (v : V) (t : table),
      rep_ok t ->
      bound k t = true ->
      get k t = v ->
      In (k, v) (elements t).

  Axiom elements_correct : forall (k : key) (v : V) (t : table),
      rep_ok t ->
      In (k, v) (elements t) ->
      bound k t = true /\ get k t = v.

End ETable.

Module TreeETable (VT : ValType) <: ETable.

  Include TreeTable VT.

  Definition rep_ok (t : table) : Prop :=
    BST t.

  Definition bound (k : key) (t : table) : bool :=
    SearchTree.bound k t.

  Definition elements (t : table) : list (key * V) :=
    SearchTree.elements t.

  Theorem empty_ok : rep_ok empty.
  Proof.
    apply empty_tree_BST.
  Qed.

  Theorem set_ok : forall (k : key) (v : V) (t : table),
      rep_ok t -> rep_ok (set k v t).
  Proof.
    apply insert_BST.
  Qed.

  Theorem bound_empty : forall (k : key),
      bound k empty = false.
  Proof.
    reflexivity.
  Qed.

  Theorem bound_set_same : forall (k : key) (v : V) (t : table),
      bound k (set k v t) = true.
  Proof.
    intros k v t. unfold bound, set. induction t; bdall.
  Qed.

  Theorem bound_set_other : forall (k k' : key) (v : V) (t : table),
      k <> k' -> bound k' (set k v t) = bound k' t.
  Proof.
    intros k k' v t Hneq. unfold bound, set. induction t; bdall.
  Qed.

  Theorem elements_complete : forall (k : key) (v : V) (t : table),
      rep_ok t ->
      bound k t = true ->
      get k t = v ->
      In (k, v) (elements t).
  Proof.
    intros k v t Hbound Hlookup.
    pose proof SearchTree.elements_complete as Hcomplete.
    unfold elements_complete_spec in Hcomplete.
    apply Hcomplete; assumption.
  Qed.

  Theorem elements_correct : forall (k : key) (v : V) (t : table),
      rep_ok t ->
      In (k, v) (elements t) ->
      bound k t = true /\ get k t = v.
  Proof.
    intros k v t. simpl. intros Hin.
    pose proof SearchTree.elements_correct as Hcorrect.
    unfold elements_correct_spec in Hcorrect.
    apply Hcorrect; assumption.
  Qed.

End TreeETable.

(** Now we can use the table. *)

Module StringTreeETableExample.

  Module StringTreeETable := TreeETable StringVal.
  Import StringTreeETable.
  Open Scope string_scope.

  Example ex1 :
    In (0, "A") (elements (set 0 "A" (set 1 "B" empty))).
  Proof.
    apply elements_complete;
      auto using empty_ok, set_ok, bound_set_same, get_set_same.
  Qed.

End StringTreeETableExample.

(* ################################################################# *)
(** * Encapsulation with the Coq Module System (Advanced) *)

(** Functor [TreeETable], above, reveals internal implementation
    details that your data structures class probably taught you are
    better kept private.  For example, the constructors [E] and [T] of
    trees and the implementation of [get] are publicly exposed: *)

Example exposed_trees_ex :
  (StringTreeETableExample.StringTreeETable.get 0 (T E 0 "A" E) = "A")%string.
Proof.
  unfold StringTreeETableExample.StringTreeETable.get. (* we can see [lookup] *)
  reflexivity.
Qed.

(** Like many languages, Coq makes it possible to _encapsulate_
    these details, meaning that they become hidden outside the module.
    It's a simple matter of changing the [<:] syntax to [:] in the
    functor's type.  The only change in the implementation below is
    that one character. *)

(** The [:] syntax makes the module type _opaque_: only what is
    revealed in the type is available for code outside the module to
    use.  The [<:] syntax, however, makes the module type
    _transparent_: the module must conform to the type, but everything
    about the module is still revealed. *)

Module TreeETableFullyEncapsulated (VT : ValType) : ETable.
  Include TreeTable VT.

  Definition rep_ok (t : table) : Prop :=
    BST t.

  Definition bound (k : key) (t : table) : bool :=
    SearchTree.bound k t.

  Definition elements (t : table) : list (key * V) :=
    SearchTree.elements t.

  Theorem empty_ok : rep_ok empty.
  Proof.
    apply empty_tree_BST.
  Qed.

  Theorem set_ok : forall (k : key) (v : V) (t : table),
      rep_ok t -> rep_ok (set k v t).
  Proof.
    apply insert_BST.
  Qed.

  Theorem bound_empty : forall (k : key),
      bound k empty = false.
  Proof.
    reflexivity.
  Qed.

  Theorem bound_set_same : forall (k : key) (v : V) (t : table),
      bound k (set k v t) = true.
  Proof.
    intros k v t. unfold bound, set. induction t; bdall.
  Qed.

  Theorem bound_set_other : forall (k k' : key) (v : V) (t : table),
      k <> k' -> bound k' (set k v t) = bound k' t.
  Proof.
    intros k k' v t Hneq. unfold bound, set. induction t; bdall.
  Qed.

  Theorem elements_complete : forall (k : key) (v : V) (t : table),
      rep_ok t ->
      bound k t = true ->
      get k t = v ->
      In (k, v) (elements t).
  Proof.
    intros k v t Hbound Hlookup.
    pose proof SearchTree.elements_complete as Hcomplete.
    unfold elements_complete_spec in Hcomplete.
    apply Hcomplete; assumption.
  Qed.

  Theorem elements_correct : forall (k : key) (v : V) (t : table),
      rep_ok t ->
      In (k, v) (elements t) ->
      bound k t = true /\ get k t = v.
  Proof.
    intros k v t. simpl. intros Hin.
    pose proof SearchTree.elements_correct as Hcorrect.
    unfold elements_correct_spec in Hcorrect.
    apply Hcorrect; assumption.
  Qed.

End TreeETableFullyEncapsulated.

(** Unfortunately, the module is now too encapsulated to be useful: *)

Module OverlyEncapsulatedExample.

  Module StringTreeETableFullyEncapsulated := TreeETableFullyEncapsulated StringVal.
  Import StringTreeETableFullyEncapsulated.
  Open Scope string_scope.

  Fail Example ex1 : get 0 empty = "".
  (* fails with an error about [""] not having type [V] *)

End OverlyEncapsulatedExample.

(** The problem is that the module now hides not only the internal
    implementation, but also the value type [V]. The functor was
    instantiated on [StringVal], which defines that type as [string].
    But the output of the functor has type [ETable], which doesn't
    reveal anything about [V] except that it is a [Type]. Note in the
    output of the following command how [V] is printed like an axiom
    would be, indicating that nothing is known (externally) about its
    implementation: *)

Print OverlyEncapsulatedExample.StringTreeETableFullyEncapsulated.V.

(** We need to selectively expose certain implementation details.
    We've just seen that [V] should be exposed.  Along with it, we'll
    also want [default] to be exposed.  We can accomplish that with an
    advanced feature of Coq's module system.  The Coq manual doesn't
    give this feature a name, but OCaml (in which Coq is implemented)
    calls it a _sharing constraint_, so we'll use that term here. A
    sharing constraint enables us to constrain definitions shared by
    modules to be the same. *)

Module Type SimpleTable.
  Parameter key : Type.
  Parameter V : Type.
  Parameter default : V.
  Parameter table : Type.
  (* We omit everything else for sake of a simple example. *)
End SimpleTable.

Module SimpleStringTable1 : SimpleTable.
  Definition key := nat.
  Definition V := string.
  Definition default : string := "".
  Definition table := tree V.
End SimpleStringTable1.

(* [V] is abstract. *)
Print SimpleStringTable1.V.

Module Type SimpleTable2 := SimpleTable with Definition V := string.

Module SimpleStringTable2 : SimpleTable2.
  Definition key := nat.
  Definition V := string.
  Definition default : string := "".
  Definition table := tree V.
End SimpleStringTable2.

(* [V] is exposed, but [default] is abstract. *)
Print SimpleStringTable2.V.
Print SimpleStringTable2.default.

Module Type SimpleTable3 := SimpleTable
  with Definition V := string
  with Definition default := ""%string.

Module SimpleStringTable3 : SimpleTable3.
  Definition key := nat.
  Definition V := string.
  Definition default : string := "".
  Definition table := tree V.
End SimpleStringTable3.

(* Both [V] and [default] are exposed. *)
Print SimpleStringTable3.V.
Print SimpleStringTable3.default.

(** Putting sharing constraints to use, let's expose [V] and [default]
    in our implementation of tree-based tables. *)

Module TreeETableEncapsulated (VT : ValType) : (ETable with Definition V := VT.V with Definition default := VT.default).

  Include TreeTable VT.

  Definition rep_ok (t : table) : Prop :=
    BST t.

  Definition bound (k : key) (t : table) : bool :=
    SearchTree.bound k t.

  Definition elements (t : table) : list (key * V) :=
    SearchTree.elements t.

  Theorem empty_ok : rep_ok empty.
  Proof.
    apply empty_tree_BST.
  Qed.

  Theorem set_ok : forall (k : key) (v : V) (t : table),
      rep_ok t -> rep_ok (set k v t).
  Proof.
    apply insert_BST.
  Qed.

  Theorem bound_empty : forall (k : key),
      bound k empty = false.
  Proof.
    reflexivity.
  Qed.

  Theorem bound_set_same : forall (k : key) (v : V) (t : table),
      bound k (set k v t) = true.
  Proof.
    intros k v t. unfold bound, set. induction t; bdall.
  Qed.

  Theorem bound_set_other : forall (k k' : key) (v : V) (t : table),
      k <> k' -> bound k' (set k v t) = bound k' t.
  Proof.
    intros k k' v t Hneq. unfold bound, set. induction t; bdall.
  Qed.

  Theorem elements_complete : forall (k : key) (v : V) (t : table),
      rep_ok t ->
      bound k t = true ->
      get k t = v ->
      In (k, v) (elements t).
  Proof.
    intros k v t Hbound Hlookup.
    pose proof SearchTree.elements_complete as Hcomplete.
    unfold elements_complete_spec in Hcomplete.
    apply Hcomplete; assumption.
  Qed.

  Theorem elements_correct : forall (k : key) (v : V) (t : table),
      rep_ok t ->
      In (k, v) (elements t) ->
      bound k t = true /\ get k t = v.
  Proof.
    intros k v t. simpl. intros Hin.
    pose proof SearchTree.elements_correct as Hcorrect.
    unfold elements_correct_spec in Hcorrect.
    apply Hcorrect; assumption.
  Qed.

End TreeETableEncapsulated.

Module NicelyEncapsulatedExample.

  Module StringTreeETableEncapsulated := TreeETableEncapsulated StringVal.
  Import StringTreeETableEncapsulated.
  Open Scope string_scope.

  Example ex1 : get 0 empty = "".
  Proof.
    (* We can't directly simplify, because [get] is encapsulated. *)
    Fail reflexivity.
    (* But we can use the specifications exposed in the interface. *)
    apply get_empty_default.
  Qed.

  (* We can't fabricate trees with [T] and [E] anymore, because [tree]
     is encapsulated. *)
  Fail Example ex2 : get 0 (T E 0 "A" E) = "A".
End NicelyEncapsulatedExample.

(** Note what we've happily achieved: we can reason about the behavior
    of an ADT entirely from its specification, rather than depending
    on the implementation code.  This is what specification comments
    in interfaces attempt to achieve in real-world code. *)

(** **** Exercise: 4 stars, advanced, optional (elements_spec)  *)

(** Develop a nicely-encapsulated interface and implementation of
    tree-based tables that exposes the rest of the specification of
    [elements] from [SearchTree], including the inverses of
    correctness and completenesss, sortedness, and
    non-duplication. Send us your solution, so we can include it! *)

(** [] *)

(* ################################################################# *)
(** * Model-based Specification *)

(** The interfaces above have been based on equational specification
    of tables.  Let's consider model-based specifications.  Recall
    from [SearchTree] that in this style of specification, we

    - introduce an abstraction function (or relation) that associates
      a _concrete value_ of the ADT implementation with an _abstract
      value_ in an already well-understood type; and

    - show that the concrete and abstract operations are related in a
      sensible way. *)

(** We begin by defining a new map operation, [bound], and redefining
    existing operations to make them more clear in the table
    specification we are about to write. *)

Definition map_update {V : Type}
           (k : key) (v : V) (m : partial_map V) : partial_map V :=
  update m k v.

Definition map_find {V : Type} := @find V.

Definition empty_map {V : Type} := @Maps.empty V.

(** Now we can define an interface for tables that includes an
    abstraction function [Abs], and specifications written in terms of
    it. *)

Module Type ETableAbs.

  Parameter table : Type.
  Definition key := nat.
  Parameter V : Type.
  Parameter default : V.

  Parameter empty : table.
  Parameter get : key -> table -> V.
  Parameter set : key -> V -> table -> table.
  Parameter bound : key -> table -> bool.
  Parameter elements : table -> list (key * V).

  Parameter Abs : table -> partial_map V.
  Parameter rep_ok : table -> Prop.

  Axiom empty_ok :
      rep_ok empty.

  Axiom set_ok : forall (k : key) (v : V) (t : table),
      rep_ok t -> rep_ok (set k v t).

  Axiom empty_relate :
      Abs empty = empty_map.

  Axiom bound_relate : forall (t : table) (k : key),
      rep_ok t ->
      map_bound k (Abs t) = bound k t.

  Axiom lookup_relate : forall (t : table) (k : key),
      rep_ok t ->
      map_find default k (Abs t) = get k t.

  Axiom insert_relate : forall (t : table) (k : key) (v : V),
      rep_ok t ->
      map_update k v (Abs t) = Abs (set k v t).

  Axiom elements_relate : forall (t : table),
      rep_ok t ->
      Abs t = map_of_list (elements t).

End ETableAbs.

(** **** Exercise: 4 stars, standard (list_etable_abs)  *)

(** Implement [ETableAbs] using association lists as the
    representation type. *)

Module ListETableAbs (VT : ValType) <: ETableAbs.

  Definition V := VT.V.
  Definition default := VT.default.
  Definition key := nat.
  Definition table := list (key * V).

  Definition empty : table
    (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

  Fixpoint get (k : key) (t : table) : V
    (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

  Definition set (k : key) (v : V) (t : table) : table
    (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

  Fixpoint bound (k : key) (t : table) : bool
    (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

  Definition elements (t : table) : list (key * V)
    (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

  Definition Abs (t : table) : partial_map V
    (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

  Definition rep_ok (t : table) : Prop
    (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

  Theorem empty_ok : rep_ok empty.
  Proof.
    (* FILL IN HERE *) Admitted.

  Theorem set_ok : forall (k : key) (v : V) (t : table),
      rep_ok t -> rep_ok (set k v t).
  Proof.
    (* FILL IN HERE *) Admitted.

  Theorem empty_relate :
    Abs empty = empty_map.
  Proof.
    (* FILL IN HERE *) Admitted.

  Theorem bound_relate : forall (t : table) (k : key),
      rep_ok t ->
      map_bound k (Abs t) = bound k t.
  Proof.
    (* FILL IN HERE *) Admitted.

  Theorem lookup_relate : forall (t : table) (k : key),
      rep_ok t ->
      map_find default k (Abs t) = get k t.
  Proof.
    (* FILL IN HERE *) Admitted.

  Theorem insert_relate : forall (t : table) (k : key) (v : V),
      rep_ok t ->
      map_update k v (Abs t) = Abs (set k v t).
  Proof.
    (* FILL IN HERE *) Admitted.

  Theorem elements_relate : forall (t : table),
      rep_ok t ->
      Abs t = map_of_list (elements t).
  Proof.
    (* FILL IN HERE *) Admitted.

End ListETableAbs.

(* Instantiate functor for sake of autograding. *)
Module StringListETableAbs := ListETableAbs StringVal.

(** [] *)

(** **** Exercise: 3 stars, standard, optional (TreeTableModel) 

    Give an implementation of [ETableAbs] using the abstraction
    function [Abs] from [SearchTree]. All the proofs of the
    [relate] axioms should be simple applications of the lemmas
    already proved as exercises in that chapter. *)

(* Do not modify the following line: *)
Definition manual_grade_for_TreeTableModel : option (nat*string) := None.

(** [] *)

(** **** Exercise: 2 stars, advanced, optional (TreeTableModel')  *)

(** Repeat the previous exercise, this time using the alternative
    [Abs'] function from [SearchTree]. Hint: Just tweak your
    solution to the previous exercise. *)

(** [] *)

(* ################################################################# *)
(** * Summary of ADT Verification *)

(** With equational specifications:

    - Define a _representation invariant_ to characterize which
      values of the _representation type_ are legal.  Prove that each
      operation on the representation type _preserves_ the representation
      invariant.

    - Using the representation invariant, verify the equational
      specification.

    With model-based specifications:

    - Define and verify preservation of the the representation invariant.

    - Define an _abstraction function_ that relates the
      representation type to another type that is easier to reason
      about.

    - Prove that operations of the abstract and concrete types commute
      with the abstraction function. *)

(* ################################################################# *)
(** * Another ADT: Queue *)

(** Here is an interface and algebraic specification for FIFO queues. To
    ensure totality, [peek] takes a default value and [deq] returns the
    empty queue when applied to the empty queue. *)

Module Type Queue.
  Parameter V : Type.
  Parameter queue : Type.
  Parameter empty: queue.
  Parameter is_empty : queue -> bool.
  Parameter enq : queue -> V -> queue.
  Parameter deq : queue -> queue.
  Parameter peek : V -> queue -> V.
  Axiom is_empty_empty : is_empty empty = true.
  Axiom is_empty_nonempty : forall q v, is_empty (enq q v) = false.
  Axiom peek_empty : forall d, peek d empty = d.
  Axiom peek_nonempty : forall d q v, peek d (enq q v) = peek v q.
  Axiom deq_empty : deq empty = empty.
  Axiom deq_nonempty : forall q v, deq (enq q v) = if is_empty q then q else enq (deq q) v.
End Queue.

(** **** Exercise: 3 stars, standard (list_queue)  *)

(** Implement that interface and verify your implementation.  As the
    representation type, use [list V].  At least one operation will
    have to be linear time; we recommend that it be [enq]. All the
    proofs should be quite easy. *)

Module ListQueue <: Queue.
  Definition V := nat. (* for simplicity *)
  Definition queue := list V.

  Definition empty : queue
    (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

  Definition is_empty (q : queue) : bool
    (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

  Definition enq (q : queue) (v : V) : queue
    (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

  Definition deq (q : queue) : queue
    (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

  Definition peek (default : V) (q : queue) : V
    (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

  Theorem is_empty_empty : is_empty empty = true.
  Proof.
    (* FILL IN HERE *) Admitted.

  Theorem is_empty_nonempty : forall q v,
      is_empty (enq q v) = false.
  Proof.
    (* FILL IN HERE *) Admitted.

  Theorem peek_empty : forall d,
      peek d empty = d.
  Proof.
    (* FILL IN HERE *) Admitted.

  Theorem peek_nonempty : forall d q v,
      peek d (enq q v) = peek v q.
  Proof.
    (* FILL IN HERE *) Admitted.

  Theorem deq_empty :
    deq empty = empty.
  Proof.
    (* FILL IN HERE *) Admitted.

  Theorem deq_nonempty : forall q v,
      deq (enq q v) = if is_empty q then q else enq (deq q) v.
  Proof.
    (* FILL IN HERE *) Admitted.

End ListQueue.

(** [] *)

(** Here is an interface and model-based specification for queues. We omit
    [rep_ok] from it, because our intended implementation isn't going
    to require a representation invariant. *)

Module Type QueueAbs.
  Parameter V : Type.
  Parameter queue : Type.
  Parameter empty : queue.
  Parameter is_empty : queue -> bool.
  Parameter enq : queue -> V -> queue.
  Parameter deq : queue -> queue.
  Parameter peek : V -> queue -> V.
  Parameter Abs : queue -> list V.
  Axiom empty_relate : Abs empty = [].
  Axiom enq_relate : forall q v,  Abs (enq q v) = (Abs q) ++ [v].
  Axiom peek_relate : forall d q, peek d q = hd d (Abs q).
  Axiom deq_relate : forall q, Abs (deq q) = tl (Abs q).
End QueueAbs.

(** **** Exercise: 3 stars, standard (two_list_queue)  *)

(** Below is an implementation of [QueueAbs] using two lists.  It
    achieves amortized constant-time performance, improving on the
    single-list implementation. Verify this implementation. *)

Module TwoListQueueAbs <: QueueAbs.
  Definition V := nat. (* for simplicity *)

  Definition queue : Type := list V * list V.

  (* [(f, b)] represents a queue with a front list [f] and a back list
     [b], where the back list is stored in reverse order. *)
  Definition Abs '((f, b) : queue) : list V :=
    f ++ (rev b).

  Definition empty : queue :=
    ([], []).

  Definition is_empty (q: queue) :=
    match q with
    | ([], []) => true
    | _ => false
    end.

  Definition enq '((f, b) : queue) (v : V) :=
    (f, v :: b).

  Definition deq (q : queue) :=
    match q with
    | ([], []) => ([], [])
    | ([], b) =>
      match rev b with
      | [] => ([], [])
      | _ :: f => (f, [])
      end
    | (_ :: f, b) => (f, b)
    end.

  Definition peek (d : V) (q : queue) :=
    match q with
    | ([], []) => d
    | ([], b) =>
      match rev b with
      | [] => d
      | v :: _ => v
      end
    | (v :: _, _) => v
    end.

  Theorem empty_relate : Abs empty = [].
  Proof.
    (* FILL IN HERE *) Admitted.

  Theorem enq_relate : forall q v,
      Abs (enq q v) = (Abs q) ++ [v].
  Proof.
    (* FILL IN HERE *) Admitted.

  Theorem peek_relate : forall d q,
      peek d q = hd d (Abs q).
  Proof.
    (* FILL IN HERE *) Admitted.

  Theorem deq_relate : forall q,
      Abs (deq q) = tl (Abs q).
  Proof.
    (* FILL IN HERE *) Admitted.

End TwoListQueueAbs.

(** [] *)

(* ################################################################# *)
(** * Representation Invariants and Subset Types *)

(** In specifications thus far, whenever there was a representation
    invariant that needed to be enforced we had to add it as a
    precondition and postcondition for operations.  For example, the
    correctness of the table [get] operation depended on its [table]
    input satisfying [rep_ok].  We had to write propositions like [forall
    (t : table), rep_ok t -> ...], in which we had a type [table] with
    lots of values, and we got rid of some of those values by
    requiring [rep_ok] to hold of them. *)

(** Coq makes it possible to directly express the requirement that
    values of a type must satisfy a proposition.  The type

      {x : A | P}

    is the type of all values [x] of type [A] that satisfy property
    [P], which itself has type [A -> Prop].  The notation is deliberately
    suggestive of set-builder notation used in mathematics. Such types
    are known as _subset types_. *)

(* ================================================================= *)
(** ** Example: The Even Naturals *)

(** We can define the subset type of even natural numbers using
    the property [Nat.Even] from the standard library: *)

Definition even_nat := {x : nat | Nat.Even x}.

(** But when we try to say that [2] is an [even_nat], Coq rejects the
    definition: *)

Fail Definition two : even_nat := 2.

(** The problem is that [2] is a [nat], but we haven't proved [Nat.Even 2].
    The proof is easy: *)

Lemma Even2 : Nat.Even 2.
Proof. exists 1. reflexivity. Qed.

(** Now we can provide that proof to convince Coq [two] is an [even_nat].
    We can do that with function [exist], which is suggestive of
    "there exists an [x : A] such that [P x]." *)

Check exist : forall {A : Type} (P : A -> Prop) (x : A), P x -> {x : A | P x}.

Definition two : even_nat := exist Nat.Even 2 Even2.

(** Another way of constructing [two] is to enter Coq's proof scripting
    mode and use tactics.  We saw this briefly in [ProofObjects]. *)

Definition two' : even_nat.
Proof.
  apply exist with (x := 2).
  exists 1. reflexivity.
Defined.

(** That technique is often useful with subset types, because it
    helps us more easily build the proof objects, rather than have to
    write them ourselves. *)

(** A value of type [even_nat] is like a "package" containing the [nat]
    and the proof that the [nat] is even.  We have to use functions to
    extract those components from the package. *)

Fail Example plus_two : 1 + two = 3.

Check proj1_sig : forall {A : Type} {P : A -> Prop} (e : {x : A | P x}), A.

Example plus_two : 1 + proj1_sig two = 3.
Proof. reflexivity. Qed.

Check proj2_sig : forall {A : Type} {P : A -> Prop} (e : {x : A | P x}), P (proj1_sig e).

Example Even2' : Nat.Even 2 := proj2_sig two.

(* ================================================================= *)
(** ** Defining Subset Types *)

(** Like nearly everything else we've seen in Coq's logic, subset
    types are actually defined in the standard library rather than
    being built-in to the language. *)

Module SigSandbox.

  (** Subset types are just a syntactic notation for [sig]: *)

  Inductive sig {A : Type} (P : A -> Prop) : Type :=
  | exist (x : A) : P x -> sig P.

  Notation "{ x : A | P }" := (sig A (fun x => P)).

  (** The name [sig] is short for the Greek capital letter sigma,
      because subset types are similar to something known in type
      theory as _sigma types_, aka _dependent sums_. *)

  
  (** Subset types and existential quantification are quite similar.
      Recall how the latter is defined: *)

  Inductive ex {A : Type} (P : A -> Prop) : Prop :=
  | ex_intro (x : A) : P x -> ex P.

  (** The only difference is that [sig] creates a [Type] whereas [ex]
      creates a [Prop].  That is, the former is computational in content,
      whereas the latter is logical.  Therefore we can pattern match
      to recover the witness from a [sig], but we cannot do the same
      with an [ex]. *)

  Definition proj1_sig {A : Type} {P : A -> Prop} (e : sig P) : A :=
    match e with
    | exist _ x _ => x
    end.

  Definition proj2_sig {A : Type} {P : A -> Prop} (e : sig P) : P (proj1_sig e) :=
    match e with
    | exist _ _ p => p
    end.

  Fail Definition proj1_ex {A : Type} {P : A -> Prop} (e : ex P) : A :=
    match e with
    | ex_intro _ x _ => x
    end.

End SigSandbox.

(* ================================================================= *)
(** ** Example: Vectors *)

(** A _vector_ is a list of a known length. Type [vector X] contains
    values [(xs, n)] with a particular representation invariant: [n]
    must be the length of [xs].  *)

Definition vector (X : Type) :=
  { '(xs, n) : list X * nat | length xs = n }.

(** The type itself enforces the representation invariant, because a
    value of type [vector X] cannot be constructed without first
    proving that the invariant holds. *)

(** **** Exercise: 1 star, standard (a_vector)  *)

(** Construct any vector of your choice. *)

Example a_vector : vector nat.
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 2 stars, standard (vector_cons_correct)  *)

(** Define a cons operation on vectors. Remember to end with
    [Defined] rather than [Qed]. *)

Definition vector_cons {X : Type} (x : X) (v : vector X) : vector X.
Proof.
  (* FILL IN HERE *) Admitted.

(** Prove the correctness of your cons operation. *)

Definition list_of_vector {X : Type} (v : vector X) : list X :=
  fst (proj1_sig v).

Theorem vector_cons_correct : forall (X : Type) (x : X) (v : vector X),
    list_of_vector (vector_cons x v) = x :: (list_of_vector v).
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 2 stars, standard (vector_app_correct)  *)

(** Define an append operation on vectors. *)

Definition vector_app {X : Type} (v1 v2 : vector X) : vector X.
Proof.
  (* FILL IN HERE *) Admitted.

(** Prove the correctness of your append operation. *)

Theorem vector_app_correct : forall (X : Type) (v1 v2 : vector X),
    list_of_vector (vector_app v1 v2) =
    list_of_vector v1 ++ list_of_vector v2.
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)

(* ================================================================= *)
(** ** Using Subset Types to Enforce the BST Invariant *)

(** Let's use subset types to reimplement tree-based tables with an
    [elements] operation.  Previously we had to add [rep_ok] to the
    interface and specifications.  With subset types we can eliminate
    that. *)

Module Type ETableSubset.

  Include Table.

  (** Note: no [rep_ok] anywhere. *)

  Parameter bound : key -> table -> bool.
  Parameter elements : table -> list (key * V).

  Axiom bound_empty : forall (k : key),
      bound k empty = false.

  Axiom bound_set_same : forall (k : key) (v : V) (t : table),
      bound k (set k v t) = true.

  Axiom bound_set_other : forall (k k' : key) (v : V) (t : table),
      k <> k' -> bound k' (set k v t) = bound k' t.

  Axiom elements_complete : forall (k : key) (v : V) (t : table),
      bound k t = true ->
      get k t = v ->
      In (k, v) (elements t).

  Axiom elements_correct : forall (k : key) (v : V) (t : table),
      In (k, v) (elements t) ->
      bound k t = true /\ get k t = v.

End ETableSubset.

Module TreeETableSubset (VT : ValType) <: ETableSubset.

  Definition V := VT.V.
  Definition default := VT.default.
  Definition key := nat.

  (** [table] now is required to enforce [BST]. *)
  Definition table := { t : tree V | BST t }.

  (** Now instead of proving separate theorems that operations return
      valid representations, the proofs are "baked in" to the
      operations. *)
  Definition empty : table.
  Proof.
    apply (exist _ empty_tree).
    apply empty_tree_BST.
  Defined.

  (** Now we insert a projection to get to the tree. *)
  Definition get (k : key) (t : table) : V :=
    lookup default k (proj1_sig t).

  Definition set (k : key) (v : V) (t : table) : table.
  Proof.
    destruct t as [t Ht].
    apply (exist _ (insert k v t)).
    apply insert_BST. assumption.
  Defined.

  Definition bound (k : key) (t : table) : bool :=
    SearchTree.bound k (proj1_sig t).

  Definition elements (t : table) : list (key * V) :=
    elements (proj1_sig t).

  Theorem get_empty_default: forall (k : key),
      get k empty = default.
  Proof.
    apply lookup_empty.
  Qed.

  (** Now the rest of the proofs require minor modifications to
      destruct the table to get the tree and the representation
      invariant, and use the latter where needed. *)

  Theorem get_set_same: forall (k : key) (v : V) (t : table),
      get k (set k v t) = v.
  Proof.
    intros. unfold get, set.
    destruct t as [t Hbst]. simpl.
    apply lookup_insert_eq.
  Qed.

  Theorem get_set_other: forall (k k' : key) (v : V) (t : table),
      k <> k' -> get k' (set k v t) = get k' t.
  Proof.
    intros. unfold get, set.
    destruct t as [t Hbst]. simpl.
    apply lookup_insert_neq. assumption.
  Qed.

  Theorem bound_empty : forall (k : key),
      bound k empty = false.
  Proof.
    reflexivity.
  Qed.

  Theorem bound_set_same : forall (k : key) (v : V) (t : table),
      bound k (set k v t) = true.
  Proof.
    intros k v t. unfold bound, set.
    destruct t as [t Hbst]. simpl in *.
    induction t; inv Hbst; bdall.
  Qed.

  Theorem bound_set_other : forall (k k' : key) (v : V) (t : table),
      k <> k' -> bound k' (set k v t) = bound k' t.
  Proof.
    intros k k' v t Hneq. unfold bound, set.
    destruct t as [t Hbst]. simpl in *.
    induction t; inv Hbst; bdall.
  Qed.

  Theorem elements_complete : forall (k : key) (v : V) (t : table),
      bound k t = true ->
      get k t = v ->
      In (k, v) (elements t).
  Proof.
    intros k v t Hbound Hlookup.
    pose proof SearchTree.elements_complete as Hcomplete.
    unfold elements_complete_spec in Hcomplete.
    apply Hcomplete with default; try assumption.
    destruct t as [t Hbst]. assumption.
  Qed.

  Theorem elements_correct : forall (k : key) (v : V) (t : table),
      In (k, v) (elements t) ->
      bound k t = true /\ get k t = v.
  Proof.
    intros k v t. simpl. intros Hin.
    pose proof SearchTree.elements_correct as Hcorrect.
    unfold elements_correct_spec in Hcorrect.
    apply Hcorrect; try assumption.
    destruct t as [t Hbst]. assumption.
  Qed.

End TreeETableSubset.

(** **** Exercise: 4 stars, advanced (ListsETable)  *)

(** Implement [ETableSubset] using association lists that are not
    permitted to contain duplicate keys.  Enforce that representation
    invariant with a subset type.  Note that you do not have to keep
    the lists in a sorted order. The implementation of [elements]
    should therefore just be quite easy: just return the association
    list.  The implementation of [set], though, will have to be a
    linear-time operation. *)

(* Do not modify the following line: *)
Definition manual_grade_for_ListsETable : option (nat*string) := None.
(** [] *)

(* 2020-08-07 17:08 *)
