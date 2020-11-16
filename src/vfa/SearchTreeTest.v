Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From VFA Require Import SearchTree.

Parameter MISSING: Type.

Module Check.

Ltac check_type A B :=
    match type of A with
    | context[MISSING] => idtac "Missing:" A
    | ?T => first [unify T B; idtac "Type: ok" | idtac "Type: wrong - should be (" B ")"]
    end.

Ltac print_manual_grade A :=
    match eval compute in A with
    | Some (_ ?S ?C) =>
        idtac "Score:"  S;
        match eval compute in C with
          | ""%string => idtac "Comment: None"
          | _ => idtac "Comment:" C
        end
    | None =>
        idtac "Score: Ungraded";
        idtac "Comment: None"
    end.

End Check.

From VFA Require Import SearchTree.
Import Check.

Goal True.

idtac "-------------------  empty_tree_BST  --------------------".
idtac " ".

idtac "#> empty_tree_BST".
idtac "Possible points: 1".
check_type @empty_tree_BST ((forall V : Type, @BST V (@empty_tree V))).
idtac "Assumptions:".
Abort.
Print Assumptions empty_tree_BST.
Goal True.
idtac " ".

idtac "-------------------  insert_BST  --------------------".
idtac " ".

idtac "#> ForallT_insert".
idtac "Possible points: 3".
check_type @ForallT_insert (
(forall (V : Type) (P : key -> V -> Prop) (t : tree V),
 @ForallT V P t ->
 forall (k : key) (v : V), P k v -> @ForallT V P (@insert V k v t))).
idtac "Assumptions:".
Abort.
Print Assumptions ForallT_insert.
Goal True.
idtac " ".

idtac "#> insert_BST".
idtac "Possible points: 3".
check_type @insert_BST (
(forall (V : Type) (k : key) (v : V) (t : tree V),
 @BST V t -> @BST V (@insert V k v t))).
idtac "Assumptions:".
Abort.
Print Assumptions insert_BST.
Goal True.
idtac " ".

idtac "-------------------  elements_complete  --------------------".
idtac " ".

idtac "#> elements_complete".
idtac "Possible points: 3".
check_type @elements_complete (elements_complete_spec).
idtac "Assumptions:".
Abort.
Print Assumptions elements_complete.
Goal True.
idtac " ".

idtac "-------------------  elements_preserves_forall  --------------------".
idtac " ".

idtac "#> elements_preserves_forall".
idtac "Possible points: 2".
check_type @elements_preserves_forall (
(forall (V : Type) (P : key -> V -> Prop) (t : tree V),
 @ForallT V P t ->
 @List.Forall (key * V) (@uncurry key V Prop P) (@elements V t))).
idtac "Assumptions:".
Abort.
Print Assumptions elements_preserves_forall.
Goal True.
idtac " ".

idtac "-------------------  elements_preserves_relation  --------------------".
idtac " ".

idtac "#> elements_preserves_relation".
idtac "Possible points: 2".
check_type @elements_preserves_relation (
(forall (V : Type) (k k' : key) (v : V) (t : tree V) (R : key -> key -> Prop),
 @ForallT V (fun (y : key) (_ : V) => R y k') t ->
 @List.In (key * V) (k, v) (@elements V t) -> R k k')).
idtac "Assumptions:".
Abort.
Print Assumptions elements_preserves_relation.
Goal True.
idtac " ".

idtac "-------------------  elements_correct  --------------------".
idtac " ".

idtac "#> elements_correct".
idtac "Possible points: 6".
check_type @elements_correct (elements_correct_spec).
idtac "Assumptions:".
Abort.
Print Assumptions elements_correct.
Goal True.
idtac " ".

idtac "-------------------  elements_complete_inverse  --------------------".
idtac " ".

idtac "#> elements_complete_inverse".
idtac "Advanced".
idtac "Possible points: 2".
check_type @elements_complete_inverse (
(forall (V : Type) (k : key) (v : V) (t : tree V),
 @BST V t ->
 @bound V k t = false -> ~ @List.In (key * V) (k, v) (@elements V t))).
idtac "Assumptions:".
Abort.
Print Assumptions elements_complete_inverse.
Goal True.
idtac " ".

idtac "-------------------  elements_correct_inverse  --------------------".
idtac " ".

idtac "#> bound_value".
idtac "Advanced".
idtac "Possible points: 3".
check_type @bound_value (
(forall (V : Type) (k : key) (t : tree V),
 @bound V k t = true -> exists v : V, forall d : V, @lookup V d k t = v)).
idtac "Assumptions:".
Abort.
Print Assumptions bound_value.
Goal True.
idtac " ".

idtac "#> elements_complete_inverse".
idtac "Advanced".
idtac "Possible points: 3".
check_type @elements_complete_inverse (
(forall (V : Type) (k : key) (v : V) (t : tree V),
 @BST V t ->
 @bound V k t = false -> ~ @List.In (key * V) (k, v) (@elements V t))).
idtac "Assumptions:".
Abort.
Print Assumptions elements_complete_inverse.
Goal True.
idtac " ".

idtac "-------------------  sorted_app  --------------------".
idtac " ".

idtac "#> sorted_app".
idtac "Advanced".
idtac "Possible points: 3".
check_type @sorted_app (
(forall (l1 l2 : list nat) (x : nat),
 Sort.sorted l1 ->
 Sort.sorted l2 ->
 @List.Forall nat (fun n : nat => n < x) l1 ->
 @List.Forall nat (fun n : nat => n > x) l2 -> Sort.sorted (l1 ++ x :: l2))).
idtac "Assumptions:".
Abort.
Print Assumptions sorted_app.
Goal True.
idtac " ".

idtac "-------------------  sorted_elements  --------------------".
idtac " ".

idtac "#> sorted_elements".
idtac "Advanced".
idtac "Possible points: 6".
check_type @sorted_elements (
(forall (V : Type) (t : tree V),
 @BST V t -> Sort.sorted (@list_keys V (@elements V t)))).
idtac "Assumptions:".
Abort.
Print Assumptions sorted_elements.
Goal True.
idtac " ".

idtac "-------------------  fast_elements_eq_elements  --------------------".
idtac " ".

idtac "#> fast_elements_tr_helper".
idtac "Possible points: 2".
check_type @fast_elements_tr_helper (
(forall (V : Type) (t : tree V) (lst : list (key * V)),
 @fast_elements_tr V t lst = (@elements V t ++ lst)%list)).
idtac "Assumptions:".
Abort.
Print Assumptions fast_elements_tr_helper.
Goal True.
idtac " ".

idtac "#> fast_elements_eq_elements".
idtac "Possible points: 1".
check_type @fast_elements_eq_elements (
(forall (V : Type) (t : tree V), @fast_elements V t = @elements V t)).
idtac "Assumptions:".
Abort.
Print Assumptions fast_elements_eq_elements.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 23".
idtac "Max points - advanced: 40".
idtac "".
idtac "Allowed Axioms:".
idtac "functional_extensionality".
idtac "functional_extensionality_dep".
idtac "FunctionalExtensionality.functional_extensionality_dep".
idtac "int".
idtac "Abs".
idtac "Abs_inj".
idtac "ltb".
idtac "ltb_lt".
idtac "leb".
idtac "leb_le".
idtac "Extract.int".
idtac "Extract.Abs".
idtac "Extract.Abs_inj".
idtac "Extract.ltb".
idtac "Extract.ltb_lt".
idtac "Extract.leb".
idtac "Extract.leb_le".
idtac "".
idtac "".
idtac "********** Summary **********".
idtac "".
idtac "Below is a summary of the automatically graded exercises that are incomplete.".
idtac "".
idtac "The output for each exercise can be any of the following:".
idtac "  - 'Closed under the global context', if it is complete".
idtac "  - 'MANUAL', if it is manually graded".
idtac "  - A list of pending axioms, containing unproven assumptions. In this case".
idtac "    the exercise is considered complete, if the axioms are all allowed.".
idtac "".
idtac "********** Standard **********".
idtac "---------- empty_tree_BST ---------".
Print Assumptions empty_tree_BST.
idtac "---------- ForallT_insert ---------".
Print Assumptions ForallT_insert.
idtac "---------- insert_BST ---------".
Print Assumptions insert_BST.
idtac "---------- elements_complete ---------".
Print Assumptions elements_complete.
idtac "---------- elements_preserves_forall ---------".
Print Assumptions elements_preserves_forall.
idtac "---------- elements_preserves_relation ---------".
Print Assumptions elements_preserves_relation.
idtac "---------- elements_correct ---------".
Print Assumptions elements_correct.
idtac "---------- fast_elements_tr_helper ---------".
Print Assumptions fast_elements_tr_helper.
idtac "---------- fast_elements_eq_elements ---------".
Print Assumptions fast_elements_eq_elements.
idtac "".
idtac "********** Advanced **********".
idtac "---------- elements_complete_inverse ---------".
Print Assumptions elements_complete_inverse.
idtac "---------- bound_value ---------".
Print Assumptions bound_value.
idtac "---------- elements_complete_inverse ---------".
Print Assumptions elements_complete_inverse.
idtac "---------- sorted_app ---------".
Print Assumptions sorted_app.
idtac "---------- sorted_elements ---------".
Print Assumptions sorted_elements.
Abort.

(* 2020-08-07 17:08 *)
