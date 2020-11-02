Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From VFA Require Import Selection.

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

From VFA Require Import Selection.
Import Check.

Goal True.

idtac "-------------------  select_perm  --------------------".
idtac " ".

idtac "#> select_perm".
idtac "Possible points: 3".
check_type @select_perm (
(forall (x : nat) (l : list nat) (y : nat) (r : list nat),
 (y, r) = select x l -> @Permutation.Permutation nat (x :: l) (y :: r))).
idtac "Assumptions:".
Abort.
Print Assumptions select_perm.
Goal True.
idtac " ".

idtac "-------------------  selsort_perm  --------------------".
idtac " ".

idtac "#> selsort_perm".
idtac "Possible points: 3".
check_type @selsort_perm (
(forall (n : nat) (l : list nat),
 @length nat l = n -> @Permutation.Permutation nat l (selsort l n))).
idtac "Assumptions:".
Abort.
Print Assumptions selsort_perm.
Goal True.
idtac " ".

idtac "-------------------  selection_sort_perm  --------------------".
idtac " ".

idtac "#> selection_sort_perm".
idtac "Possible points: 1".
check_type @selection_sort_perm (
(forall l : list nat, @Permutation.Permutation nat l (selection_sort l))).
idtac "Assumptions:".
Abort.
Print Assumptions selection_sort_perm.
Goal True.
idtac " ".

idtac "-------------------  select_rest_length  --------------------".
idtac " ".

idtac "#> select_rest_length".
idtac "Possible points: 2".
check_type @select_rest_length (
(forall (x : nat) (l : list nat) (y : nat) (r : list nat),
 select x l = (y, r) -> @length nat l = @length nat r)).
idtac "Assumptions:".
Abort.
Print Assumptions select_rest_length.
Goal True.
idtac " ".

idtac "-------------------  select_fst_leq  --------------------".
idtac " ".

idtac "#> select_fst_leq".
idtac "Possible points: 3".
check_type @select_fst_leq (
(forall (al bl : list nat) (x y : nat), select x al = (y, bl) -> y <= x)).
idtac "Assumptions:".
Abort.
Print Assumptions select_fst_leq.
Goal True.
idtac " ".

idtac "-------------------  select_smallest  --------------------".
idtac " ".

idtac "#> select_smallest".
idtac "Possible points: 3".
check_type @select_smallest (
(forall (al bl : list nat) (x y : nat), select x al = (y, bl) -> y <=* bl)).
idtac "Assumptions:".
Abort.
Print Assumptions select_smallest.
Goal True.
idtac " ".

idtac "-------------------  select_in  --------------------".
idtac " ".

idtac "#> select_in".
idtac "Possible points: 3".
check_type @select_in (
(forall (al bl : list nat) (x y : nat),
 select x al = (y, bl) -> @In nat y (x :: al))).
idtac "Assumptions:".
Abort.
Print Assumptions select_in.
Goal True.
idtac " ".

idtac "-------------------  cons_of_small_maintains_sort  --------------------".
idtac " ".

idtac "#> cons_of_small_maintains_sort".
idtac "Possible points: 3".
check_type @cons_of_small_maintains_sort (
(forall (bl : list nat) (y n : nat),
 n = @length nat bl ->
 y <=* bl -> sorted (selsort bl n) -> sorted (y :: selsort bl n))).
idtac "Assumptions:".
Abort.
Print Assumptions cons_of_small_maintains_sort.
Goal True.
idtac " ".

idtac "-------------------  selsort_sorted  --------------------".
idtac " ".

idtac "#> selsort_sorted".
idtac "Possible points: 3".
check_type @selsort_sorted (
(forall (n : nat) (al : list nat),
 @length nat al = n -> sorted (selsort al n))).
idtac "Assumptions:".
Abort.
Print Assumptions selsort_sorted.
Goal True.
idtac " ".

idtac "-------------------  selection_sort_sorted  --------------------".
idtac " ".

idtac "#> selection_sort_sorted".
idtac "Possible points: 1".
check_type @selection_sort_sorted ((forall al : list nat, sorted (selection_sort al))).
idtac "Assumptions:".
Abort.
Print Assumptions selection_sort_sorted.
Goal True.
idtac " ".

idtac "-------------------  selection_sort_is_correct  --------------------".
idtac " ".

idtac "#> selection_sort_is_correct".
idtac "Possible points: 1".
check_type @selection_sort_is_correct ((is_a_sorting_algorithm selection_sort)).
idtac "Assumptions:".
Abort.
Print Assumptions selection_sort_is_correct.
Goal True.
idtac " ".

idtac "-------------------  selsort'_perm  --------------------".
idtac " ".

idtac "#> selsort'_perm".
idtac "Possible points: 2".
check_type @selsort'_perm (
(forall (n : nat) (l : list nat),
 @length nat l = n -> @Permutation.Permutation nat l (selsort' l))).
idtac "Assumptions:".
Abort.
Print Assumptions selsort'_perm.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 28".
idtac "Max points - advanced: 28".
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
idtac "---------- select_perm ---------".
Print Assumptions select_perm.
idtac "---------- selsort_perm ---------".
Print Assumptions selsort_perm.
idtac "---------- selection_sort_perm ---------".
Print Assumptions selection_sort_perm.
idtac "---------- select_rest_length ---------".
Print Assumptions select_rest_length.
idtac "---------- select_fst_leq ---------".
Print Assumptions select_fst_leq.
idtac "---------- select_smallest ---------".
Print Assumptions select_smallest.
idtac "---------- select_in ---------".
Print Assumptions select_in.
idtac "---------- cons_of_small_maintains_sort ---------".
Print Assumptions cons_of_small_maintains_sort.
idtac "---------- selsort_sorted ---------".
Print Assumptions selsort_sorted.
idtac "---------- selection_sort_sorted ---------".
Print Assumptions selection_sort_sorted.
idtac "---------- selection_sort_is_correct ---------".
Print Assumptions selection_sort_is_correct.
idtac "---------- selsort'_perm ---------".
Print Assumptions selsort'_perm.
idtac "".
idtac "********** Advanced **********".
Abort.

(* 2020-08-07 17:08 *)
