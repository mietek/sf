Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From VFA Require Import Merge.

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

From VFA Require Import Merge.
Import Check.

Goal True.

idtac "-------------------  split_perm  --------------------".
idtac " ".

idtac "#> split_perm".
idtac "Possible points: 3".
check_type @split_perm (
(forall (X : Type) (l l1 l2 : list X),
 @split X l = (l1, l2) -> @Permutation.Permutation X l (l1 ++ l2))).
idtac "Assumptions:".
Abort.
Print Assumptions split_perm.
Goal True.
idtac " ".

idtac "-------------------  sorted_merge1  --------------------".
idtac " ".

idtac "#> sorted_merge1".
idtac "Possible points: 2".
check_type @sorted_merge1 (
(forall (x x1 : nat) (l1 : list nat) (x2 : nat) (l2 : list nat),
 x <= x1 ->
 x <= x2 ->
 Sort.sorted (merge (x1 :: l1) (x2 :: l2)) ->
 Sort.sorted (x :: merge (x1 :: l1) (x2 :: l2)))).
idtac "Assumptions:".
Abort.
Print Assumptions sorted_merge1.
Goal True.
idtac " ".

idtac "-------------------  sorted_merge  --------------------".
idtac " ".

idtac "#> sorted_merge".
idtac "Possible points: 6".
check_type @sorted_merge (
(forall l1 : list nat,
 Sort.sorted l1 ->
 forall l2 : list nat, Sort.sorted l2 -> Sort.sorted (merge l1 l2))).
idtac "Assumptions:".
Abort.
Print Assumptions sorted_merge.
Goal True.
idtac " ".

idtac "-------------------  mergesort_sorts  --------------------".
idtac " ".

idtac "#> mergesort_sorts".
idtac "Possible points: 2".
check_type @mergesort_sorts ((forall l : list nat, Sort.sorted (mergesort l))).
idtac "Assumptions:".
Abort.
Print Assumptions mergesort_sorts.
Goal True.
idtac " ".

idtac "-------------------  merge_perm  --------------------".
idtac " ".

idtac "#> merge_perm".
idtac "Advanced".
idtac "Possible points: 3".
check_type @merge_perm (
(forall l1 l2 : list nat,
 @Permutation.Permutation nat (l1 ++ l2) (merge l1 l2))).
idtac "Assumptions:".
Abort.
Print Assumptions merge_perm.
Goal True.
idtac " ".

idtac "-------------------  mergesort_perm  --------------------".
idtac " ".

idtac "#> mergesort_perm".
idtac "Advanced".
idtac "Possible points: 3".
check_type @mergesort_perm (
(forall l : list nat, @Permutation.Permutation nat l (mergesort l))).
idtac "Assumptions:".
Abort.
Print Assumptions mergesort_perm.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 13".
idtac "Max points - advanced: 19".
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
idtac "---------- split_perm ---------".
Print Assumptions split_perm.
idtac "---------- sorted_merge1 ---------".
Print Assumptions sorted_merge1.
idtac "---------- sorted_merge ---------".
Print Assumptions sorted_merge.
idtac "---------- mergesort_sorts ---------".
Print Assumptions mergesort_sorts.
idtac "".
idtac "********** Advanced **********".
idtac "---------- merge_perm ---------".
Print Assumptions merge_perm.
idtac "---------- mergesort_perm ---------".
Print Assumptions mergesort_perm.
Abort.

(* 2020-08-07 17:08 *)
