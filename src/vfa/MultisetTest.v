Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From VFA Require Import Multiset.

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

From VFA Require Import Multiset.
Import Check.

Goal True.

idtac "-------------------  union_assoc  --------------------".
idtac " ".

idtac "#> union_assoc".
idtac "Possible points: 1".
check_type @union_assoc (
(forall a b c : multiset, union a (union b c) = union (union a b) c)).
idtac "Assumptions:".
Abort.
Print Assumptions union_assoc.
Goal True.
idtac " ".

idtac "-------------------  union_comm  --------------------".
idtac " ".

idtac "#> union_comm".
idtac "Possible points: 1".
check_type @union_comm ((forall a b : multiset, union a b = union b a)).
idtac "Assumptions:".
Abort.
Print Assumptions union_comm.
Goal True.
idtac " ".

idtac "-------------------  union_swap  --------------------".
idtac " ".

idtac "#> union_swap".
idtac "Possible points: 2".
check_type @union_swap (
(forall a b c : multiset, union a (union b c) = union b (union a c))).
idtac "Assumptions:".
Abort.
Print Assumptions union_swap.
Goal True.
idtac " ".

idtac "-------------------  insert_contents  --------------------".
idtac " ".

idtac "#> insert_contents".
idtac "Possible points: 3".
check_type @insert_contents (
(forall (x : nat) (l : list nat),
 contents (Sort.insert x l) = contents (x :: l))).
idtac "Assumptions:".
Abort.
Print Assumptions insert_contents.
Goal True.
idtac " ".

idtac "-------------------  sort_contents  --------------------".
idtac " ".

idtac "#> sort_contents".
idtac "Possible points: 2".
check_type @sort_contents ((forall l : list value, contents l = contents (Sort.sort l))).
idtac "Assumptions:".
Abort.
Print Assumptions sort_contents.
Goal True.
idtac " ".

idtac "-------------------  insertion_sort_correct  --------------------".
idtac " ".

idtac "#> insertion_sort_correct".
idtac "Possible points: 1".
check_type @insertion_sort_correct ((is_a_sorting_algorithm' Sort.sort)).
idtac "Assumptions:".
Abort.
Print Assumptions insertion_sort_correct.
Goal True.
idtac " ".

idtac "-------------------  permutations_vs_multiset  --------------------".
idtac " ".

idtac "#> Manually graded: permutations_vs_multiset".
idtac "Possible points: 1".
print_manual_grade manual_grade_for_permutations_vs_multiset.
idtac " ".

idtac "-------------------  perm_contents  --------------------".
idtac " ".

idtac "#> perm_contents".
idtac "Possible points: 3".
check_type @perm_contents (
(forall al bl : list nat,
 @Permutation.Permutation nat al bl -> contents al = contents bl)).
idtac "Assumptions:".
Abort.
Print Assumptions perm_contents.
Goal True.
idtac " ".

idtac "-------------------  contents_nil_inv  --------------------".
idtac " ".

idtac "#> contents_nil_inv".
idtac "Advanced".
idtac "Possible points: 2".
check_type @contents_nil_inv (
(forall l : list value,
 (forall x : value, 0 = contents l x) -> l = @nil value)).
idtac "Assumptions:".
Abort.
Print Assumptions contents_nil_inv.
Goal True.
idtac " ".

idtac "-------------------  contents_cons_inv  --------------------".
idtac " ".

idtac "#> contents_cons_inv".
idtac "Advanced".
idtac "Possible points: 3".
check_type @contents_cons_inv (
(forall (l : list value) (x : value) (n : nat),
 S n = contents l x ->
 exists l1 l2 : list value,
   l = (l1 ++ x :: l2)%list /\ contents (l1 ++ l2) x = n)).
idtac "Assumptions:".
Abort.
Print Assumptions contents_cons_inv.
Goal True.
idtac " ".

idtac "-------------------  contents_insert_other  --------------------".
idtac " ".

idtac "#> contents_insert_other".
idtac "Advanced".
idtac "Possible points: 2".
check_type @contents_insert_other (
(forall (l1 l2 : list value) (x y : value),
 y <> x -> contents (l1 ++ x :: l2) y = contents (l1 ++ l2) y)).
idtac "Assumptions:".
Abort.
Print Assumptions contents_insert_other.
Goal True.
idtac " ".

idtac "-------------------  contents_perm  --------------------".
idtac " ".

idtac "#> contents_perm".
idtac "Advanced".
idtac "Possible points: 3".
check_type @contents_perm (
(forall al bl : list value,
 contents al = contents bl -> @Permutation.Permutation value al bl)).
idtac "Assumptions:".
Abort.
Print Assumptions contents_perm.
Goal True.
idtac " ".

idtac "-------------------  same_contents_iff_perm  --------------------".
idtac " ".

idtac "#> same_contents_iff_perm".
idtac "Possible points: 1".
check_type @same_contents_iff_perm (
(forall al bl : list value,
 contents al = contents bl <-> @Permutation.Permutation value al bl)).
idtac "Assumptions:".
Abort.
Print Assumptions same_contents_iff_perm.
Goal True.
idtac " ".

idtac "-------------------  sort_specifications_equivalent  --------------------".
idtac " ".

idtac "#> sort_specifications_equivalent".
idtac "Possible points: 2".
check_type @sort_specifications_equivalent (
(forall sort : list nat -> list nat,
 Sort.is_a_sorting_algorithm sort <-> is_a_sorting_algorithm' sort)).
idtac "Assumptions:".
Abort.
Print Assumptions sort_specifications_equivalent.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 17".
idtac "Max points - advanced: 27".
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
idtac "---------- union_assoc ---------".
Print Assumptions union_assoc.
idtac "---------- union_comm ---------".
Print Assumptions union_comm.
idtac "---------- union_swap ---------".
Print Assumptions union_swap.
idtac "---------- insert_contents ---------".
Print Assumptions insert_contents.
idtac "---------- sort_contents ---------".
Print Assumptions sort_contents.
idtac "---------- insertion_sort_correct ---------".
Print Assumptions insertion_sort_correct.
idtac "---------- permutations_vs_multiset ---------".
idtac "MANUAL".
idtac "---------- perm_contents ---------".
Print Assumptions perm_contents.
idtac "---------- same_contents_iff_perm ---------".
Print Assumptions same_contents_iff_perm.
idtac "---------- sort_specifications_equivalent ---------".
Print Assumptions sort_specifications_equivalent.
idtac "".
idtac "********** Advanced **********".
idtac "---------- contents_nil_inv ---------".
Print Assumptions contents_nil_inv.
idtac "---------- contents_cons_inv ---------".
Print Assumptions contents_cons_inv.
idtac "---------- contents_insert_other ---------".
Print Assumptions contents_insert_other.
idtac "---------- contents_perm ---------".
Print Assumptions contents_perm.
Abort.

(* 2020-08-07 17:08 *)
