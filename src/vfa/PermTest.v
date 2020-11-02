Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From VFA Require Import Perm.

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

From VFA Require Import Perm.
Import Check.

Goal True.

idtac "-------------------  Permutation_properties  --------------------".
idtac " ".

idtac "#> Manually graded: Permutation_properties".
idtac "Possible points: 2".
print_manual_grade manual_grade_for_Permutation_properties.
idtac " ".

idtac "-------------------  permut_example  --------------------".
idtac " ".

idtac "#> permut_example".
idtac "Possible points: 3".
check_type @permut_example (
(forall a b : list nat,
 @Permutation nat (5 :: 6 :: a ++ b) ((5 :: b) ++ 6 :: a ++ []))).
idtac "Assumptions:".
Abort.
Print Assumptions permut_example.
Goal True.
idtac " ".

idtac "-------------------  not_a_permutation  --------------------".
idtac " ".

idtac "#> not_a_permutation".
idtac "Possible points: 2".
check_type @not_a_permutation ((~ @Permutation nat [1; 1] [1; 2])).
idtac "Assumptions:".
Abort.
Print Assumptions not_a_permutation.
Goal True.
idtac " ".

idtac "-------------------  Forall_perm  --------------------".
idtac " ".

idtac "#> Forall_perm".
idtac "Possible points: 3".
check_type @Forall_perm (
(forall (A : Type) (f : A -> Prop) (al bl : list A),
 @Permutation A al bl -> @Forall A f al -> @Forall A f bl)).
idtac "Assumptions:".
Abort.
Print Assumptions Forall_perm.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 10".
idtac "Max points - advanced: 10".
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
idtac "---------- Permutation_properties ---------".
idtac "MANUAL".
idtac "---------- permut_example ---------".
Print Assumptions permut_example.
idtac "---------- not_a_permutation ---------".
Print Assumptions not_a_permutation.
idtac "---------- Forall_perm ---------".
Print Assumptions Forall_perm.
idtac "".
idtac "********** Advanced **********".
Abort.

(* 2020-08-07 17:08 *)
