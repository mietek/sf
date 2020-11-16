Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From VFA Require Import Extract.

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

From VFA Require Import Extract.
Import Check.

Goal True.

idtac "-------------------  sort_int_correct  --------------------".
idtac " ".

idtac "#> sort_int_correct".
idtac "Possible points: 3".
check_type @sort_int_correct (
(forall al : list int,
 @Permutation.Permutation int al (sort_int al) /\ sorted (sort_int al))).
idtac "Assumptions:".
Abort.
Print Assumptions sort_int_correct.
Goal True.
idtac " ".

idtac "-------------------  lookup_insert_eq  --------------------".
idtac " ".

idtac "#> lookup_insert_eq".
idtac "Possible points: 2".
check_type @lookup_insert_eq (
(forall (V : Type) (default : V) (t : tree V) (k : key) (v : V),
 @lookup V default k (@insert V k v t) = v)).
idtac "Assumptions:".
Abort.
Print Assumptions lookup_insert_eq.
Goal True.
idtac " ".

idtac "-------------------  lookup_insert_neq  --------------------".
idtac " ".

idtac "#> lookup_insert_neq".
idtac "Possible points: 3".
check_type @lookup_insert_neq (
(forall (V : Type) (default : V) (t : tree V) (k k' : key) (v : V),
 k <> k' -> @lookup V default k' (@insert V k v t) = @lookup V default k' t)).
idtac "Assumptions:".
Abort.
Print Assumptions lookup_insert_neq.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 8".
idtac "Max points - advanced: 8".
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
idtac "---------- sort_int_correct ---------".
Print Assumptions sort_int_correct.
idtac "---------- lookup_insert_eq ---------".
Print Assumptions lookup_insert_eq.
idtac "---------- lookup_insert_neq ---------".
Print Assumptions lookup_insert_neq.
idtac "".
idtac "********** Advanced **********".
Abort.

(* 2020-08-07 17:08 *)
