Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From VFA Require Import Decide.

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

From VFA Require Import Decide.
Import Check.

Goal True.

idtac "-------------------  insert_sorted_le_dec  --------------------".
idtac " ".

idtac "#> ScratchPad2.insert_sorted".
idtac "Possible points: 2".
check_type @ScratchPad2.insert_sorted (
(forall (a : nat) (l : list nat),
 ScratchPad2.sorted l -> ScratchPad2.sorted (ScratchPad2.insert a l))).
idtac "Assumptions:".
Abort.
Print Assumptions ScratchPad2.insert_sorted.
Goal True.
idtac " ".

idtac "-------------------  list_nat_in  --------------------".
idtac " ".

idtac "#> list_nat_in".
idtac "Possible points: 2".
check_type @list_nat_in (
(forall (i : nat) (al : list nat),
 {@List.In nat i al} + {~ @List.In nat i al})).
idtac "Assumptions:".
Abort.
Print Assumptions list_nat_in.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 4".
idtac "Max points - advanced: 4".
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
idtac "---------- ScratchPad2.insert_sorted ---------".
Print Assumptions ScratchPad2.insert_sorted.
idtac "---------- list_nat_in ---------".
Print Assumptions list_nat_in.
idtac "".
idtac "********** Advanced **********".
Abort.

(* 2020-08-07 17:10 *)
