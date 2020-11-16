Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From PLF Require Import RecordSub.

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

From PLF Require Import RecordSub.
Import Check.

Goal True.

idtac "-------------------  subtyping_example_1  --------------------".
idtac " ".

idtac "#> RecordSub.Examples.subtyping_example_1".
idtac "Possible points: 2".
check_type @RecordSub.Examples.subtyping_example_1 (
(RecordSub.subtype RecordSub.Examples.TRcd_kj RecordSub.Examples.TRcd_j)).
idtac "Assumptions:".
Abort.
Print Assumptions RecordSub.Examples.subtyping_example_1.
Goal True.
idtac " ".

idtac "-------------------  subtyping_example_2  --------------------".
idtac " ".

idtac "#> RecordSub.Examples.subtyping_example_2".
idtac "Possible points: 1".
check_type @RecordSub.Examples.subtyping_example_2 (
(RecordSub.subtype
   (RecordSub.Ty_Arrow RecordSub.Ty_Top RecordSub.Examples.TRcd_kj)
   (RecordSub.Ty_Arrow
      (RecordSub.Ty_Arrow RecordSub.Examples.C RecordSub.Examples.C)
      RecordSub.Examples.TRcd_j))).
idtac "Assumptions:".
Abort.
Print Assumptions RecordSub.Examples.subtyping_example_2.
Goal True.
idtac " ".

idtac "-------------------  subtyping_example_3  --------------------".
idtac " ".

idtac "#> RecordSub.Examples.subtyping_example_3".
idtac "Possible points: 1".
check_type @RecordSub.Examples.subtyping_example_3 (
(RecordSub.subtype
   (RecordSub.Ty_Arrow RecordSub.Ty_RNil
      (RecordSub.Ty_RCons RecordSub.Examples.j RecordSub.Examples.A
         RecordSub.Ty_RNil))
   (RecordSub.Ty_Arrow
      (RecordSub.Ty_RCons RecordSub.Examples.k RecordSub.Examples.B
         RecordSub.Ty_RNil) RecordSub.Ty_RNil))).
idtac "Assumptions:".
Abort.
Print Assumptions RecordSub.Examples.subtyping_example_3.
Goal True.
idtac " ".

idtac "-------------------  subtyping_example_4  --------------------".
idtac " ".

idtac "#> RecordSub.Examples.subtyping_example_4".
idtac "Possible points: 2".
check_type @RecordSub.Examples.subtyping_example_4 (
(RecordSub.subtype
   (RecordSub.Ty_RCons RecordSub.Examples.x RecordSub.Examples.A
      (RecordSub.Ty_RCons RecordSub.Examples.y RecordSub.Examples.B
         (RecordSub.Ty_RCons RecordSub.Examples.z RecordSub.Examples.C
            RecordSub.Ty_RNil)))
   (RecordSub.Ty_RCons RecordSub.Examples.z RecordSub.Examples.C
      (RecordSub.Ty_RCons RecordSub.Examples.y RecordSub.Examples.B
         (RecordSub.Ty_RCons RecordSub.Examples.x RecordSub.Examples.A
            RecordSub.Ty_RNil))))).
idtac "Assumptions:".
Abort.
Print Assumptions RecordSub.Examples.subtyping_example_4.
Goal True.
idtac " ".

idtac "-------------------  rcd_types_match_informal  --------------------".
idtac " ".

idtac "#> Manually graded: RecordSub.rcd_types_match_informal".
idtac "Possible points: 3".
print_manual_grade RecordSub.manual_grade_for_rcd_types_match_informal.
idtac " ".

idtac "-------------------  typing_example_0  --------------------".
idtac " ".

idtac "#> RecordSub.Examples2.typing_example_0".
idtac "Possible points: 1".
check_type @RecordSub.Examples2.typing_example_0 (
(RecordSub.has_type (@Maps.empty RecordSub.ty) RecordSub.Examples2.trcd_kj
   RecordSub.Examples.TRcd_kj)).
idtac "Assumptions:".
Abort.
Print Assumptions RecordSub.Examples2.typing_example_0.
Goal True.
idtac " ".

idtac "-------------------  typing_example_1  --------------------".
idtac " ".

idtac "#> RecordSub.Examples2.typing_example_1".
idtac "Possible points: 2".
check_type @RecordSub.Examples2.typing_example_1 (
(RecordSub.has_type (@Maps.empty RecordSub.ty)
   (RecordSub.tm_app
      (RecordSub.tm_abs RecordSub.Examples.x RecordSub.Examples.TRcd_j
         (RecordSub.tm_rproj (RecordSub.tm_var RecordSub.Examples.x)
            RecordSub.Examples.j)) RecordSub.Examples2.trcd_kj)
   (RecordSub.Ty_Arrow RecordSub.Examples.B RecordSub.Examples.B))).
idtac "Assumptions:".
Abort.
Print Assumptions RecordSub.Examples2.typing_example_1.
Goal True.
idtac " ".

idtac "-------------------  canonical_forms_of_arrow_types  --------------------".
idtac " ".

idtac "#> RecordSub.canonical_forms_of_arrow_types".
idtac "Possible points: 3".
check_type @RecordSub.canonical_forms_of_arrow_types (
(forall (Gamma : RecordSub.context) (s : RecordSub.tm) (T1 T2 : RecordSub.ty),
 RecordSub.has_type Gamma s (RecordSub.Ty_Arrow T1 T2) ->
 RecordSub.value s ->
 exists (x : String.string) (S1 : RecordSub.ty) (s2 : RecordSub.tm),
   s = RecordSub.tm_abs x S1 s2)).
idtac "Assumptions:".
Abort.
Print Assumptions RecordSub.canonical_forms_of_arrow_types.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 15".
idtac "Max points - advanced: 15".
idtac "".
idtac "Allowed Axioms:".
idtac "functional_extensionality".
idtac "FunctionalExtensionality.functional_extensionality_dep".
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
idtac "---------- RecordSub.Examples.subtyping_example_1 ---------".
Print Assumptions RecordSub.Examples.subtyping_example_1.
idtac "---------- RecordSub.Examples.subtyping_example_2 ---------".
Print Assumptions RecordSub.Examples.subtyping_example_2.
idtac "---------- RecordSub.Examples.subtyping_example_3 ---------".
Print Assumptions RecordSub.Examples.subtyping_example_3.
idtac "---------- RecordSub.Examples.subtyping_example_4 ---------".
Print Assumptions RecordSub.Examples.subtyping_example_4.
idtac "---------- rcd_types_match_informal ---------".
idtac "MANUAL".
idtac "---------- RecordSub.Examples2.typing_example_0 ---------".
Print Assumptions RecordSub.Examples2.typing_example_0.
idtac "---------- RecordSub.Examples2.typing_example_1 ---------".
Print Assumptions RecordSub.Examples2.typing_example_1.
idtac "---------- RecordSub.canonical_forms_of_arrow_types ---------".
Print Assumptions RecordSub.canonical_forms_of_arrow_types.
idtac "".
idtac "********** Advanced **********".
Abort.

(* 2020-09-09 21:09 *)
