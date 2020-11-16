Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From PLF Require Import Stlc.

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

From PLF Require Import Stlc.
Import Check.

Goal True.

idtac "-------------------  substi_correct  --------------------".
idtac " ".

idtac "#> STLC.substi_correct".
idtac "Possible points: 3".
check_type @STLC.substi_correct (
(forall (s : STLC.tm) (x : String.string) (t t' : STLC.tm),
 STLC.subst x s t = t' <-> STLC.substi s x t t')).
idtac "Assumptions:".
Abort.
Print Assumptions STLC.substi_correct.
Goal True.
idtac " ".

idtac "-------------------  step_example5  --------------------".
idtac " ".

idtac "#> STLC.step_example5".
idtac "Possible points: 2".
check_type @STLC.step_example5 (
(STLC.multistep
   (STLC.tm_app
      (STLC.tm_app
         (STLC.tm_abs STLC.x
            (STLC.Ty_Arrow (STLC.Ty_Arrow STLC.Ty_Bool STLC.Ty_Bool)
               (STLC.Ty_Arrow STLC.Ty_Bool STLC.Ty_Bool))
            (STLC.tm_var STLC.x))
         (STLC.tm_abs STLC.x (STLC.Ty_Arrow STLC.Ty_Bool STLC.Ty_Bool)
            (STLC.tm_var STLC.x)))
      (STLC.tm_abs STLC.x STLC.Ty_Bool (STLC.tm_var STLC.x)))
   (STLC.tm_abs STLC.x STLC.Ty_Bool (STLC.tm_var STLC.x)))).
idtac "Assumptions:".
Abort.
Print Assumptions STLC.step_example5.
Goal True.
idtac " ".

idtac "-------------------  typing_example_3  --------------------".
idtac " ".

idtac "#> STLC.typing_example_3".
idtac "Possible points: 2".
check_type @STLC.typing_example_3 (
(exists T : STLC.ty,
   STLC.has_type (@Maps.empty STLC.ty)
     (STLC.tm_abs STLC.x (STLC.Ty_Arrow STLC.Ty_Bool STLC.Ty_Bool)
        (STLC.tm_abs STLC.y (STLC.Ty_Arrow STLC.Ty_Bool STLC.Ty_Bool)
           (STLC.tm_abs STLC.z STLC.Ty_Bool
              (STLC.tm_app (STLC.tm_var STLC.y)
                 (STLC.tm_app (STLC.tm_var STLC.x) (STLC.tm_var STLC.z))))))
     T)).
idtac "Assumptions:".
Abort.
Print Assumptions STLC.typing_example_3.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 7".
idtac "Max points - advanced: 7".
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
idtac "---------- STLC.substi_correct ---------".
Print Assumptions STLC.substi_correct.
idtac "---------- STLC.step_example5 ---------".
Print Assumptions STLC.step_example5.
idtac "---------- STLC.typing_example_3 ---------".
Print Assumptions STLC.typing_example_3.
idtac "".
idtac "********** Advanced **********".
Abort.

(* 2020-09-09 21:08 *)
