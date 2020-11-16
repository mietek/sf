Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From PLF Require Import MoreStlc.

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

From PLF Require Import MoreStlc.
Import Check.

Goal True.

idtac "-------------------  STLCE_definitions  --------------------".
idtac " ".

idtac "#> Manually graded: STLCExtended.extensions_definition".
idtac "Possible points: 3".
print_manual_grade STLCExtended.manual_grade_for_extensions_definition.
idtac " ".

idtac "-------------------  STLCE_examples  --------------------".
idtac " ".

idtac "#> STLCExtended.Examples.Prodtest.typechecks".
idtac "Possible points: 0.25".
check_type @STLCExtended.Examples.Prodtest.typechecks (
(STLCExtended.has_type (@Maps.empty STLCExtended.ty)
   STLCExtended.Examples.Prodtest.test STLCExtended.Ty_Nat)).
idtac "Assumptions:".
Abort.
Print Assumptions STLCExtended.Examples.Prodtest.typechecks.
Goal True.
idtac " ".

idtac "#> STLCExtended.Examples.Prodtest.reduces".
idtac "Possible points: 0.25".
check_type @STLCExtended.Examples.Prodtest.reduces (
(STLCExtended.multistep STLCExtended.Examples.Prodtest.test
   (STLCExtended.tm_const 6))).
idtac "Assumptions:".
Abort.
Print Assumptions STLCExtended.Examples.Prodtest.reduces.
Goal True.
idtac " ".

idtac "#> STLCExtended.Examples.LetTest.typechecks".
idtac "Possible points: 0.25".
check_type @STLCExtended.Examples.LetTest.typechecks (
(STLCExtended.has_type (@Maps.empty STLCExtended.ty)
   STLCExtended.Examples.LetTest.test STLCExtended.Ty_Nat)).
idtac "Assumptions:".
Abort.
Print Assumptions STLCExtended.Examples.LetTest.typechecks.
Goal True.
idtac " ".

idtac "#> STLCExtended.Examples.LetTest.reduces".
idtac "Possible points: 0.25".
check_type @STLCExtended.Examples.LetTest.reduces (
(STLCExtended.multistep STLCExtended.Examples.LetTest.test
   (STLCExtended.tm_const 6))).
idtac "Assumptions:".
Abort.
Print Assumptions STLCExtended.Examples.LetTest.reduces.
Goal True.
idtac " ".

idtac "#> STLCExtended.Examples.FixTest1.typechecks".
idtac "Possible points: 0.25".
check_type @STLCExtended.Examples.FixTest1.typechecks (
(STLCExtended.has_type (@Maps.empty STLCExtended.ty)
   STLCExtended.Examples.FixTest1.fact
   (STLCExtended.Ty_Arrow STLCExtended.Ty_Nat STLCExtended.Ty_Nat))).
idtac "Assumptions:".
Abort.
Print Assumptions STLCExtended.Examples.FixTest1.typechecks.
Goal True.
idtac " ".

idtac "#> STLCExtended.Examples.FixTest1.reduces".
idtac "Possible points: 0.25".
check_type @STLCExtended.Examples.FixTest1.reduces (
(STLCExtended.multistep
   (STLCExtended.tm_app STLCExtended.Examples.FixTest1.fact
      (STLCExtended.tm_const 4)) (STLCExtended.tm_const 24))).
idtac "Assumptions:".
Abort.
Print Assumptions STLCExtended.Examples.FixTest1.reduces.
Goal True.
idtac " ".

idtac "#> STLCExtended.Examples.FixTest2.typechecks".
idtac "Possible points: 0.25".
check_type @STLCExtended.Examples.FixTest2.typechecks (
(STLCExtended.has_type (@Maps.empty STLCExtended.ty)
   STLCExtended.Examples.FixTest2.map
   (STLCExtended.Ty_Arrow
      (STLCExtended.Ty_Arrow STLCExtended.Ty_Nat STLCExtended.Ty_Nat)
      (STLCExtended.Ty_Arrow (STLCExtended.Ty_List STLCExtended.Ty_Nat)
         (STLCExtended.Ty_List STLCExtended.Ty_Nat))))).
idtac "Assumptions:".
Abort.
Print Assumptions STLCExtended.Examples.FixTest2.typechecks.
Goal True.
idtac " ".

idtac "#> STLCExtended.Examples.FixTest2.reduces".
idtac "Possible points: 0.25".
check_type @STLCExtended.Examples.FixTest2.reduces (
(STLCExtended.multistep
   (STLCExtended.tm_app
      (STLCExtended.tm_app STLCExtended.Examples.FixTest2.map
         (STLCExtended.tm_abs STLCExtended.Examples.a STLCExtended.Ty_Nat
            (STLCExtended.tm_succ
               (STLCExtended.tm_var STLCExtended.Examples.a))))
      (STLCExtended.tm_cons (STLCExtended.tm_const 1)
         (STLCExtended.tm_cons (STLCExtended.tm_const 2)
            (STLCExtended.tm_nil STLCExtended.Ty_Nat))))
   (STLCExtended.tm_cons (STLCExtended.tm_const 2)
      (STLCExtended.tm_cons (STLCExtended.tm_const 3)
         (STLCExtended.tm_nil STLCExtended.Ty_Nat))))).
idtac "Assumptions:".
Abort.
Print Assumptions STLCExtended.Examples.FixTest2.reduces.
Goal True.
idtac " ".

idtac "#> STLCExtended.Examples.FixTest3.typechecks".
idtac "Possible points: 0.25".
check_type @STLCExtended.Examples.FixTest3.typechecks (
(STLCExtended.has_type (@Maps.empty STLCExtended.ty)
   STLCExtended.Examples.FixTest3.equal
   (STLCExtended.Ty_Arrow STLCExtended.Ty_Nat
      (STLCExtended.Ty_Arrow STLCExtended.Ty_Nat STLCExtended.Ty_Nat)))).
idtac "Assumptions:".
Abort.
Print Assumptions STLCExtended.Examples.FixTest3.typechecks.
Goal True.
idtac " ".

idtac "#> STLCExtended.Examples.FixTest3.reduces".
idtac "Possible points: 0.25".
check_type @STLCExtended.Examples.FixTest3.reduces (
(STLCExtended.multistep
   (STLCExtended.tm_app
      (STLCExtended.tm_app STLCExtended.Examples.FixTest3.equal
         (STLCExtended.tm_const 4)) (STLCExtended.tm_const 4))
   (STLCExtended.tm_const 1))).
idtac "Assumptions:".
Abort.
Print Assumptions STLCExtended.Examples.FixTest3.reduces.
Goal True.
idtac " ".

idtac "#> STLCExtended.Examples.FixTest4.typechecks".
idtac "Possible points: 0.25".
check_type @STLCExtended.Examples.FixTest4.typechecks (
(STLCExtended.has_type (@Maps.empty STLCExtended.ty)
   STLCExtended.Examples.FixTest4.eotest
   (STLCExtended.Ty_Prod STLCExtended.Ty_Nat STLCExtended.Ty_Nat))).
idtac "Assumptions:".
Abort.
Print Assumptions STLCExtended.Examples.FixTest4.typechecks.
Goal True.
idtac " ".

idtac "#> STLCExtended.Examples.FixTest4.reduces".
idtac "Possible points: 0.25".
check_type @STLCExtended.Examples.FixTest4.reduces (
(STLCExtended.multistep STLCExtended.Examples.FixTest4.eotest
   (STLCExtended.tm_pair (STLCExtended.tm_const 0) (STLCExtended.tm_const 1)))).
idtac "Assumptions:".
Abort.
Print Assumptions STLCExtended.Examples.FixTest4.reduces.
Goal True.
idtac " ".

idtac "-------------------  STLCE_progress  --------------------".
idtac " ".

idtac "#> Manually graded: STLCExtended.progress".
idtac "Possible points: 3".
print_manual_grade STLCExtended.manual_grade_for_progress.
idtac " ".

idtac "-------------------  STLCE_subst_preserves_typing  --------------------".
idtac " ".

idtac "#> Manually graded: STLCExtended.substitution_preserves_typing".
idtac "Possible points: 2".
print_manual_grade STLCExtended.manual_grade_for_substitution_preserves_typing.
idtac " ".

idtac "-------------------  STLCE_preservation  --------------------".
idtac " ".

idtac "#> Manually graded: STLCExtended.preservation".
idtac "Possible points: 3".
print_manual_grade STLCExtended.manual_grade_for_preservation.
idtac " ".

idtac " ".

idtac "Max points - standard: 14".
idtac "Max points - advanced: 14".
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
idtac "---------- extensions_definition ---------".
idtac "MANUAL".
idtac "---------- STLCExtended.Examples.Prodtest.typechecks ---------".
Print Assumptions STLCExtended.Examples.Prodtest.typechecks.
idtac "---------- STLCExtended.Examples.Prodtest.reduces ---------".
Print Assumptions STLCExtended.Examples.Prodtest.reduces.
idtac "---------- STLCExtended.Examples.LetTest.typechecks ---------".
Print Assumptions STLCExtended.Examples.LetTest.typechecks.
idtac "---------- STLCExtended.Examples.LetTest.reduces ---------".
Print Assumptions STLCExtended.Examples.LetTest.reduces.
idtac "---------- STLCExtended.Examples.FixTest1.typechecks ---------".
Print Assumptions STLCExtended.Examples.FixTest1.typechecks.
idtac "---------- STLCExtended.Examples.FixTest1.reduces ---------".
Print Assumptions STLCExtended.Examples.FixTest1.reduces.
idtac "---------- STLCExtended.Examples.FixTest2.typechecks ---------".
Print Assumptions STLCExtended.Examples.FixTest2.typechecks.
idtac "---------- STLCExtended.Examples.FixTest2.reduces ---------".
Print Assumptions STLCExtended.Examples.FixTest2.reduces.
idtac "---------- STLCExtended.Examples.FixTest3.typechecks ---------".
Print Assumptions STLCExtended.Examples.FixTest3.typechecks.
idtac "---------- STLCExtended.Examples.FixTest3.reduces ---------".
Print Assumptions STLCExtended.Examples.FixTest3.reduces.
idtac "---------- STLCExtended.Examples.FixTest4.typechecks ---------".
Print Assumptions STLCExtended.Examples.FixTest4.typechecks.
idtac "---------- STLCExtended.Examples.FixTest4.reduces ---------".
Print Assumptions STLCExtended.Examples.FixTest4.reduces.
idtac "---------- progress ---------".
idtac "MANUAL".
idtac "---------- substitution_preserves_typing ---------".
idtac "MANUAL".
idtac "---------- preservation ---------".
idtac "MANUAL".
idtac "".
idtac "********** Advanced **********".
Abort.

(* 2020-09-09 21:08 *)
