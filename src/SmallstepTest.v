Require Import Smallstep.
Parameter MISSING: Type.

Module Check.

Ltac check_type A B :=
match type of A with
| context[MISSING] => idtac "Missing:" A
| ?T => first [unify T B; idtac "Type: ok" | idtac "Type: wrong - should be " B]
end.

Ltac check_exists A :=
match type of A with
| context[MISSING] => idtac "Missing:" A
| ?T => idtac "Is present."; idtac "Check type:" T
end.
End Check.

Require Import Smallstep.
Import Check.

Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Maps.
Require Import Imp.
Module TestSimpleArith1.
Import SimpleArith1.
Goal True.
idtac "Entering exercise test_step_2 (standard): 1 point".
Abort.
Import SimpleArith1.
Goal True.
idtac " ".

idtac "#> SimpleArith1.test_step_2".
check_type @SimpleArith1.test_step_2 (P(C 0)(P(C 2)(P(C 0)(C 3)))==> P(C 0)(P(C 2)(C(0 + 3)))).
idtac "Assumptions:".
Abort.
Print Assumptions SimpleArith1.test_step_2.
Goal True.
idtac " ".

idtac "Exiting exercise (test_step_2)".
idtac " ".
Abort.

End TestSimpleArith1.
Module TestSimpleArith2.
Import SimpleArith2.
Import SimpleArith1.
End TestSimpleArith2.
Module TestSimpleArith3.
Import SimpleArith3.
Import SimpleArith1.
End TestSimpleArith3.
Goal True.
idtac "Entering exercise redo_determinism (standard): 3 points".
idtac " ".

idtac "#> step_deterministic".
check_type @step_deterministic (deterministic step).
idtac "Assumptions:".
Abort.
Print Assumptions step_deterministic.
Goal True.
idtac " ".

idtac "Exiting exercise (redo_determinism)".
idtac " ".
Abort.

Module TestTemp4.
Import Temp4.
Goal True.
idtac "Entering exercise smallstep_bools (standard): 1 point".
Abort.
Import Temp4.
Goal True.
idtac " ".

idtac "Manually graded.".
idtac " ".

idtac "Exiting exercise (smallstep_bools)".
idtac " ".
Abort.

Module TestTemp5.
Import Temp5.
Goal True.
idtac "Entering exercise smallstep_bool_shortcut (standard): 2 points".
Abort.
Import Temp4.Temp5.
Goal True.
idtac " ".

idtac "#> Temp4.Temp5.bool_step_prop4_holds".
check_type @Temp4.Temp5.bool_step_prop4_holds (bool_step_prop4).
idtac "Assumptions:".
Abort.
Print Assumptions Temp4.Temp5.bool_step_prop4_holds.
Goal True.
idtac " ".

idtac "Exiting exercise (smallstep_bool_shortcut)".
idtac " ".
Abort.

End TestTemp5.
End TestTemp4.
Goal True.
idtac "Entering exercise test_multistep_4 (standard): 2 points".
idtac " ".

idtac "#> test_multistep_4".
check_type @test_multistep_4 (P(C 0)(P(C 2)(P(C 0)(C 3)))==>* P(C 0)(C(2 +(0 + 3)))).
idtac "Assumptions:".
Abort.
Print Assumptions test_multistep_4.
Goal True.
idtac " ".

idtac "Exiting exercise (test_multistep_4)".
idtac " ".

idtac "Entering exercise multistep_congr_2 (standard): 2 points".
idtac " ".

idtac "#> multistep_congr_2".
check_type @multistep_congr_2 (forall t1 t2 t2', value t1 -> t2 ==>* t2' -> P t1 t2 ==>* P t1 t2').
idtac "Assumptions:".
Abort.
Print Assumptions multistep_congr_2.
Goal True.
idtac " ".

idtac "Exiting exercise (multistep_congr_2)".
idtac " ".

idtac "Entering exercise eval__multistep (standard): 3 points".
idtac " ".

idtac "#> eval__multistep".
check_type @eval__multistep (forall t n, t \\ n -> t ==>* C n).
idtac "Assumptions:".
Abort.
Print Assumptions eval__multistep.
Goal True.
idtac " ".

idtac "Exiting exercise (eval__multistep)".
idtac " ".

idtac "Entering exercise eval__multistep_inf (advanced): 3 points".
idtac " ".

idtac "Exiting exercise (eval__multistep_inf)".
idtac " ".

idtac "Entering exercise step__eval (standard): 3 points".
idtac " ".

idtac "#> step__eval".
check_type @step__eval (forall t t' n, t ==> t' -> t' \\ n -> t \\ n).
idtac "Assumptions:".
Abort.
Print Assumptions step__eval.
Goal True.
idtac " ".

idtac "Exiting exercise (step__eval)".
idtac " ".

idtac "Entering exercise multistep__eval (standard): 3 points".
idtac " ".

idtac "#> multistep__eval".
check_type @multistep__eval (forall t t', normal_form_of t t' -> exists n, t' = C n /\ t \\ n).
idtac "Assumptions:".
Abort.
Print Assumptions multistep__eval.
Goal True.
idtac " ".

idtac "Exiting exercise (multistep__eval)".
idtac " ".

idtac "Entering exercise combined_properties (standard): 4 points".
idtac " ".

idtac "Manually graded.".
idtac " ".

idtac "Exiting exercise (combined_properties)".
idtac " ".
Abort.

Module TestCImp.
Import CImp.
End TestCImp.
Goal True.
idtac "Entering exercise compiler_is_correct (advanced): 3 points".
idtac " ".

idtac "#> compiler_is_correct_statement".
check_type @compiler_is_correct_statement (Prop).
idtac "Assumptions:".
Abort.
Print Assumptions compiler_is_correct_statement.
Goal True.
idtac " ".

idtac "#> compiler_is_correct".
check_type @compiler_is_correct (compiler_is_correct_statement).
idtac "Assumptions:".
Abort.
Print Assumptions compiler_is_correct.
Goal True.
idtac " ".

idtac "Exiting exercise (compiler_is_correct)".
idtac " ".

idtac "Max points - regular: 24".
idtac "Max points - advanced: 30".
Abort.
