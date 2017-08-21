Require Import Stlc.
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

Require Import Stlc.
Import Check.

Require Import Maps.
Require Import Smallstep.
Require Import Types.
Module TestSTLC.
Import STLC.
Goal True.
idtac "Entering exercise substi (standard): 3 points".
Abort.
Import STLC.
Goal True.
idtac " ".

idtac "#> STLC.substi_correct".
check_type @STLC.substi_correct (forall s x t t', [x := s]t = t' <-> substi s x t t').
idtac "Assumptions:".
Abort.
Print Assumptions STLC.substi_correct.
Goal True.
idtac " ".

idtac "Exiting exercise (substi)".
idtac " ".

idtac "Entering exercise step_example3 (standard): 2 points".
Abort.
Import STLC.
Goal True.
idtac " ".

idtac "#> STLC.step_example5".
check_type @STLC.step_example5 (tapp(tapp idBBBB idBB)idB ==>* idB).
idtac "Assumptions:".
Abort.
Print Assumptions STLC.step_example5.
Goal True.
idtac " ".

idtac "#> STLC.step_example5_with_normalize".
check_type @STLC.step_example5_with_normalize (tapp(tapp idBBBB idBB)idB ==>* idB).
idtac "Assumptions:".
Abort.
Print Assumptions STLC.step_example5_with_normalize.
Goal True.
idtac " ".

idtac "Exiting exercise (step_example3)".
idtac " ".

idtac "Entering exercise typing_example_3 (standard): 2 points".
Abort.
Import STLC.
Goal True.
idtac " ".

idtac "#> STLC.typing_example_3".
check_type @STLC.typing_example_3 (exists T, empty |-(tabs x(TArrow TBool TBool)(tabs y(TArrow TBool TBool)(tabs z TBool(tapp(tvar y)(tapp(tvar x)(tvar z))))))\in T).
idtac "Assumptions:".
Abort.
Print Assumptions STLC.typing_example_3.
Goal True.
idtac " ".

idtac "Exiting exercise (typing_example_3)".
idtac " ".
Abort.

End TestSTLC.
Goal True.
idtac "Max points - regular: 7".
idtac "Max points - advanced: 7".
Abort.
