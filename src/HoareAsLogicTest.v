Require Import HoareAsLogic.
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

Require Import HoareAsLogic.
Import Check.

Require Import Imp.
Require Import Hoare.
Goal True.
idtac "Entering exercise hoare_proof_sound (standard): 2 points".
idtac " ".

idtac "#> hoare_proof_sound".
check_type @hoare_proof_sound (forall P c Q, hoare_proof P c Q -> {{P}}c{{Q}}).
idtac "Assumptions:".
Abort.
Print Assumptions hoare_proof_sound.
Goal True.
idtac " ".

idtac "Exiting exercise (hoare_proof_sound)".
idtac " ".

idtac "Entering exercise wp_is_precondition (standard): 1 point".
idtac " ".

idtac "#> wp_is_precondition".
check_type @wp_is_precondition (forall c Q, {{wp c Q}}c{{Q}}).
idtac "Assumptions:".
Abort.
Print Assumptions wp_is_precondition.
Goal True.
idtac " ".

idtac "Exiting exercise (wp_is_precondition)".
idtac " ".

idtac "Entering exercise wp_is_weakest (standard): 1 point".
idtac " ".

idtac "#> wp_is_weakest".
check_type @wp_is_weakest (forall c Q P', {{P'}}c{{Q}} -> forall st, P' st -> wp c Q st).
idtac "Assumptions:".
Abort.
Print Assumptions wp_is_weakest.
Goal True.
idtac " ".

idtac "Exiting exercise (wp_is_weakest)".
idtac " ".

idtac "Entering exercise hoare_proof_complete (standard): 5 points".
idtac " ".

idtac "#> hoare_proof_complete".
check_type @hoare_proof_complete (forall P c Q, {{P}}c{{Q}} -> hoare_proof P c Q).
idtac "Assumptions:".
Abort.
Print Assumptions hoare_proof_complete.
Goal True.
idtac " ".

idtac "Exiting exercise (hoare_proof_complete)".
idtac " ".

idtac "Max points - regular: 9".
idtac "Max points - advanced: 9".
Abort.
