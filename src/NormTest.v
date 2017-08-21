Require Import Norm.
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

Require Import Norm.
Import Check.

Goal True.
idtac "Entering exercise norm_fail (standard): 2 points".
idtac " ".

idtac "Manually graded.".
idtac " ".

idtac "Exiting exercise (norm_fail)".
idtac " ".

idtac "Entering exercise norm (standard): 5 points".
idtac " ".

idtac "Exiting exercise (norm)".
idtac " ".
Abort.

Require Import Coq.Lists.List.
Import ListNotations.
Require Import Maps.
Require Import Smallstep.
Goal True.
idtac "Max points - regular: 7".
idtac "Max points - advanced: 7".
Abort.
