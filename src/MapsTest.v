Require Import Maps.
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

Require Import Maps.
Import Check.

Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Logic.FunctionalExtensionality.
Goal True.
idtac "Entering exercise t_update_same (standard): 2 points".
idtac " ".

idtac "#> t_update_same".
check_type @t_update_same (forall X x (m : total_map X), t_update m x(m x) = m).
idtac "Assumptions:".
Abort.
Print Assumptions t_update_same.
Goal True.
idtac " ".

idtac "Exiting exercise (t_update_same)".
idtac " ".

idtac "Entering exercise t_update_permute (standard): 3 points".
idtac " ".

idtac "#> t_update_permute".
check_type @t_update_permute (forall (X : Type) v1 v2 x1 x2 (m : total_map X), x2 <> x1 -> (t_update(t_update m x2 v2)x1 v1) = (t_update(t_update m x1 v1)x2 v2)).
idtac "Assumptions:".
Abort.
Print Assumptions t_update_permute.
Goal True.
idtac " ".

idtac "Exiting exercise (t_update_permute)".
idtac " ".

idtac "Max points - regular: 5".
idtac "Max points - advanced: 5".
Abort.
