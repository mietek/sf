Require Import Auto.
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

Require Import Auto.
Import Check.

Require Import Coq.omega.Omega.
Require Import Maps.
Require Import Imp.
Module TestRepeat.
Import Repeat.
End TestRepeat.
Goal True.
idtac "Max points - regular: 0".
idtac "Max points - advanced: 0".
Abort.
