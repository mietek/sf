Require Import Typechecking.
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

Require Import Typechecking.
Import Check.

Require Import Coq.Bool.Bool.
Require Import Maps.
Require Import Smallstep.
Require Import Stlc.
Module TestSTLCChecker.
Import STLCChecker.
Import STLC.
End TestSTLCChecker.
Goal True.
idtac "Entering exercise typechecker_extensions (standard): 5 points".
idtac " ".
Abort.

Module TestTypecheckerExtensions.
Import TypecheckerExtensions.
Require Import MoreStlc.
Import STLCExtended.
End TestTypecheckerExtensions.
Goal True.
idtac "Exiting exercise (typechecker_extensions)".
idtac " ".

idtac "Max points - regular: 5".
idtac "Max points - advanced: 5".
Abort.
