Require Import StlcProp.
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

Require Import StlcProp.
Import Check.

Require Import Maps.
Require Import Types.
Require Import Stlc.
Require Import Smallstep.
Module TestSTLCProp.
Import STLCProp.
Import STLC.
Goal True.
idtac "Entering exercise progress_from_term_ind (advanced): 3 points".
Abort.
Import STLCProp.
Goal True.
idtac " ".

idtac "#> STLCProp.progress'".
check_type @STLCProp.progress' (forall t T, empty |- t \in T -> value t \/ exists t', t ==> t').
idtac "Assumptions:".
Abort.
Print Assumptions STLCProp.progress'.
Goal True.
idtac " ".

idtac "Exiting exercise (progress_from_term_ind)".
idtac " ".

idtac "Entering exercise afi (standard): 1 point".
Abort.
Import STLCProp.
Goal True.
idtac " ".

idtac "Manually graded.".
idtac " ".

idtac "Exiting exercise (afi)".
idtac " ".

idtac "Entering exercise subject_expansion_stlc (standard): 2 points".
Abort.
Import STLCProp.
Goal True.
idtac " ".

idtac "Manually graded.".
idtac " ".

idtac "Exiting exercise (subject_expansion_stlc)".
idtac " ".

idtac "Entering exercise types_unique (standard): 3 points".
Abort.
Import STLCProp.
Goal True.
idtac " ".

idtac "Manually graded.".
idtac " ".

idtac "Exiting exercise (types_unique)".
idtac " ".

idtac "Entering exercise progress_preservation_statement (standard): 1 point".
Abort.
Import STLCProp.
Goal True.
idtac " ".

idtac "Manually graded.".
idtac " ".

idtac "Exiting exercise (progress_preservation_statement)".
idtac " ".

idtac "Entering exercise stlc_variation1 (standard): 2 points".
Abort.
Import STLCProp.
Goal True.
idtac " ".

idtac "Manually graded.".
idtac " ".

idtac "Exiting exercise (stlc_variation1)".
idtac " ".

idtac "Entering exercise stlc_variation2 (standard): 2 points".
Abort.
Import STLCProp.
Goal True.
idtac " ".

idtac "Manually graded.".
idtac " ".

idtac "Exiting exercise (stlc_variation2)".
idtac " ".

idtac "Entering exercise stlc_variation3 (standard): 2 points".
Abort.
Import STLCProp.
Goal True.
idtac " ".

idtac "Manually graded.".
idtac " ".

idtac "Exiting exercise (stlc_variation3)".
idtac " ".
Abort.

End TestSTLCProp.
Module TestSTLCArith.
Import STLCArith.
Import STLC.
Goal True.
idtac "Entering exercise stlc_arith (standard): 4 points".
Abort.
Import STLCArith.
Goal True.
idtac " ".

idtac "Manually graded.".
idtac " ".

idtac "Exiting exercise (stlc_arith)".
idtac " ".
Abort.

End TestSTLCArith.
Goal True.
idtac "Max points - regular: 17".
idtac "Max points - advanced: 20".
Abort.
