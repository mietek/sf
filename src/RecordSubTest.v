Require Import RecordSub.
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

Require Import RecordSub.
Import Check.

Require Import Maps.
Require Import Smallstep.
Require Import MoreStlc.
Module TestExamples.
Import Examples.
Goal True.
idtac "Entering exercise subtyping_example_1 (standard): 2 points".
Abort.
Import Examples.
Goal True.
idtac " ".

idtac "#> Examples.subtyping_example_1".
check_type @Examples.subtyping_example_1 (subtype TRcd_kj TRcd_j).
idtac "Assumptions:".
Abort.
Print Assumptions Examples.subtyping_example_1.
Goal True.
idtac " ".

idtac "Exiting exercise (subtyping_example_1)".
idtac " ".

idtac "Entering exercise subtyping_example_2 (standard): 1 point".
Abort.
Import Examples.
Goal True.
idtac " ".

idtac "#> Examples.subtyping_example_2".
check_type @Examples.subtyping_example_2 (subtype(TArrow TTop TRcd_kj)(TArrow(TArrow C C)TRcd_j)).
idtac "Assumptions:".
Abort.
Print Assumptions Examples.subtyping_example_2.
Goal True.
idtac " ".

idtac "Exiting exercise (subtyping_example_2)".
idtac " ".

idtac "Entering exercise subtyping_example_3 (standard): 1 point".
Abort.
Import Examples.
Goal True.
idtac " ".

idtac "#> Examples.subtyping_example_3".
check_type @Examples.subtyping_example_3 (subtype(TArrow TRNil(TRCons j A TRNil))(TArrow(TRCons k B TRNil)TRNil)).
idtac "Assumptions:".
Abort.
Print Assumptions Examples.subtyping_example_3.
Goal True.
idtac " ".

idtac "Exiting exercise (subtyping_example_3)".
idtac " ".

idtac "Entering exercise subtyping_example_4 (standard): 2 points".
Abort.
Import Examples.
Goal True.
idtac " ".

idtac "#> Examples.subtyping_example_4".
check_type @Examples.subtyping_example_4 (subtype(TRCons x A(TRCons y B(TRCons z C TRNil)))(TRCons z C(TRCons y B(TRCons x A TRNil)))).
idtac "Assumptions:".
Abort.
Print Assumptions Examples.subtyping_example_4.
Goal True.
idtac " ".

idtac "Exiting exercise (subtyping_example_4)".
idtac " ".
Abort.

End TestExamples.
Goal True.
idtac "Entering exercise rcd_types_match_informal (standard): 3 points".
idtac " ".

idtac "Exiting exercise (rcd_types_match_informal)".
idtac " ".
Abort.

Module TestExamples2.
Import Examples2.
Import Examples.
Goal True.
idtac "Entering exercise typing_example_0 (standard): 1 point".
Abort.
Import Examples2.
Goal True.
idtac " ".

idtac "#> Examples2.typing_example_0".
check_type @Examples2.typing_example_0 (has_type empty(trcons k(tabs z A(tvar z))(trcons j(tabs z B(tvar z))trnil))TRcd_kj).
idtac "Assumptions:".
Abort.
Print Assumptions Examples2.typing_example_0.
Goal True.
idtac " ".

idtac "Exiting exercise (typing_example_0)".
idtac " ".

idtac "Entering exercise typing_example_1 (standard): 2 points".
Abort.
Import Examples2.
Goal True.
idtac " ".

idtac "#> Examples2.typing_example_1".
check_type @Examples2.typing_example_1 (has_type empty(tapp(tabs x TRcd_j(tproj(tvar x)j))(trcd_kj))(TArrow B B)).
idtac "Assumptions:".
Abort.
Print Assumptions Examples2.typing_example_1.
Goal True.
idtac " ".

idtac "Exiting exercise (typing_example_1)".
idtac " ".
Abort.

End TestExamples2.
Goal True.
idtac "Entering exercise canonical_forms_of_arrow_types (standard): 3 points".
idtac " ".

idtac "#> canonical_forms_of_arrow_types".
check_type @canonical_forms_of_arrow_types (forall Gamma s T1 T2, has_type Gamma s(TArrow T1 T2) -> value s -> exists x, exists S1, exists s2, s = tabs x S1 s2).
idtac "Assumptions:".
Abort.
Print Assumptions canonical_forms_of_arrow_types.
Goal True.
idtac " ".

idtac "Exiting exercise (canonical_forms_of_arrow_types)".
idtac " ".

idtac "Max points - regular: 15".
idtac "Max points - advanced: 15".
Abort.
