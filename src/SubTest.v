Require Import Sub.
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

Require Import Sub.
Import Check.

Require Import Maps.
Require Import Types.
Require Import Smallstep.
Goal True.
idtac "Entering exercise arrow_sub_wrong (standard): 2 points".
idtac " ".

idtac "Manually graded.".
idtac " ".

idtac "Exiting exercise (arrow_sub_wrong)".
idtac " ".

idtac "Entering exercise subtype_order (standard): 2 points".
idtac " ".

idtac "Manually graded.".
idtac " ".

idtac "Exiting exercise (subtype_order)".
idtac " ".

idtac "Entering exercise subtype_instances_tf_2 (standard): 1 point".
idtac " ".

idtac "Manually graded.".
idtac " ".

idtac "Exiting exercise (subtype_instances_tf_2)".
idtac " ".

idtac "Entering exercise subtype_concepts_tf (standard): 1 point".
idtac " ".

idtac "Manually graded.".
idtac " ".

idtac "Exiting exercise (subtype_concepts_tf)".
idtac " ".

idtac "Entering exercise proper_subtypes (standard): 2 points".
idtac " ".

idtac "Manually graded.".
idtac " ".

idtac "Exiting exercise (proper_subtypes)".
idtac " ".

idtac "Entering exercise small_large_1 (standard): 2 points".
idtac " ".

idtac "Manually graded.".
idtac " ".

idtac "Exiting exercise (small_large_1)".
idtac " ".

idtac "Entering exercise small_large_2 (standard): 2 points".
idtac " ".

idtac "Manually graded.".
idtac " ".

idtac "Exiting exercise (small_large_2)".
idtac " ".

idtac "Entering exercise small_large_4 (standard): 2 points".
idtac " ".

idtac "Manually graded.".
idtac " ".

idtac "Exiting exercise (small_large_4)".
idtac " ".

idtac "Entering exercise smallest_1 (standard): 2 points".
idtac " ".

idtac "Manually graded.".
idtac " ".

idtac "Exiting exercise (smallest_1)".
idtac " ".

idtac "Entering exercise smallest_2 (standard): 2 points".
idtac " ".

idtac "Manually graded.".
idtac " ".

idtac "Exiting exercise (smallest_2)".
idtac " ".

idtac "Entering exercise pair_permutation (standard): 2 points".
idtac " ".

idtac "Manually graded.".
idtac " ".

idtac "Exiting exercise (pair_permutation)".
idtac " ".
Abort.

Module TestExamples.
Import Examples.
End TestExamples.
Module TestExamples2.
Import Examples2.
Import Examples.
End TestExamples2.
Goal True.
idtac "Entering exercise variations (standard): 2 points".
idtac " ".

idtac "Manually graded.".
idtac " ".

idtac "Exiting exercise (variations)".
idtac " ".

idtac "Entering exercise products (standard): 4 points".
idtac " ".
Abort.

Module TestProductExtension.
Import ProductExtension.
Goal True.
idtac "#> ProductExtension.progress".
check_type @ProductExtension.progress (forall t T, empty |- t \in T -> value t \/ exists t', t ==> t').
idtac "Assumptions:".
Abort.
Print Assumptions ProductExtension.progress.
Goal True.
idtac " ".

idtac "#> ProductExtension.preservation".
check_type @ProductExtension.preservation (forall t t' T, empty |- t \in T -> t ==> t' -> empty |- t' \in T).
idtac "Assumptions:".
Abort.
Print Assumptions ProductExtension.preservation.
Goal True.
idtac " ".
Abort.

End TestProductExtension.
Goal True.
idtac "Exiting exercise (products)".
idtac " ".

idtac "Max points - regular: 26".
idtac "Max points - advanced: 26".
Abort.
