Require Import Types.
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

Require Import Types.
Import Check.

Require Import Coq.Arith.Arith.
Require Import Maps.
Require Import Imp.
Require Import Smallstep.
Goal True.
idtac "Entering exercise some_term_is_stuck (standard): 2 points".
idtac " ".

idtac "#> some_term_is_stuck".
check_type @some_term_is_stuck (exists t, stuck t).
idtac "Assumptions:".
Abort.
Print Assumptions some_term_is_stuck.
Goal True.
idtac " ".

idtac "Exiting exercise (some_term_is_stuck)".
idtac " ".

idtac "Entering exercise value_is_nf (standard): 3 points".
idtac " ".

idtac "#> value_is_nf".
check_type @value_is_nf (forall t, value t -> step_normal_form t).
idtac "Assumptions:".
Abort.
Print Assumptions value_is_nf.
Goal True.
idtac " ".

idtac "Exiting exercise (value_is_nf)".
idtac " ".

idtac "Entering exercise finish_progress (standard): 3 points".
idtac " ".

idtac "#> progress".
check_type @progress (forall t T, |- t \in T -> value t \/ exists t', t ==> t').
idtac "Assumptions:".
Abort.
Print Assumptions progress.
Goal True.
idtac " ".

idtac "Exiting exercise (finish_progress)".
idtac " ".

idtac "Entering exercise finish_progress_informal (advanced): 3 points".
idtac " ".

idtac "Manually graded.".
idtac " ".

idtac "Exiting exercise (finish_progress_informal)".
idtac " ".

idtac "Entering exercise finish_preservation (standard): 2 points".
idtac " ".

idtac "#> preservation".
check_type @preservation (forall t t' T, |- t \in T -> t ==> t' -> |- t' \in T).
idtac "Assumptions:".
Abort.
Print Assumptions preservation.
Goal True.
idtac " ".

idtac "Exiting exercise (finish_preservation)".
idtac " ".

idtac "Entering exercise finish_preservation_informal (advanced): 3 points".
idtac " ".

idtac "Manually graded.".
idtac " ".

idtac "Exiting exercise (finish_preservation_informal)".
idtac " ".

idtac "Entering exercise preservation_alternate_proof (standard): 3 points".
idtac " ".

idtac "#> preservation'".
check_type @preservation' (forall t t' T, |- t \in T -> t ==> t' -> |- t' \in T).
idtac "Assumptions:".
Abort.
Print Assumptions preservation'.
Goal True.
idtac " ".

idtac "Exiting exercise (preservation_alternate_proof)".
idtac " ".
Abort.

Module TestNormalizePlayground.
Import NormalizePlayground.
Import Smallstep.
Goal True.
idtac "Entering exercise normalize_ex (standard): 1 point".
Abort.
Import NormalizePlayground.
Goal True.
idtac " ".

idtac "#> NormalizePlayground.normalize_ex".
check_type @NormalizePlayground.normalize_ex (exists e', (P(C 3)(P(C 2)(C 1)))==>* e').
idtac "Assumptions:".
Abort.
Print Assumptions NormalizePlayground.normalize_ex.
Goal True.
idtac " ".

idtac "Exiting exercise (normalize_ex)".
idtac " ".
Abort.

End TestNormalizePlayground.
Goal True.
idtac "Entering exercise subject_expansion (standard): 2 points".
idtac " ".

idtac "Manually graded.".
idtac " ".

idtac "Exiting exercise (subject_expansion)".
idtac " ".

idtac "Entering exercise variation1 (standard): 2 points".
idtac " ".

idtac "Manually graded.".
idtac " ".

idtac "Exiting exercise (variation1)".
idtac " ".

idtac "Entering exercise variation2 (standard): 2 points".
idtac " ".

idtac "Manually graded.".
idtac " ".

idtac "Exiting exercise (variation2)".
idtac " ".

idtac "Entering exercise remove_predzero (standard): 1 point".
idtac " ".

idtac "Manually graded.".
idtac " ".

idtac "Exiting exercise (remove_predzero)".
idtac " ".

idtac "Entering exercise prog_pres_bigstep (advanced): 4 points".
idtac " ".

idtac "Manually graded.".
idtac " ".

idtac "Exiting exercise (prog_pres_bigstep)".
idtac " ".

idtac "Max points - regular: 21".
idtac "Max points - advanced: 31".
Abort.
