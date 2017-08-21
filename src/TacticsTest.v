Require Import Tactics.
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

Require Import Tactics.
Import Check.

Require Export Poly.
Goal True.
idtac "Entering exercise apply_exercise1 (standard): 3 points".
idtac " ".

idtac "#> rev_exercise1".
check_type @rev_exercise1 (forall (l l' : list nat), l = rev l' -> l' = rev l).
idtac "Assumptions:".
Abort.
Print Assumptions rev_exercise1.
Goal True.
idtac " ".

idtac "Exiting exercise (apply_exercise1)".
idtac " ".

idtac "Entering exercise inversion_ex3 (standard): 1 point".
idtac " ".

idtac "#> inversion_ex3".
check_type @inversion_ex3 (forall (X : Type) (x y z : X) (l j : list X), x :: y :: l = z :: j -> y :: l = x :: j -> x = y).
idtac "Assumptions:".
Abort.
Print Assumptions inversion_ex3.
Goal True.
idtac " ".

idtac "Exiting exercise (inversion_ex3)".
idtac " ".

idtac "Entering exercise inversion_ex6 (standard): 1 point".
idtac " ".

idtac "#> inversion_ex6".
check_type @inversion_ex6 (forall (X : Type) (x y z : X) (l j : list X), x :: y :: l = [] -> y :: l = z :: j -> x = z).
idtac "Assumptions:".
Abort.
Print Assumptions inversion_ex6.
Goal True.
idtac " ".

idtac "Exiting exercise (inversion_ex6)".
idtac " ".

idtac "Entering exercise plus_n_n_injective (standard): 3 points".
idtac " ".

idtac "#> plus_n_n_injective".
check_type @plus_n_n_injective (forall n m, n + n = m + m -> n = m).
idtac "Assumptions:".
Abort.
Print Assumptions plus_n_n_injective.
Goal True.
idtac " ".

idtac "Exiting exercise (plus_n_n_injective)".
idtac " ".

idtac "Entering exercise beq_nat_true (standard): 2 points".
idtac " ".

idtac "#> beq_nat_true".
check_type @beq_nat_true (forall n m, beq_nat n m = true -> n = m).
idtac "Assumptions:".
Abort.
Print Assumptions beq_nat_true.
Goal True.
idtac " ".

idtac "Exiting exercise (beq_nat_true)".
idtac " ".

idtac "Entering exercise beq_nat_true_informal (advanced): 2 points".
idtac " ".

idtac "Manually graded.".
idtac " ".

idtac "Exiting exercise (beq_nat_true_informal)".
idtac " ".

idtac "Entering exercise gen_dep_practice (standard): 3 points".
idtac " ".

idtac "#> nth_error_after_last".
check_type @nth_error_after_last (forall (n : nat) (X : Type) (l : list X), length l = n -> nth_error l n = None).
idtac "Assumptions:".
Abort.
Print Assumptions nth_error_after_last.
Goal True.
idtac " ".

idtac "Exiting exercise (gen_dep_practice)".
idtac " ".

idtac "Entering exercise destruct_eqn_practice (standard): 2 points".
idtac " ".

idtac "#> bool_fn_applied_thrice".
check_type @bool_fn_applied_thrice (forall (f : bool -> bool) (b : bool), f(f(f b)) = f b).
idtac "Assumptions:".
Abort.
Print Assumptions bool_fn_applied_thrice.
Goal True.
idtac " ".

idtac "Exiting exercise (destruct_eqn_practice)".
idtac " ".

idtac "Entering exercise beq_nat_sym (standard): 3 points".
idtac " ".

idtac "#> beq_nat_sym".
check_type @beq_nat_sym (forall (n m : nat), beq_nat n m = beq_nat m n).
idtac "Assumptions:".
Abort.
Print Assumptions beq_nat_sym.
Goal True.
idtac " ".

idtac "Exiting exercise (beq_nat_sym)".
idtac " ".

idtac "Entering exercise split_combine (advanced): 3 points".
idtac " ".

idtac "Manually graded.".
idtac " ".

idtac "Exiting exercise (split_combine)".
idtac " ".

idtac "Entering exercise filter_exercise (advanced): 3 points".
idtac " ".

idtac "#> filter_exercise".
check_type @filter_exercise (forall (X : Type) (test : X -> bool) (x : X) (l lf : list X), filter test l = x :: lf -> test x = true).
idtac "Assumptions:".
Abort.
Print Assumptions filter_exercise.
Goal True.
idtac " ".

idtac "Exiting exercise (filter_exercise)".
idtac " ".

idtac "Entering exercise forall_exists_challenge (advanced): 4 points".
idtac " ".

idtac "Exiting exercise (forall_exists_challenge)".
idtac " ".

idtac "Max points - regular: 18".
idtac "Max points - advanced: 30".
Abort.
