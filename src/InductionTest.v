Require Import Induction.
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

Require Import Induction.
Import Check.

Require Export Basics.
Goal True.
idtac "Entering exercise basic_induction (standard): 2 points".
idtac " ".

idtac "#> mult_0_r".
check_type @mult_0_r (forall n, n * 0 = 0).
idtac "Assumptions:".
Abort.
Print Assumptions mult_0_r.
Goal True.
idtac " ".

idtac "#> plus_n_Sm".
check_type @plus_n_Sm (forall n m, S(n + m) = n +(S m)).
idtac "Assumptions:".
Abort.
Print Assumptions plus_n_Sm.
Goal True.
idtac " ".

idtac "#> plus_comm".
check_type @plus_comm (forall n m, n + m = m + n).
idtac "Assumptions:".
Abort.
Print Assumptions plus_comm.
Goal True.
idtac " ".

idtac "#> plus_assoc".
check_type @plus_assoc (forall n m p, n +(m + p) = (n + m)+ p).
idtac "Assumptions:".
Abort.
Print Assumptions plus_assoc.
Goal True.
idtac " ".

idtac "Exiting exercise (basic_induction)".
idtac " ".

idtac "Entering exercise double_plus (standard): 2 points".
idtac " ".

idtac "#> double_plus".
check_type @double_plus (forall n, double n = n + n).
idtac "Assumptions:".
Abort.
Print Assumptions double_plus.
Goal True.
idtac " ".

idtac "Exiting exercise (double_plus)".
idtac " ".

idtac "Entering exercise destruct_induction (standard): 1 point".
idtac " ".

idtac "Manually graded.".
idtac " ".

idtac "Exiting exercise (destruct_induction)".
idtac " ".

idtac "Entering exercise plus_comm_informal (advanced): 2 points".
idtac " ".

idtac "Manually graded.".
idtac " ".

idtac "Exiting exercise (plus_comm_informal)".
idtac " ".

idtac "Entering exercise mult_comm (standard): 3 points".
idtac " ".

idtac "#> plus_swap".
check_type @plus_swap (forall n m p, n +(m + p) = m +(n + p)).
idtac "Assumptions:".
Abort.
Print Assumptions plus_swap.
Goal True.
idtac " ".

idtac "#> mult_comm".
check_type @mult_comm (forall m n, m * n = n * m).
idtac "Assumptions:".
Abort.
Print Assumptions mult_comm.
Goal True.
idtac " ".

idtac "Exiting exercise (mult_comm)".
idtac " ".

idtac "Entering exercise binary_commute (standard): 3 points".
idtac " ".

idtac "Manually graded.".
idtac " ".

idtac "Exiting exercise (binary_commute)".
idtac " ".

idtac "Entering exercise binary_inverse (advanced): 5 points".
idtac " ".

idtac "Manually graded.".
idtac " ".

idtac "Exiting exercise (binary_inverse)".
idtac " ".

idtac "Max points - regular: 11".
idtac "Max points - advanced: 18".
Abort.
