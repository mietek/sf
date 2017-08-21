Require Import Hoare2.
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

Require Import Hoare2.
Import Check.

Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Maps.
Require Import Imp.
Require Import Hoare.
Goal True.
idtac "Entering exercise if_minus_plus_reloaded (standard): 2 points".
idtac " ".

idtac "Manually graded.".
idtac " ".

idtac "Exiting exercise (if_minus_plus_reloaded)".
idtac " ".

idtac "Entering exercise slow_assignment (standard): 2 points".
idtac " ".

idtac "Manually graded.".
idtac " ".

idtac "Exiting exercise (slow_assignment)".
idtac " ".

idtac "Entering exercise factorial (standard): 3 points".
idtac " ".

idtac "Manually graded.".
idtac " ".

idtac "Exiting exercise (factorial)".
idtac " ".

idtac "Entering exercise Min_Hoare (standard): 3 points".
idtac " ".

idtac "Manually graded.".
idtac " ".

idtac "Exiting exercise (Min_Hoare)".
idtac " ".

idtac "Entering exercise two_loops (standard): 3 points".
idtac " ".

idtac "Manually graded.".
idtac " ".

idtac "Exiting exercise (two_loops)".
idtac " ".

idtac "Entering exercise slow_assignment_dec (advanced): 3 points".
idtac " ".

idtac "#> slow_assignment_dec".
check_type @slow_assignment_dec (forall (m : nat), decorated).
idtac "Assumptions:".
Abort.
Print Assumptions slow_assignment_dec.
Goal True.
idtac " ".

idtac "#> slow_assignment_dec_correct".
check_type @slow_assignment_dec_correct (forall m, dec_correct(slow_assignment_dec m)).
idtac "Assumptions:".
Abort.
Print Assumptions slow_assignment_dec_correct.
Goal True.
idtac " ".

idtac "Exiting exercise (slow_assignment_dec)".
idtac " ".

idtac "Entering exercise factorial_dec (advanced): 4 points".
idtac " ".

idtac "Manually graded.".
idtac " ".

idtac "Exiting exercise (factorial_dec)".
idtac " ".

idtac "Max points - regular: 13".
idtac "Max points - advanced: 20".
Abort.
