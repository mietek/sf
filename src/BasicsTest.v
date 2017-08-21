Require Import Basics.
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

Require Import Basics.
Import Check.

Goal True.
idtac "Entering exercise nandb (standard): 1 point".
idtac " ".

idtac "#> nandb".
check_type @nandb (forall (b1 : bool) (b2 : bool), bool).
idtac "Assumptions:".
Abort.
Print Assumptions nandb.
Goal True.
idtac " ".

idtac "#> test_nandb1".
check_type @test_nandb1 ((nandb true false) = true).
idtac "Assumptions:".
Abort.
Print Assumptions test_nandb1.
Goal True.
idtac " ".

idtac "#> test_nandb2".
check_type @test_nandb2 ((nandb false false) = true).
idtac "Assumptions:".
Abort.
Print Assumptions test_nandb2.
Goal True.
idtac " ".

idtac "#> test_nandb3".
check_type @test_nandb3 ((nandb false true) = true).
idtac "Assumptions:".
Abort.
Print Assumptions test_nandb3.
Goal True.
idtac " ".

idtac "#> test_nandb4".
check_type @test_nandb4 ((nandb true true) = false).
idtac "Assumptions:".
Abort.
Print Assumptions test_nandb4.
Goal True.
idtac " ".

idtac "Exiting exercise (nandb)".
idtac " ".

idtac "Entering exercise andb3 (standard): 1 point".
idtac " ".

idtac "#> andb3".
check_type @andb3 (forall (b1 : bool) (b2 : bool) (b3 : bool), bool).
idtac "Assumptions:".
Abort.
Print Assumptions andb3.
Goal True.
idtac " ".

idtac "#> test_andb31".
check_type @test_andb31 ((andb3 true true true) = true).
idtac "Assumptions:".
Abort.
Print Assumptions test_andb31.
Goal True.
idtac " ".

idtac "#> test_andb32".
check_type @test_andb32 ((andb3 false true true) = false).
idtac "Assumptions:".
Abort.
Print Assumptions test_andb32.
Goal True.
idtac " ".

idtac "#> test_andb33".
check_type @test_andb33 ((andb3 true false true) = false).
idtac "Assumptions:".
Abort.
Print Assumptions test_andb33.
Goal True.
idtac " ".

idtac "#> test_andb34".
check_type @test_andb34 ((andb3 true true false) = false).
idtac "Assumptions:".
Abort.
Print Assumptions test_andb34.
Goal True.
idtac " ".

idtac "Exiting exercise (andb3)".
idtac " ".
Abort.

Module TestNatPlayground.
Import NatPlayground.
End TestNatPlayground.
Module TestNatPlayground2.
Import NatPlayground2.
End TestNatPlayground2.
Goal True.
idtac "Entering exercise factorial (standard): 1 point".
idtac " ".

idtac "#> factorial".
check_type @factorial (forall (n : nat), nat).
idtac "Assumptions:".
Abort.
Print Assumptions factorial.
Goal True.
idtac " ".

idtac "#> test_factorial1".
check_type @test_factorial1 ((factorial 3) = 6).
idtac "Assumptions:".
Abort.
Print Assumptions test_factorial1.
Goal True.
idtac " ".

idtac "#> test_factorial2".
check_type @test_factorial2 ((factorial 5) = (mult 10 12)).
idtac "Assumptions:".
Abort.
Print Assumptions test_factorial2.
Goal True.
idtac " ".

idtac "Exiting exercise (factorial)".
idtac " ".

idtac "Entering exercise blt_nat (standard): 1 point".
idtac " ".

idtac "#> blt_nat".
check_type @blt_nat (forall (n m : nat), bool).
idtac "Assumptions:".
Abort.
Print Assumptions blt_nat.
Goal True.
idtac " ".

idtac "#> test_blt_nat1".
check_type @test_blt_nat1 ((blt_nat 2 2) = false).
idtac "Assumptions:".
Abort.
Print Assumptions test_blt_nat1.
Goal True.
idtac " ".

idtac "#> test_blt_nat2".
check_type @test_blt_nat2 ((blt_nat 2 4) = true).
idtac "Assumptions:".
Abort.
Print Assumptions test_blt_nat2.
Goal True.
idtac " ".

idtac "#> test_blt_nat3".
check_type @test_blt_nat3 ((blt_nat 4 2) = false).
idtac "Assumptions:".
Abort.
Print Assumptions test_blt_nat3.
Goal True.
idtac " ".

idtac "Exiting exercise (blt_nat)".
idtac " ".

idtac "Entering exercise plus_id_exercise (standard): 1 point".
idtac " ".

idtac "#> plus_id_exercise".
check_type @plus_id_exercise (forall n m o, n = m -> m = o -> n + m = m + o).
idtac "Assumptions:".
Abort.
Print Assumptions plus_id_exercise.
Goal True.
idtac " ".

idtac "Exiting exercise (plus_id_exercise)".
idtac " ".

idtac "Entering exercise mult_S_1 (standard): 2 points".
idtac " ".

idtac "#> mult_S_1".
check_type @mult_S_1 (forall n m, m = S n -> m *(1 + n) = m * m).
idtac "Assumptions:".
Abort.
Print Assumptions mult_S_1.
Goal True.
idtac " ".

idtac "Exiting exercise (mult_S_1)".
idtac " ".

idtac "Entering exercise andb_true_elim2 (standard): 2 points".
idtac " ".

idtac "#> andb_true_elim2".
check_type @andb_true_elim2 (forall b c, andb b c = true -> c = true).
idtac "Assumptions:".
Abort.
Print Assumptions andb_true_elim2.
Goal True.
idtac " ".

idtac "Exiting exercise (andb_true_elim2)".
idtac " ".

idtac "Entering exercise zero_nbeq_plus_1 (standard): 1 point".
idtac " ".

idtac "#> zero_nbeq_plus_1".
check_type @zero_nbeq_plus_1 (forall n, beq_nat 0(n + 1) = false).
idtac "Assumptions:".
Abort.
Print Assumptions zero_nbeq_plus_1.
Goal True.
idtac " ".

idtac "Exiting exercise (zero_nbeq_plus_1)".
idtac " ".

idtac "Entering exercise boolean_functions (standard): 2 points".
idtac " ".

idtac "Manually graded.".
idtac " ".

idtac "Exiting exercise (boolean_functions)".
idtac " ".

idtac "Entering exercise andb_eq_orb (standard): 2 points".
idtac " ".

idtac "#> andb_eq_orb".
check_type @andb_eq_orb (forall (b c : bool), (andb b c = orb b c) -> b = c).
idtac "Assumptions:".
Abort.
Print Assumptions andb_eq_orb.
Goal True.
idtac " ".

idtac "Exiting exercise (andb_eq_orb)".
idtac " ".

idtac "Entering exercise binary (standard): 3 points".
idtac " ".

idtac "Manually graded.".
idtac " ".

idtac "Exiting exercise (binary)".
idtac " ".

idtac "Max points - regular: 17".
idtac "Max points - advanced: 17".
Abort.
