Require Import Poly.
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

Require Import Poly.
Import Check.

Require Export Lists.
Module TestMumbleGrumble.
Import MumbleGrumble.
Goal True.
idtac "Entering exercise mumble_grumble (standard): 2 points".
Abort.
Import MumbleGrumble.
Goal True.
idtac " ".

idtac "Manually graded.".
idtac " ".

idtac "Exiting exercise (mumble_grumble)".
idtac " ".
Abort.

End TestMumbleGrumble.
Goal True.
idtac "Entering exercise split (standard): 2 points".
idtac " ".

idtac "#> split".
check_type @split (forall {X Y : Type} (l : list(X * Y)), (list X)*(list Y)).
idtac "Assumptions:".
Abort.
Print Assumptions split.
Goal True.
idtac " ".

idtac "#> test_split".
check_type @test_split (split[(1, false);(2, false)] = ([1 ; 2], [false ; false])).
idtac "Assumptions:".
Abort.
Print Assumptions test_split.
Goal True.
idtac " ".

idtac "Exiting exercise (split)".
idtac " ".

idtac "Entering exercise filter_even_gt7 (standard): 2 points".
idtac " ".

idtac "#> filter_even_gt7".
check_type @filter_even_gt7 (forall (l : list nat), list nat).
idtac "Assumptions:".
Abort.
Print Assumptions filter_even_gt7.
Goal True.
idtac " ".

idtac "#> test_filter_even_gt7_1".
check_type @test_filter_even_gt7_1 (filter_even_gt7[1 ; 2 ; 6 ; 9 ; 10 ; 3 ; 12 ; 8] = [10 ; 12 ; 8]).
idtac "Assumptions:".
Abort.
Print Assumptions test_filter_even_gt7_1.
Goal True.
idtac " ".

idtac "#> test_filter_even_gt7_2".
check_type @test_filter_even_gt7_2 (filter_even_gt7[5 ; 2 ; 6 ; 19 ; 129] = []).
idtac "Assumptions:".
Abort.
Print Assumptions test_filter_even_gt7_2.
Goal True.
idtac " ".

idtac "Exiting exercise (filter_even_gt7)".
idtac " ".

idtac "Entering exercise partition (standard): 3 points".
idtac " ".

idtac "#> partition".
check_type @partition (forall {X : Type} (test : X -> bool) (l : list X), list X * list X).
idtac "Assumptions:".
Abort.
Print Assumptions partition.
Goal True.
idtac " ".

idtac "#> test_partition1".
check_type @test_partition1 (partition oddb[1 ; 2 ; 3 ; 4 ; 5] = ([1 ; 3 ; 5], [2 ; 4])).
idtac "Assumptions:".
Abort.
Print Assumptions test_partition1.
Goal True.
idtac " ".

idtac "#> test_partition2".
check_type @test_partition2 (partition(fun x => false)[5 ; 9 ; 0] = ([], [5 ; 9 ; 0])).
idtac "Assumptions:".
Abort.
Print Assumptions test_partition2.
Goal True.
idtac " ".

idtac "Exiting exercise (partition)".
idtac " ".

idtac "Entering exercise map_rev (standard): 3 points".
idtac " ".

idtac "#> map_rev".
check_type @map_rev (forall (X Y : Type) (f : X -> Y) (l : list X), map f(rev l) = rev(map f l)).
idtac "Assumptions:".
Abort.
Print Assumptions map_rev.
Goal True.
idtac " ".

idtac "Exiting exercise (map_rev)".
idtac " ".

idtac "Entering exercise flat_map (standard): 2 points".
idtac " ".

idtac "#> flat_map".
check_type @flat_map (forall {X Y : Type} (f : X -> list Y) (l : list X), (list Y)).
idtac "Assumptions:".
Abort.
Print Assumptions flat_map.
Goal True.
idtac " ".

idtac "#> test_flat_map1".
check_type @test_flat_map1 (flat_map(fun n => [n ; n ; n])[1 ; 5 ; 4] = [1 ; 1 ; 1 ; 5 ; 5 ; 5 ; 4 ; 4 ; 4]).
idtac "Assumptions:".
Abort.
Print Assumptions test_flat_map1.
Goal True.
idtac " ".

idtac "Exiting exercise (flat_map)".
idtac " ".

idtac "Entering exercise fold_types_different (advanced): 1 point".
idtac " ".

idtac "Manually graded.".
idtac " ".

idtac "Exiting exercise (fold_types_different)".
idtac " ".
Abort.

Module TestExercises.
Import Exercises.
Goal True.
idtac "Entering exercise fold_length (standard): 2 points".
Abort.
Import Exercises.
Goal True.
idtac " ".

idtac "#> Exercises.fold_length_correct".
check_type @Exercises.fold_length_correct (forall X (l : list X), fold_length l = length l).
idtac "Assumptions:".
Abort.
Print Assumptions Exercises.fold_length_correct.
Goal True.
idtac " ".

idtac "Exiting exercise (fold_length)".
idtac " ".

idtac "Entering exercise fold_map (standard): 3 points".
Abort.
Import Exercises.
Goal True.
idtac " ".

idtac "Manually graded.".
idtac " ".

idtac "Exiting exercise (fold_map)".
idtac " ".

idtac "Entering exercise currying (advanced): 2 points".
Abort.
Import Exercises.
Goal True.
idtac " ".

idtac "#> Exercises.prod_uncurry".
check_type @Exercises.prod_uncurry (forall {X Y Z : Type} (f : X -> Y -> Z) (p : X * Y), Z).
idtac "Assumptions:".
Abort.
Print Assumptions Exercises.prod_uncurry.
Goal True.
idtac " ".

idtac "#> Exercises.uncurry_curry".
check_type @Exercises.uncurry_curry (forall (X Y Z : Type) (f : X -> Y -> Z) x y, prod_curry(prod_uncurry f)x y = f x y).
idtac "Assumptions:".
Abort.
Print Assumptions Exercises.uncurry_curry.
Goal True.
idtac " ".

idtac "#> Exercises.curry_uncurry".
check_type @Exercises.curry_uncurry (forall (X Y Z : Type) (f : (X * Y) -> Z) (p : X * Y), prod_uncurry(prod_curry f)p = f p).
idtac "Assumptions:".
Abort.
Print Assumptions Exercises.curry_uncurry.
Goal True.
idtac " ".

idtac "Exiting exercise (currying)".
idtac " ".

idtac "Entering exercise nth_error_informal (advanced): 2 points".
Abort.
Import Exercises.
Goal True.
idtac " ".

idtac "Manually graded.".
idtac " ".

idtac "Exiting exercise (nth_error_informal)".
idtac " ".

idtac "Entering exercise church_numerals (advanced): 4 points".
Abort.
Import Exercises.
Goal True.
idtac " ".
Abort.

Module TestChurch.
Import Church.
Goal True.
idtac "#> Exercises.Church.succ".
check_type @Exercises.Church.succ (forall (n : nat), nat).
idtac "Assumptions:".
Abort.
Print Assumptions Exercises.Church.succ.
Goal True.
idtac " ".

idtac "#> Exercises.Church.succ_1".
check_type @Exercises.Church.succ_1 (succ zero = one).
idtac "Assumptions:".
Abort.
Print Assumptions Exercises.Church.succ_1.
Goal True.
idtac " ".

idtac "#> Exercises.Church.succ_2".
check_type @Exercises.Church.succ_2 (succ one = two).
idtac "Assumptions:".
Abort.
Print Assumptions Exercises.Church.succ_2.
Goal True.
idtac " ".

idtac "#> Exercises.Church.succ_3".
check_type @Exercises.Church.succ_3 (succ two = three).
idtac "Assumptions:".
Abort.
Print Assumptions Exercises.Church.succ_3.
Goal True.
idtac " ".

idtac "#> Exercises.Church.plus".
check_type @Exercises.Church.plus (forall (n m : nat), nat).
idtac "Assumptions:".
Abort.
Print Assumptions Exercises.Church.plus.
Goal True.
idtac " ".

idtac "#> Exercises.Church.plus_1".
check_type @Exercises.Church.plus_1 (plus zero one = one).
idtac "Assumptions:".
Abort.
Print Assumptions Exercises.Church.plus_1.
Goal True.
idtac " ".

idtac "#> Exercises.Church.plus_2".
check_type @Exercises.Church.plus_2 (plus two three = plus three two).
idtac "Assumptions:".
Abort.
Print Assumptions Exercises.Church.plus_2.
Goal True.
idtac " ".

idtac "#> Exercises.Church.plus_3".
check_type @Exercises.Church.plus_3 (plus(plus two two)three = plus one(plus three three)).
idtac "Assumptions:".
Abort.
Print Assumptions Exercises.Church.plus_3.
Goal True.
idtac " ".

idtac "#> Exercises.Church.mult".
check_type @Exercises.Church.mult (forall (n m : nat), nat).
idtac "Assumptions:".
Abort.
Print Assumptions Exercises.Church.mult.
Goal True.
idtac " ".

idtac "#> Exercises.Church.mult_1".
check_type @Exercises.Church.mult_1 (mult one one = one).
idtac "Assumptions:".
Abort.
Print Assumptions Exercises.Church.mult_1.
Goal True.
idtac " ".

idtac "#> Exercises.Church.mult_2".
check_type @Exercises.Church.mult_2 (mult zero(plus three three) = zero).
idtac "Assumptions:".
Abort.
Print Assumptions Exercises.Church.mult_2.
Goal True.
idtac " ".

idtac "#> Exercises.Church.mult_3".
check_type @Exercises.Church.mult_3 (mult two three = plus three three).
idtac "Assumptions:".
Abort.
Print Assumptions Exercises.Church.mult_3.
Goal True.
idtac " ".

idtac "#> Exercises.Church.exp".
check_type @Exercises.Church.exp (forall (n m : nat), nat).
idtac "Assumptions:".
Abort.
Print Assumptions Exercises.Church.exp.
Goal True.
idtac " ".

idtac "#> Exercises.Church.exp_1".
check_type @Exercises.Church.exp_1 (exp two two = plus two two).
idtac "Assumptions:".
Abort.
Print Assumptions Exercises.Church.exp_1.
Goal True.
idtac " ".

idtac "#> Exercises.Church.exp_2".
check_type @Exercises.Church.exp_2 (exp three two = plus(mult two(mult two two))one).
idtac "Assumptions:".
Abort.
Print Assumptions Exercises.Church.exp_2.
Goal True.
idtac " ".

idtac "#> Exercises.Church.exp_3".
check_type @Exercises.Church.exp_3 (exp three zero = one).
idtac "Assumptions:".
Abort.
Print Assumptions Exercises.Church.exp_3.
Goal True.
idtac " ".
Abort.

End TestChurch.
Goal True.
idtac "Exiting exercise (church_numerals)".
idtac " ".
Abort.

End TestExercises.
Goal True.
idtac "Max points - regular: 19".
idtac "Max points - advanced: 28".
Abort.
