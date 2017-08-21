Require Import Logic.
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

Require Import Logic.
Import Check.

Require Export Tactics.
Goal True.
idtac "Entering exercise and_exercise (standard): 2 points".
idtac " ".

idtac "#> and_exercise".
check_type @and_exercise (forall n m, n + m = 0 -> n = 0 /\ m = 0).
idtac "Assumptions:".
Abort.
Print Assumptions and_exercise.
Goal True.
idtac " ".

idtac "Exiting exercise (and_exercise)".
idtac " ".

idtac "Entering exercise and_assoc (standard): 2 points".
idtac " ".

idtac "#> and_assoc".
check_type @and_assoc (forall P Q R, P /\ (Q /\ R) -> (P /\ Q) /\ R).
idtac "Assumptions:".
Abort.
Print Assumptions and_assoc.
Goal True.
idtac " ".

idtac "Exiting exercise (and_assoc)".
idtac " ".

idtac "Entering exercise mult_eq_0 (standard): 1 point".
idtac " ".

idtac "#> mult_eq_0".
check_type @mult_eq_0 (forall n m, n * m = 0 -> n = 0 \/ m = 0).
idtac "Assumptions:".
Abort.
Print Assumptions mult_eq_0.
Goal True.
idtac " ".

idtac "Exiting exercise (mult_eq_0)".
idtac " ".

idtac "Entering exercise or_commut (standard): 1 point".
idtac " ".

idtac "#> or_commut".
check_type @or_commut (forall P Q, P \/ Q -> Q \/ P).
idtac "Assumptions:".
Abort.
Print Assumptions or_commut.
Goal True.
idtac " ".

idtac "Exiting exercise (or_commut)".
idtac " ".
Abort.

Module TestMyNot.
Import MyNot.
End TestMyNot.
Goal True.
idtac "Entering exercise double_neg_inf (advanced): 2 points".
idtac " ".

idtac "Manually graded.".
idtac " ".

idtac "Exiting exercise (double_neg_inf)".
idtac " ".

idtac "Entering exercise contrapositive (standard): 2 points".
idtac " ".

idtac "#> contrapositive".
check_type @contrapositive (forall (P Q : Prop), (P -> Q) -> (~ Q -> ~ P)).
idtac "Assumptions:".
Abort.
Print Assumptions contrapositive.
Goal True.
idtac " ".

idtac "Exiting exercise (contrapositive)".
idtac " ".

idtac "Entering exercise not_both_true_and_false (standard): 1 point".
idtac " ".

idtac "#> not_both_true_and_false".
check_type @not_both_true_and_false (forall P, ~ (P /\ ~ P)).
idtac "Assumptions:".
Abort.
Print Assumptions not_both_true_and_false.
Goal True.
idtac " ".

idtac "Exiting exercise (not_both_true_and_false)".
idtac " ".

idtac "Entering exercise informal_not_PNP (advanced): 1 point".
idtac " ".

idtac "Manually graded.".
idtac " ".

idtac "Exiting exercise (informal_not_PNP)".
idtac " ".
Abort.

Module TestMyIff.
Import MyIff.
End TestMyIff.
Goal True.
idtac "Entering exercise or_distributes_over_and (standard): 3 points".
idtac " ".

idtac "#> or_distributes_over_and".
check_type @or_distributes_over_and (forall P Q R, P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R)).
idtac "Assumptions:".
Abort.
Print Assumptions or_distributes_over_and.
Goal True.
idtac " ".

idtac "Exiting exercise (or_distributes_over_and)".
idtac " ".
Abort.

Require Import Coq.Setoids.Setoid.
Goal True.
idtac "Entering exercise dist_not_exists (standard): 1 point".
idtac " ".

idtac "#> dist_not_exists".
check_type @dist_not_exists (forall (X : Type) (P : X -> Prop), (forall x, P x) -> ~ (exists x, ~ P x)).
idtac "Assumptions:".
Abort.
Print Assumptions dist_not_exists.
Goal True.
idtac " ".

idtac "Exiting exercise (dist_not_exists)".
idtac " ".

idtac "Entering exercise dist_exists_or (standard): 2 points".
idtac " ".

idtac "#> dist_exists_or".
check_type @dist_exists_or (forall (X : Type) (P Q : X -> Prop), (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x)).
idtac "Assumptions:".
Abort.
Print Assumptions dist_exists_or.
Goal True.
idtac " ".

idtac "Exiting exercise (dist_exists_or)".
idtac " ".

idtac "Entering exercise In_map_iff (standard): 2 points".
idtac " ".

idtac "#> In_map_iff".
check_type @In_map_iff (forall (A B : Type) (f : A -> B) (l : list A) (y : B), In y(map f l) <-> exists x, f x = y /\ In x l).
idtac "Assumptions:".
Abort.
Print Assumptions In_map_iff.
Goal True.
idtac " ".

idtac "Exiting exercise (In_map_iff)".
idtac " ".

idtac "Entering exercise in_app_iff (standard): 2 points".
idtac " ".

idtac "#> in_app_iff".
check_type @in_app_iff (forall A l l' (a : A), In a(l ++ l') <-> In a l \/ In a l').
idtac "Assumptions:".
Abort.
Print Assumptions in_app_iff.
Goal True.
idtac " ".

idtac "Exiting exercise (in_app_iff)".
idtac " ".

idtac "Entering exercise All (standard): 3 points".
idtac " ".

idtac "#> All".
check_type @All (forall {T : Type} (P : T -> Prop) (l : list T), Prop).
idtac "Assumptions:".
Abort.
Print Assumptions All.
Goal True.
idtac " ".

idtac "#> All_In".
check_type @All_In (forall T (P : T -> Prop) (l : list T), (forall x, In x l -> P x) <-> All P l).
idtac "Assumptions:".
Abort.
Print Assumptions All_In.
Goal True.
idtac " ".

idtac "Exiting exercise (All)".
idtac " ".

idtac "Entering exercise combine_odd_even (standard): 3 points".
idtac " ".

idtac "#> combine_odd_even".
check_type @combine_odd_even (forall (Podd Peven : nat -> Prop), nat -> Prop).
idtac "Assumptions:".
Abort.
Print Assumptions combine_odd_even.
Goal True.
idtac " ".

idtac "#> combine_odd_even_intro".
check_type @combine_odd_even_intro (forall (Podd Peven : nat -> Prop) (n : nat), (oddb n = true -> Podd n) -> (oddb n = false -> Peven n) -> combine_odd_even Podd Peven n).
idtac "Assumptions:".
Abort.
Print Assumptions combine_odd_even_intro.
Goal True.
idtac " ".

idtac "#> combine_odd_even_elim_odd".
check_type @combine_odd_even_elim_odd (forall (Podd Peven : nat -> Prop) (n : nat), combine_odd_even Podd Peven n -> oddb n = true -> Podd n).
idtac "Assumptions:".
Abort.
Print Assumptions combine_odd_even_elim_odd.
Goal True.
idtac " ".

idtac "#> combine_odd_even_elim_even".
check_type @combine_odd_even_elim_even (forall (Podd Peven : nat -> Prop) (n : nat), combine_odd_even Podd Peven n -> oddb n = false -> Peven n).
idtac "Assumptions:".
Abort.
Print Assumptions combine_odd_even_elim_even.
Goal True.
idtac " ".

idtac "Exiting exercise (combine_odd_even)".
idtac " ".

idtac "Entering exercise tr_rev (standard): 4 points".
idtac " ".

idtac "#> tr_rev_correct".
check_type @tr_rev_correct (forall X, @tr_rev X = @rev X).
idtac "Assumptions:".
Abort.
Print Assumptions tr_rev_correct.
Goal True.
idtac " ".

idtac "Exiting exercise (tr_rev)".
idtac " ".

idtac "Entering exercise evenb_double_conv (standard): 3 points".
idtac " ".

idtac "#> evenb_double_conv".
check_type @evenb_double_conv (forall n, exists k, n = if evenb n then double k else S(double k)).
idtac "Assumptions:".
Abort.
Print Assumptions evenb_double_conv.
Goal True.
idtac " ".

idtac "Exiting exercise (evenb_double_conv)".
idtac " ".

idtac "Entering exercise logical_connectives (standard): 2 points".
idtac " ".

idtac "#> andb_true_iff".
check_type @andb_true_iff (forall b1 b2, b1 && b2 = true <-> b1 = true /\ b2 = true).
idtac "Assumptions:".
Abort.
Print Assumptions andb_true_iff.
Goal True.
idtac " ".

idtac "#> orb_true_iff".
check_type @orb_true_iff (forall b1 b2, b1 || b2 = true <-> b1 = true \/ b2 = true).
idtac "Assumptions:".
Abort.
Print Assumptions orb_true_iff.
Goal True.
idtac " ".

idtac "Exiting exercise (logical_connectives)".
idtac " ".

idtac "Entering exercise beq_nat_false_iff (standard): 1 point".
idtac " ".

idtac "#> beq_nat_false_iff".
check_type @beq_nat_false_iff (forall x y, beq_nat x y = false <-> x <> y).
idtac "Assumptions:".
Abort.
Print Assumptions beq_nat_false_iff.
Goal True.
idtac " ".

idtac "Exiting exercise (beq_nat_false_iff)".
idtac " ".

idtac "Entering exercise beq_list (standard): 3 points".
idtac " ".

idtac "#> beq_list".
check_type @beq_list (forall {A : Type} (beq : A -> A -> bool) (l1 l2 : list A), bool).
idtac "Assumptions:".
Abort.
Print Assumptions beq_list.
Goal True.
idtac " ".

idtac "#> beq_list_true_iff".
check_type @beq_list_true_iff (forall A (beq : A -> A -> bool), (forall a1 a2, beq a1 a2 = true <-> a1 = a2) -> forall l1 l2, beq_list beq l1 l2 = true <-> l1 = l2).
idtac "Assumptions:".
Abort.
Print Assumptions beq_list_true_iff.
Goal True.
idtac " ".

idtac "Exiting exercise (beq_list)".
idtac " ".

idtac "Entering exercise All_forallb (standard): 2 points".
idtac " ".

idtac "#> forallb_true_iff".
check_type @forallb_true_iff (forall X test (l : list X), forallb test l = true <-> All(fun x => test x = true)l).
idtac "Assumptions:".
Abort.
Print Assumptions forallb_true_iff.
Goal True.
idtac " ".

idtac "Exiting exercise (All_forallb)".
idtac " ".

idtac "Entering exercise excluded_middle_irrefutable (standard): 3 points".
idtac " ".

idtac "#> excluded_middle_irrefutable".
check_type @excluded_middle_irrefutable (forall (P : Prop), ~ ~ (P \/ ~ P)).
idtac "Assumptions:".
Abort.
Print Assumptions excluded_middle_irrefutable.
Goal True.
idtac " ".

idtac "Exiting exercise (excluded_middle_irrefutable)".
idtac " ".

idtac "Entering exercise not_exists_dist (advanced): 3 points".
idtac " ".

idtac "#> not_exists_dist".
check_type @not_exists_dist (excluded_middle -> forall (X : Type) (P : X -> Prop), ~ (exists x, ~ P x) -> (forall x, P x)).
idtac "Assumptions:".
Abort.
Print Assumptions not_exists_dist.
Goal True.
idtac " ".

idtac "Exiting exercise (not_exists_dist)".
idtac " ".

idtac "Max points - regular: 43".
idtac "Max points - advanced: 49".
Abort.
