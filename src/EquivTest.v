Require Import Equiv.
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

Require Import Equiv.
Import Check.

Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.
Import ListNotations.
Require Import Maps.
Require Import Imp.
Goal True.
idtac "Entering exercise skip_right (standard): 2 points".
idtac " ".

idtac "#> skip_right".
check_type @skip_right (forall c, cequiv(c ;; SKIP)c).
idtac "Assumptions:".
Abort.
Print Assumptions skip_right.
Goal True.
idtac " ".

idtac "Exiting exercise (skip_right)".
idtac " ".

idtac "Entering exercise swap_if_branches (standard): 3 points".
idtac " ".

idtac "#> swap_if_branches".
check_type @swap_if_branches (forall b e1 e2, cequiv(IFB b THEN e1 ELSE e2 FI)(IFB BNot b THEN e2 ELSE e1 FI)).
idtac "Assumptions:".
Abort.
Print Assumptions swap_if_branches.
Goal True.
idtac " ".

idtac "Exiting exercise (swap_if_branches)".
idtac " ".

idtac "Entering exercise assign_aequiv (standard): 2 points".
idtac " ".

idtac "#> assign_aequiv".
check_type @assign_aequiv (forall X e, aequiv(AId X)e -> cequiv SKIP(X ::= e)).
idtac "Assumptions:".
Abort.
Print Assumptions assign_aequiv.
Goal True.
idtac " ".

idtac "Exiting exercise (assign_aequiv)".
idtac " ".

idtac "Entering exercise equiv_classes (standard): 2 points".
idtac " ".

idtac "#> equiv_classes".
check_type @equiv_classes (list(list com)).
idtac "Assumptions:".
Abort.
Print Assumptions equiv_classes.
Goal True.
idtac " ".

idtac "Exiting exercise (equiv_classes)".
idtac " ".

idtac "Entering exercise fold_constants_com_sound (standard): 3 points".
idtac " ".

idtac "#> fold_constants_com_sound".
check_type @fold_constants_com_sound (ctrans_sound fold_constants_com).
idtac "Assumptions:".
Abort.
Print Assumptions fold_constants_com_sound.
Goal True.
idtac " ".

idtac "Exiting exercise (fold_constants_com_sound)".
idtac " ".

idtac "Entering exercise inequiv_exercise (standard): 3 points".
idtac " ".

idtac "#> inequiv_exercise".
check_type @inequiv_exercise (~ cequiv(WHILE BTrue DO SKIP END)SKIP).
idtac "Assumptions:".
Abort.
Print Assumptions inequiv_exercise.
Goal True.
idtac " ".

idtac "Exiting exercise (inequiv_exercise)".
idtac " ".
Abort.

Module TestHimp.
Import Himp.
Goal True.
idtac "Entering exercise himp_ceval (standard): 2 points".
Abort.
Import Himp.
Goal True.
idtac " ".

idtac "#> Himp.havoc_example1".
check_type @Himp.havoc_example1 ((HAVOC X)/ empty_state \\ t_update empty_state X 0).
idtac "Assumptions:".
Abort.
Print Assumptions Himp.havoc_example1.
Goal True.
idtac " ".

idtac "#> Himp.havoc_example2".
check_type @Himp.havoc_example2 ((SKIP ;; HAVOC Z)/ empty_state \\ t_update empty_state Z 42).
idtac "Assumptions:".
Abort.
Print Assumptions Himp.havoc_example2.
Goal True.
idtac " ".

idtac "Exiting exercise (himp_ceval)".
idtac " ".

idtac "Entering exercise havoc_swap (standard): 3 points".
Abort.
Import Himp.
Goal True.
idtac " ".

idtac "#> Himp.pXY_cequiv_pYX".
check_type @Himp.pXY_cequiv_pYX (cequiv pXY pYX \/ ~ cequiv pXY pYX).
idtac "Assumptions:".
Abort.
Print Assumptions Himp.pXY_cequiv_pYX.
Goal True.
idtac " ".

idtac "Exiting exercise (havoc_swap)".
idtac " ".

idtac "Entering exercise p1_p2_term (advanced): 4 points".
Abort.
Import Himp.
Goal True.
idtac " ".

idtac "#> Himp.p1_may_diverge".
check_type @Himp.p1_may_diverge (forall st st', st X <> 0 -> ~ p1 / st \\ st').
idtac "Assumptions:".
Abort.
Print Assumptions Himp.p1_may_diverge.
Goal True.
idtac " ".

idtac "#> Himp.p2_may_diverge".
check_type @Himp.p2_may_diverge (forall st st', st X <> 0 -> ~ p2 / st \\ st').
idtac "Assumptions:".
Abort.
Print Assumptions Himp.p2_may_diverge.
Goal True.
idtac " ".

idtac "Exiting exercise (p1_p2_term)".
idtac " ".

idtac "Entering exercise p1_p2_equiv (advanced): 4 points".
Abort.
Import Himp.
Goal True.
idtac " ".

idtac "#> Himp.p1_p2_equiv".
check_type @Himp.p1_p2_equiv (cequiv p1 p2).
idtac "Assumptions:".
Abort.
Print Assumptions Himp.p1_p2_equiv.
Goal True.
idtac " ".

idtac "Exiting exercise (p1_p2_equiv)".
idtac " ".

idtac "Entering exercise p3_p4_inequiv (advanced): 4 points".
Abort.
Import Himp.
Goal True.
idtac " ".

idtac "Manually graded.".
idtac " ".

idtac "Exiting exercise (p3_p4_inequiv)".
idtac " ".
Abort.

End TestHimp.
Goal True.
idtac "Max points - regular: 20".
idtac "Max points - advanced: 32".
Abort.
