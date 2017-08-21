Require Import Hoare.
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

Require Import Hoare.
Import Check.

Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Imp.
Require Import Maps.
Goal True.
idtac "Entering exercise hoare_asgn_examples (standard): 2 points".
idtac " ".

idtac "Manually graded.".
idtac " ".

idtac "Exiting exercise (hoare_asgn_examples)".
idtac " ".

idtac "Entering exercise hoare_asgn_wrong (standard): 2 points".
idtac " ".

idtac "Manually graded.".
idtac " ".

idtac "Exiting exercise (hoare_asgn_wrong)".
idtac " ".

idtac "Entering exercise hoare_asgn_fwd (advanced): 3 points".
idtac " ".

idtac "#> hoare_asgn_fwd".
check_type @hoare_asgn_fwd ((forall {X Y : Type} {f g : X -> Y}, (forall (x : X), f x = g x) -> f = g) -> forall m a P, {{fun st => P st /\ st X = m}}X ::= a{{fun st => P(t_update st X m) /\ st X = aeval(t_update st X m)a}}).
idtac "Assumptions:".
Abort.
Print Assumptions hoare_asgn_fwd.
Goal True.
idtac " ".

idtac "Exiting exercise (hoare_asgn_fwd)".
idtac " ".

idtac "Entering exercise hoare_asgn_fwd_exists (advanced): 2 points".
idtac " ".

idtac "#> hoare_asgn_fwd_exists".
check_type @hoare_asgn_fwd_exists ((forall {X Y : Type} {f g : X -> Y}, (forall (x : X), f x = g x) -> f = g) -> forall a P, {{fun st => P st}}X ::= a{{fun st => exists m, P(t_update st X m) /\ st X = aeval(t_update st X m)a}}).
idtac "Assumptions:".
Abort.
Print Assumptions hoare_asgn_fwd_exists.
Goal True.
idtac " ".

idtac "Exiting exercise (hoare_asgn_fwd_exists)".
idtac " ".

idtac "Entering exercise hoare_asgn_examples_2 (standard): 2 points".
idtac " ".

idtac "Manually graded.".
idtac " ".

idtac "Exiting exercise (hoare_asgn_examples_2)".
idtac " ".

idtac "Entering exercise hoare_asgn_example4 (standard): 2 points".
idtac " ".

idtac "#> hoare_asgn_example4".
check_type @hoare_asgn_example4 ({{fun st => True}}(X ::=(ANum 1);; Y ::=(ANum 2)){{fun st => st X = 1 /\ st Y = 2}}).
idtac "Assumptions:".
Abort.
Print Assumptions hoare_asgn_example4.
Goal True.
idtac " ".

idtac "Exiting exercise (hoare_asgn_example4)".
idtac " ".

idtac "Entering exercise swap_exercise (standard): 3 points".
idtac " ".

idtac "#> swap_program".
check_type @swap_program (com).
idtac "Assumptions:".
Abort.
Print Assumptions swap_program.
Goal True.
idtac " ".

idtac "#> swap_exercise".
check_type @swap_exercise ({{fun st => st X <= st Y}}swap_program{{fun st => st Y <= st X}}).
idtac "Assumptions:".
Abort.
Print Assumptions swap_exercise.
Goal True.
idtac " ".

idtac "Exiting exercise (swap_exercise)".
idtac " ".

idtac "Entering exercise hoarestate1 (standard): 3 points".
idtac " ".

idtac "Manually graded.".
idtac " ".

idtac "Exiting exercise (hoarestate1)".
idtac " ".

idtac "Entering exercise if_minus_plus (standard): 2 points".
idtac " ".

idtac "#> if_minus_plus".
check_type @if_minus_plus ({{fun st => True}}IFB(BLe(AId X)(AId Y))THEN(Z ::= AMinus(AId Y)(AId X))ELSE(Y ::= APlus(AId X)(AId Z))FI{{fun st => st Y = st X + st Z}}).
idtac "Assumptions:".
Abort.
Print Assumptions if_minus_plus.
Goal True.
idtac " ".

idtac "Exiting exercise (if_minus_plus)".
idtac " ".

idtac "Entering exercise if1_hoare (standard): 4 points".
idtac " ".

idtac "Manually graded.".
idtac " ".

idtac "Exiting exercise (if1_hoare)".
idtac " ".

idtac "Entering exercise hoare_repeat (advanced): 4 points".
idtac " ".

idtac "Manually graded.".
idtac " ".

idtac "Exiting exercise (hoare_repeat)".
idtac " ".

idtac "Entering exercise himp_hoare (standard): 3 points".
idtac " ".
Abort.

Module TestHimp.
Import Himp.
Goal True.
idtac "#> Himp.havoc_pre".
check_type @Himp.havoc_pre (forall (X : id) (Q : Assertion), Assertion).
idtac "Assumptions:".
Abort.
Print Assumptions Himp.havoc_pre.
Goal True.
idtac " ".

idtac "#> Himp.hoare_havoc".
check_type @Himp.hoare_havoc (forall (Q : Assertion) (X : id), {{havoc_pre X Q}}HAVOC X{{Q}}).
idtac "Assumptions:".
Abort.
Print Assumptions Himp.hoare_havoc.
Goal True.
idtac " ".
Abort.

End TestHimp.
Goal True.
idtac "Exiting exercise (himp_hoare)".
idtac " ".

idtac "Max points - regular: 23".
idtac "Max points - advanced: 32".
Abort.
