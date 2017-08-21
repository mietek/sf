Require Import IndProp.
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

Require Import IndProp.
Import Check.

Require Export Logic.
Goal True.
idtac "Entering exercise ev_double (standard): 1 point".
idtac " ".

idtac "#> ev_double".
check_type @ev_double (forall n, ev(double n)).
idtac "Assumptions:".
Abort.
Print Assumptions ev_double.
Goal True.
idtac " ".

idtac "Exiting exercise (ev_double)".
idtac " ".

idtac "Entering exercise inversion_practice (standard): 1 point".
idtac " ".

idtac "#> SSSSev__even".
check_type @SSSSev__even (forall n, ev(S(S(S(S n)))) -> ev n).
idtac "Assumptions:".
Abort.
Print Assumptions SSSSev__even.
Goal True.
idtac " ".

idtac "#> even5_nonsense".
check_type @even5_nonsense (ev 5 -> 2 + 2 = 9).
idtac "Assumptions:".
Abort.
Print Assumptions even5_nonsense.
Goal True.
idtac " ".

idtac "Exiting exercise (inversion_practice)".
idtac " ".

idtac "Entering exercise ev_sum (standard): 2 points".
idtac " ".

idtac "#> ev_sum".
check_type @ev_sum (forall n m, ev n -> ev m -> ev(n + m)).
idtac "Assumptions:".
Abort.
Print Assumptions ev_sum.
Goal True.
idtac " ".

idtac "Exiting exercise (ev_sum)".
idtac " ".

idtac "Entering exercise ev_ev__ev (advanced): 3 points".
idtac " ".

idtac "#> ev_ev__ev".
check_type @ev_ev__ev (forall n m, ev(n + m) -> ev n -> ev m).
idtac "Assumptions:".
Abort.
Print Assumptions ev_ev__ev.
Goal True.
idtac " ".

idtac "Exiting exercise (ev_ev__ev)".
idtac " ".
Abort.

Module TestPlayground.
Import Playground.
End TestPlayground.
Goal True.
idtac "Entering exercise exp_match_ex1 (standard): 3 points".
idtac " ".

idtac "#> empty_is_empty".
check_type @empty_is_empty (forall T (s : list T), ~ (s =~ EmptySet)).
idtac "Assumptions:".
Abort.
Print Assumptions empty_is_empty.
Goal True.
idtac " ".

idtac "#> MUnion'".
check_type @MUnion' (forall T (s : list T) (re1 re2 : reg_exp T), s =~ re1 \/ s =~ re2 -> s =~ Union re1 re2).
idtac "Assumptions:".
Abort.
Print Assumptions MUnion'.
Goal True.
idtac " ".

idtac "#> MStar'".
check_type @MStar' (forall T (ss : list(list T)) (re : reg_exp T), (forall s, In s ss -> s =~ re) -> fold app ss[]=~ Star re).
idtac "Assumptions:".
Abort.
Print Assumptions MStar'.
Goal True.
idtac " ".

idtac "Exiting exercise (exp_match_ex1)".
idtac " ".

idtac "Entering exercise reg_exp_of_list (standard): 4 points".
idtac " ".

idtac "#> reg_exp_of_list_spec".
check_type @reg_exp_of_list_spec (forall T (s1 s2 : list T), s1 =~ reg_exp_of_list s2 <-> s1 = s2).
idtac "Assumptions:".
Abort.
Print Assumptions reg_exp_of_list_spec.
Goal True.
idtac " ".

idtac "Exiting exercise (reg_exp_of_list)".
idtac " ".

idtac "Entering exercise re_not_empty (standard): 4 points".
idtac " ".

idtac "#> re_not_empty".
check_type @re_not_empty (forall {T : Type} (re : reg_exp T), bool).
idtac "Assumptions:".
Abort.
Print Assumptions re_not_empty.
Goal True.
idtac " ".

idtac "#> re_not_empty_correct".
check_type @re_not_empty_correct (forall T (re : reg_exp T), (exists s, s =~ re) <-> re_not_empty re = true).
idtac "Assumptions:".
Abort.
Print Assumptions re_not_empty_correct.
Goal True.
idtac " ".

idtac "Exiting exercise (re_not_empty)".
idtac " ".

idtac "Entering exercise exp_match_ex2 (standard): 4 points".
idtac " ".

idtac "#> MStar''".
check_type @MStar'' (forall T (s : list T) (re : reg_exp T), s =~ Star re -> exists ss, s = fold app ss[] /\ forall s', In s' ss -> s' =~ re).
idtac "Assumptions:".
Abort.
Print Assumptions MStar''.
Goal True.
idtac " ".

idtac "Exiting exercise (exp_match_ex2)".
idtac " ".

idtac "Entering exercise pumping (advanced): 5 points".
idtac " ".
Abort.

Module TestPumping.
Import Pumping.
Goal True.
idtac "#> Pumping.pumping".
check_type @Pumping.pumping (forall T (re : reg_exp T) s, s =~ re -> pumping_constant re <= length s -> exists s1 s2 s3, s = s1 ++ s2 ++ s3 /\ s2 <>[] /\ forall m, s1 ++ napp m s2 ++ s3 =~ re).
idtac "Assumptions:".
Abort.
Print Assumptions Pumping.pumping.
Goal True.
idtac " ".
Abort.

End TestPumping.
Goal True.
idtac "Exiting exercise (pumping)".
idtac " ".
Abort.

Module TestFirstTry.
Import FirstTry.
End TestFirstTry.
Goal True.
idtac "Entering exercise reflect_iff (standard): 2 points".
idtac " ".

idtac "#> reflect_iff".
check_type @reflect_iff (forall P b, reflect P b -> (P <-> b = true)).
idtac "Assumptions:".
Abort.
Print Assumptions reflect_iff.
Goal True.
idtac " ".

idtac "Exiting exercise (reflect_iff)".
idtac " ".

idtac "Entering exercise beq_natP_practice (standard): 3 points".
idtac " ".

idtac "#> beq_natP_practice".
check_type @beq_natP_practice (forall n l, count n l = 0 -> ~ (In n l)).
idtac "Assumptions:".
Abort.
Print Assumptions beq_natP_practice.
Goal True.
idtac " ".

idtac "Exiting exercise (beq_natP_practice)".
idtac " ".

idtac "Entering exercise nostutter (standard): 3 points".
idtac " ".

idtac "Exiting exercise (nostutter)".
idtac " ".

idtac "Entering exercise filter_challenge (advanced): 4 points".
idtac " ".

idtac "Exiting exercise (filter_challenge)".
idtac " ".
Abort.

Module TestPigeon.
Import Pigeon.
End TestPigeon.
Goal True.
idtac "Max points - regular: 27".
idtac "Max points - advanced: 39".
Abort.
