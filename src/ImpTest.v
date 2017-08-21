Require Import Imp.
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

Require Import Imp.
Import Check.

Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Maps.
Module TestAExp.
Import AExp.
Goal True.
idtac "Entering exercise optimize_0plus_b (standard): 3 points".
Abort.
Import AExp.
Goal True.
idtac " ".

idtac "#> AExp.optimize_0plus_b".
check_type @AExp.optimize_0plus_b (forall (b : bexp), bexp).
idtac "Assumptions:".
Abort.
Print Assumptions AExp.optimize_0plus_b.
Goal True.
idtac " ".

idtac "#> AExp.optimize_0plus_b_sound".
check_type @AExp.optimize_0plus_b_sound (forall b, beval(optimize_0plus_b b) = beval b).
idtac "Assumptions:".
Abort.
Print Assumptions AExp.optimize_0plus_b_sound.
Goal True.
idtac " ".

idtac "Exiting exercise (optimize_0plus_b)".
idtac " ".
Abort.

Require Import Coq.omega.Omega.
Module TestaevalR_first_try.
Import aevalR_first_try.
End TestaevalR_first_try.
Goal True.
idtac "Entering exercise bevalR (standard): 3 points".
Abort.
Import AExp.
Goal True.
idtac " ".

idtac "#> AExp.beval_iff_bevalR".
check_type @AExp.beval_iff_bevalR (forall b bv, bevalR b bv <-> beval b = bv).
idtac "Assumptions:".
Abort.
Print Assumptions AExp.beval_iff_bevalR.
Goal True.
idtac " ".

idtac "Exiting exercise (bevalR)".
idtac " ".
Abort.

End TestAExp.
Module TestaevalR_division.
Import aevalR_division.
End TestaevalR_division.
Module TestaevalR_extended.
Import aevalR_extended.
End TestaevalR_extended.
Goal True.
idtac "Entering exercise ceval_example2 (standard): 2 points".
idtac " ".

idtac "#> ceval_example2".
check_type @ceval_example2 ((X ::= ANum 0 ;; Y ::= ANum 1 ;; Z ::= ANum 2)/ empty_state \\(t_update(t_update(t_update empty_state X 0)Y 1)Z 2)).
idtac "Assumptions:".
Abort.
Print Assumptions ceval_example2.
Goal True.
idtac " ".

idtac "Exiting exercise (ceval_example2)".
idtac " ".

idtac "Entering exercise pup_to_n (advanced): 3 points".
idtac " ".

idtac "#> pup_to_n".
check_type @pup_to_n (com).
idtac "Assumptions:".
Abort.
Print Assumptions pup_to_n.
Goal True.
idtac " ".

idtac "#> pup_to_2_ceval".
check_type @pup_to_2_ceval (pup_to_n /(t_update empty_state X 2)\\ t_update(t_update(t_update(t_update(t_update(t_update empty_state X 2)Y 0)Y 2)X 1)Y 3)X 0).
idtac "Assumptions:".
Abort.
Print Assumptions pup_to_2_ceval.
Goal True.
idtac " ".

idtac "Exiting exercise (pup_to_n)".
idtac " ".

idtac "Entering exercise XtimesYinZ_spec (standard): 3 points".
idtac " ".

idtac "Manually graded.".
idtac " ".

idtac "Exiting exercise (XtimesYinZ_spec)".
idtac " ".

idtac "Entering exercise loop_never_stops (standard): 3 points".
idtac " ".

idtac "#> loop_never_stops".
check_type @loop_never_stops (forall st st', ~ (loop / st \\ st')).
idtac "Assumptions:".
Abort.
Print Assumptions loop_never_stops.
Goal True.
idtac " ".

idtac "Exiting exercise (loop_never_stops)".
idtac " ".

idtac "Entering exercise no_whilesR (standard): 3 points".
idtac " ".

idtac "#> no_whiles_eqv".
check_type @no_whiles_eqv (forall c, no_whiles c = true <-> no_whilesR c).
idtac "Assumptions:".
Abort.
Print Assumptions no_whiles_eqv.
Goal True.
idtac " ".

idtac "Exiting exercise (no_whilesR)".
idtac " ".

idtac "Entering exercise no_whiles_terminating (standard): 4 points".
idtac " ".

idtac "Manually graded.".
idtac " ".

idtac "Exiting exercise (no_whiles_terminating)".
idtac " ".

idtac "Entering exercise stack_compiler (standard): 3 points".
idtac " ".

idtac "#> s_execute".
check_type @s_execute (forall (st : state) (stack : list nat) (prog : list sinstr), list nat).
idtac "Assumptions:".
Abort.
Print Assumptions s_execute.
Goal True.
idtac " ".

idtac "#> s_execute1".
check_type @s_execute1 (s_execute empty_state[][SPush 5 ; SPush 3 ; SPush 1 ; SMinus] = [2 ; 5]).
idtac "Assumptions:".
Abort.
Print Assumptions s_execute1.
Goal True.
idtac " ".

idtac "#> s_execute2".
check_type @s_execute2 (s_execute(t_update empty_state X 3)[3 ; 4][SPush 4 ; SLoad X ; SMult ; SPlus] = [15 ; 4]).
idtac "Assumptions:".
Abort.
Print Assumptions s_execute2.
Goal True.
idtac " ".

idtac "#> s_compile".
check_type @s_compile (forall (e : aexp), list sinstr).
idtac "Assumptions:".
Abort.
Print Assumptions s_compile.
Goal True.
idtac " ".

idtac "#> s_compile1".
check_type @s_compile1 (s_compile(AMinus(AId X)(AMult(ANum 2)(AId Y))) = [SLoad X ; SPush 2 ; SLoad Y ; SMult ; SMinus]).
idtac "Assumptions:".
Abort.
Print Assumptions s_compile1.
Goal True.
idtac " ".

idtac "Exiting exercise (stack_compiler)".
idtac " ".

idtac "Entering exercise stack_compiler_correct (advanced): 4 points".
idtac " ".

idtac "#> s_compile_correct".
check_type @s_compile_correct (forall (st : state) (e : aexp), s_execute st[](s_compile e) = [aeval st e]).
idtac "Assumptions:".
Abort.
Print Assumptions s_compile_correct.
Goal True.
idtac " ".

idtac "Exiting exercise (stack_compiler_correct)".
idtac " ".
Abort.

Module TestBreakImp.
Import BreakImp.
Goal True.
idtac "Entering exercise break_imp (advanced): 4 points".
Abort.
Import BreakImp.
Goal True.
idtac " ".

idtac "#> BreakImp.break_ignore".
check_type @BreakImp.break_ignore (forall c st st' s, (BREAK ;; c)/ st \\ s / st' -> st = st').
idtac "Assumptions:".
Abort.
Print Assumptions BreakImp.break_ignore.
Goal True.
idtac " ".

idtac "#> BreakImp.while_continue".
check_type @BreakImp.while_continue (forall b c st st' s, (WHILE b DO c END)/ st \\ s / st' -> s = SContinue).
idtac "Assumptions:".
Abort.
Print Assumptions BreakImp.while_continue.
Goal True.
idtac " ".

idtac "#> BreakImp.while_stops_on_break".
check_type @BreakImp.while_stops_on_break (forall b c st st', beval st b = true -> c / st \\ SBreak / st' -> (WHILE b DO c END)/ st \\ SContinue / st').
idtac "Assumptions:".
Abort.
Print Assumptions BreakImp.while_stops_on_break.
Goal True.
idtac " ".

idtac "Exiting exercise (break_imp)".
idtac " ".
Abort.

End TestBreakImp.
Goal True.
idtac "Max points - regular: 24".
idtac "Max points - advanced: 35".
Abort.
