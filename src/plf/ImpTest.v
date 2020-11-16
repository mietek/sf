Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From PLF Require Import Imp.

Parameter MISSING: Type.

Module Check.

Ltac check_type A B :=
    match type of A with
    | context[MISSING] => idtac "Missing:" A
    | ?T => first [unify T B; idtac "Type: ok" | idtac "Type: wrong - should be (" B ")"]
    end.

Ltac print_manual_grade A :=
    match eval compute in A with
    | Some (_ ?S ?C) =>
        idtac "Score:"  S;
        match eval compute in C with
          | ""%string => idtac "Comment: None"
          | _ => idtac "Comment:" C
        end
    | None =>
        idtac "Score: Ungraded";
        idtac "Comment: None"
    end.

End Check.

From PLF Require Import Imp.
Import Check.

Goal True.

idtac "-------------------  optimize_0plus_b_sound  --------------------".
idtac " ".

idtac "#> AExp.optimize_0plus_b_sound".
idtac "Possible points: 3".
check_type @AExp.optimize_0plus_b_sound (
(forall b : AExp.bexp, AExp.beval (AExp.optimize_0plus_b b) = AExp.beval b)).
idtac "Assumptions:".
Abort.
Print Assumptions AExp.optimize_0plus_b_sound.
Goal True.
idtac " ".

idtac "-------------------  bevalR  --------------------".
idtac " ".

idtac "#> AExp.beval_iff_bevalR".
idtac "Possible points: 3".
check_type @AExp.beval_iff_bevalR (
(forall (b : AExp.bexp) (bv : bool), AExp.bevalR b bv <-> AExp.beval b = bv)).
idtac "Assumptions:".
Abort.
Print Assumptions AExp.beval_iff_bevalR.
Goal True.
idtac " ".

idtac "-------------------  ceval_example2  --------------------".
idtac " ".

idtac "#> ceval_example2".
idtac "Possible points: 2".
check_type @ceval_example2 (
(empty_st =[ X := (ANum 0); Y := (ANum 1); Z := (ANum 2)
 ]=> @Maps.t_update nat (@Maps.t_update nat (X !-> 0) Y 1) Z 2)).
idtac "Assumptions:".
Abort.
Print Assumptions ceval_example2.
Goal True.
idtac " ".

idtac "-------------------  loop_never_stops  --------------------".
idtac " ".

idtac "#> loop_never_stops".
idtac "Possible points: 3".
check_type @loop_never_stops ((forall st st' : state, ~ st =[ loop ]=> st')).
idtac "Assumptions:".
Abort.
Print Assumptions loop_never_stops.
Goal True.
idtac " ".

idtac "-------------------  no_whiles_eqv  --------------------".
idtac " ".

idtac "#> no_whiles_eqv".
idtac "Possible points: 3".
check_type @no_whiles_eqv ((forall c : com, no_whiles c = true <-> no_whilesR c)).
idtac "Assumptions:".
Abort.
Print Assumptions no_whiles_eqv.
Goal True.
idtac " ".

idtac "-------------------  no_whiles_terminating  --------------------".
idtac " ".

idtac "#> Manually graded: no_whiles_terminating".
idtac "Possible points: 6".
print_manual_grade manual_grade_for_no_whiles_terminating.
idtac " ".

idtac "-------------------  stack_compiler  --------------------".
idtac " ".

idtac "#> s_execute1".
idtac "Possible points: 1".
check_type @s_execute1 (
(s_execute empty_st (@nil nat)
   (SPush 5 :: SPush 3 :: SPush 1 :: SMinus :: @nil sinstr) =
 (2 :: 5 :: @nil nat)%list)).
idtac "Assumptions:".
Abort.
Print Assumptions s_execute1.
Goal True.
idtac " ".

idtac "#> s_execute2".
idtac "Possible points: 0.5".
check_type @s_execute2 (
(s_execute (X !-> 3) (3 :: 4 :: @nil nat)
   (SPush 4 :: SLoad X :: SMult :: SPlus :: @nil sinstr) =
 (15 :: 4 :: @nil nat)%list)).
idtac "Assumptions:".
Abort.
Print Assumptions s_execute2.
Goal True.
idtac " ".

idtac "#> s_compile1".
idtac "Possible points: 1.5".
check_type @s_compile1 (
(s_compile <{ (AId X) - (ANum 2) * (AId Y) }> =
 (SLoad X :: SPush 2 :: SLoad Y :: SMult :: SMinus :: @nil sinstr)%list)).
idtac "Assumptions:".
Abort.
Print Assumptions s_compile1.
Goal True.
idtac " ".

idtac "-------------------  execute_app  --------------------".
idtac " ".

idtac "#> execute_app".
idtac "Possible points: 3".
check_type @execute_app (
(forall (st : state) (p1 p2 : list sinstr) (stack : list nat),
 s_execute st stack (p1 ++ p2) = s_execute st (s_execute st stack p1) p2)).
idtac "Assumptions:".
Abort.
Print Assumptions execute_app.
Goal True.
idtac " ".

idtac "-------------------  stack_compiler_correct  --------------------".
idtac " ".

idtac "#> s_compile_correct_aux".
idtac "Possible points: 2.5".
check_type @s_compile_correct_aux (
(forall (st : state) (e : aexp) (stack : list nat),
 s_execute st stack (s_compile e) = (aeval st e :: stack)%list)).
idtac "Assumptions:".
Abort.
Print Assumptions s_compile_correct_aux.
Goal True.
idtac " ".

idtac "#> s_compile_correct".
idtac "Possible points: 0.5".
check_type @s_compile_correct (
(forall (st : state) (e : aexp),
 s_execute st (@nil nat) (s_compile e) = (aeval st e :: @nil nat)%list)).
idtac "Assumptions:".
Abort.
Print Assumptions s_compile_correct.
Goal True.
idtac " ".

idtac "-------------------  break_imp  --------------------".
idtac " ".

idtac "#> BreakImp.break_ignore".
idtac "Advanced".
idtac "Possible points: 1.5".
check_type @BreakImp.break_ignore (
(forall (c : BreakImp.com) (st st' : state) (s : BreakImp.result),
 BreakImp.ceval (BreakImp.CSeq BreakImp.CBreak c) st s st' -> st = st')).
idtac "Assumptions:".
Abort.
Print Assumptions BreakImp.break_ignore.
Goal True.
idtac " ".

idtac "#> BreakImp.while_continue".
idtac "Advanced".
idtac "Possible points: 1.5".
check_type @BreakImp.while_continue (
(forall (b : bexp) (c : BreakImp.com) (st st' : state) (s : BreakImp.result),
 BreakImp.ceval (BreakImp.CWhile b c) st s st' -> s = BreakImp.SContinue)).
idtac "Assumptions:".
Abort.
Print Assumptions BreakImp.while_continue.
Goal True.
idtac " ".

idtac "#> BreakImp.while_stops_on_break".
idtac "Advanced".
idtac "Possible points: 3".
check_type @BreakImp.while_stops_on_break (
(forall (b : bexp) (c : BreakImp.com) (st st' : state),
 beval st b = true ->
 BreakImp.ceval c st BreakImp.SBreak st' ->
 BreakImp.ceval (BreakImp.CWhile b c) st BreakImp.SContinue st')).
idtac "Assumptions:".
Abort.
Print Assumptions BreakImp.while_stops_on_break.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 29".
idtac "Max points - advanced: 35".
idtac "".
idtac "Allowed Axioms:".
idtac "functional_extensionality".
idtac "FunctionalExtensionality.functional_extensionality_dep".
idtac "".
idtac "".
idtac "********** Summary **********".
idtac "".
idtac "Below is a summary of the automatically graded exercises that are incomplete.".
idtac "".
idtac "The output for each exercise can be any of the following:".
idtac "  - 'Closed under the global context', if it is complete".
idtac "  - 'MANUAL', if it is manually graded".
idtac "  - A list of pending axioms, containing unproven assumptions. In this case".
idtac "    the exercise is considered complete, if the axioms are all allowed.".
idtac "".
idtac "********** Standard **********".
idtac "---------- AExp.optimize_0plus_b_sound ---------".
Print Assumptions AExp.optimize_0plus_b_sound.
idtac "---------- AExp.beval_iff_bevalR ---------".
Print Assumptions AExp.beval_iff_bevalR.
idtac "---------- ceval_example2 ---------".
Print Assumptions ceval_example2.
idtac "---------- loop_never_stops ---------".
Print Assumptions loop_never_stops.
idtac "---------- no_whiles_eqv ---------".
Print Assumptions no_whiles_eqv.
idtac "---------- no_whiles_terminating ---------".
idtac "MANUAL".
idtac "---------- s_execute1 ---------".
Print Assumptions s_execute1.
idtac "---------- s_execute2 ---------".
Print Assumptions s_execute2.
idtac "---------- s_compile1 ---------".
Print Assumptions s_compile1.
idtac "---------- execute_app ---------".
Print Assumptions execute_app.
idtac "---------- s_compile_correct_aux ---------".
Print Assumptions s_compile_correct_aux.
idtac "---------- s_compile_correct ---------".
Print Assumptions s_compile_correct.
idtac "".
idtac "********** Advanced **********".
idtac "---------- BreakImp.break_ignore ---------".
Print Assumptions BreakImp.break_ignore.
idtac "---------- BreakImp.while_continue ---------".
Print Assumptions BreakImp.while_continue.
idtac "---------- BreakImp.while_stops_on_break ---------".
Print Assumptions BreakImp.while_stops_on_break.
Abort.

(* 2020-09-09 21:08 *)
