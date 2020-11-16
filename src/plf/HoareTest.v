Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From PLF Require Import Hoare.

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

From PLF Require Import Hoare.
Import Check.

Goal True.

idtac "-------------------  hoare_post_true  --------------------".
idtac " ".

idtac "#> hoare_post_true".
idtac "Possible points: 1".
check_type @hoare_post_true (
(forall (P Q : Assertion) (c : com),
 (forall st : state, Q st) -> {{P}} c {{Q}})).
idtac "Assumptions:".
Abort.
Print Assumptions hoare_post_true.
Goal True.
idtac " ".

idtac "-------------------  hoare_pre_false  --------------------".
idtac " ".

idtac "#> hoare_pre_false".
idtac "Possible points: 1".
check_type @hoare_pre_false (
(forall (P Q : Assertion) (c : com),
 (forall st : state, ~ P st) -> {{P}} c {{Q}})).
idtac "Assumptions:".
Abort.
Print Assumptions hoare_pre_false.
Goal True.
idtac " ".

idtac "-------------------  hoare_asgn_wrong  --------------------".
idtac " ".

idtac "#> Manually graded: hoare_asgn_wrong".
idtac "Possible points: 2".
print_manual_grade manual_grade_for_hoare_asgn_wrong.
idtac " ".

idtac "-------------------  hoare_asgn_fwd  --------------------".
idtac " ".

idtac "#> hoare_asgn_fwd".
idtac "Advanced".
idtac "Possible points: 3".
check_type @hoare_asgn_fwd (
(forall (m : nat) (a : aexp) (P : state -> Prop),
 {{fun st : state => P st /\ st X = m}} X := a
 {{fun st : state =>
   P (@Maps.t_update nat st X m) /\
   st X = aeval (@Maps.t_update nat st X m) a}})).
idtac "Assumptions:".
Abort.
Print Assumptions hoare_asgn_fwd.
Goal True.
idtac " ".

idtac "-------------------  hoare_asgn_examples_2  --------------------".
idtac " ".

idtac "#> assn_sub_ex1'".
idtac "Possible points: 1".
check_type @assn_sub_ex1' (
({{fun st : state => Aexp_of_aexp (AId X) st <= Aexp_of_nat 5 st}}
 X := (ANum 2) * (AId X)
 {{fun st : state => Aexp_of_aexp (AId X) st <= Aexp_of_nat 10 st}})).
idtac "Assumptions:".
Abort.
Print Assumptions assn_sub_ex1'.
Goal True.
idtac " ".

idtac "#> assn_sub_ex2'".
idtac "Possible points: 1".
check_type @assn_sub_ex2' (
({{(fun st0 : state => (Aexp_of_nat 0 st0 <= Aexp_of_nat 3 st0)%nat) /\
   (fun st0 : state => (Aexp_of_nat 3 st0 <= Aexp_of_nat 5 st0)%nat)}}
 X := (ANum 3)
 {{(fun st0 : state => (Aexp_of_nat 0 st0 <= Aexp_of_aexp (AId X) st0)%nat) /\
   (fun st0 : state => (Aexp_of_aexp (AId X) st0 <= Aexp_of_nat 5 st0)%nat)}})).
idtac "Assumptions:".
Abort.
Print Assumptions assn_sub_ex2'.
Goal True.
idtac " ".

idtac "-------------------  hoare_asgn_example4  --------------------".
idtac " ".

idtac "#> hoare_asgn_example4".
idtac "Possible points: 2".
check_type @hoare_asgn_example4 (
({{assert_of_Prop True}} X := (ANum 1); Y := (ANum 2)
 {{(fun st0 : state => (Aexp_of_aexp (AId X) st0 = Aexp_of_nat 1 st0)%type) /\
   (fun st0 : state => (Aexp_of_aexp (AId Y) st0 = Aexp_of_nat 2 st0)%type)}})).
idtac "Assumptions:".
Abort.
Print Assumptions hoare_asgn_example4.
Goal True.
idtac " ".

idtac "-------------------  swap_exercise  --------------------".
idtac " ".

idtac "#> swap_exercise".
idtac "Possible points: 3".
check_type @swap_exercise (
({{fun st : state => Aexp_of_aexp (AId X) st <= Aexp_of_aexp (AId Y) st}}
 swap_program
 {{fun st : state => Aexp_of_aexp (AId Y) st <= Aexp_of_aexp (AId X) st}})).
idtac "Assumptions:".
Abort.
Print Assumptions swap_exercise.
Goal True.
idtac " ".

idtac "-------------------  invalid_triple  --------------------".
idtac " ".

idtac "#> invalid_triple".
idtac "Possible points: 6".
check_type @invalid_triple (
(~
 (forall (a : aexp) (n : nat),
  {{fun st : state => Aexp_of_aexp a st = Aexp_of_nat n st}}
  X := (ANum 3); Y := a
  {{fun st : state => Aexp_of_aexp (AId Y) st = Aexp_of_nat n st}}))).
idtac "Assumptions:".
Abort.
Print Assumptions invalid_triple.
Goal True.
idtac " ".

idtac "-------------------  if_minus_plus  --------------------".
idtac " ".

idtac "#> if_minus_plus".
idtac "Possible points: 2".
check_type @if_minus_plus (
({{assert_of_Prop True}}
 if (AId X) <= (AId Y) then Z := (AId Y) - (AId X)
 else Y := (AId X) + (AId Z) end
 {{fun st : state =>
   Aexp_of_aexp (AId Y) st =
   mkAexp
     (fun st0 : state =>
      (Aexp_of_aexp (AId X) st0 + Aexp_of_aexp (AId Z) st0)%nat) st}})).
idtac "Assumptions:".
Abort.
Print Assumptions if_minus_plus.
Goal True.
idtac " ".

idtac "-------------------  if1_ceval  --------------------".
idtac " ".

idtac "#> If1.if1true_test".
idtac "Possible points: 1".
check_type @If1.if1true_test (
(If1.ceval (If1.CIf1 <{ (AId X) = (ANum 0) }> (If1.CAss X (ANum 1))) empty_st
   (X !-> 1))).
idtac "Assumptions:".
Abort.
Print Assumptions If1.if1true_test.
Goal True.
idtac " ".

idtac "#> If1.if1false_test".
idtac "Possible points: 1".
check_type @If1.if1false_test (
(If1.ceval (If1.CIf1 <{ (AId X) = (ANum 0) }> (If1.CAss X (ANum 1)))
   (X !-> 2) (X !-> 2))).
idtac "Assumptions:".
Abort.
Print Assumptions If1.if1false_test.
Goal True.
idtac " ".

idtac "-------------------  hoare_if1  --------------------".
idtac " ".

idtac "#> Manually graded: If1.hoare_if1".
idtac "Possible points: 2".
print_manual_grade If1.manual_grade_for_hoare_if1.
idtac " ".

idtac "-------------------  hoare_if1_good  --------------------".
idtac " ".

idtac "#> If1.hoare_if1_good".
idtac "Possible points: 2".
check_type @If1.hoare_if1_good (
(If1.hoare_triple
   (fun st : state =>
    mkAexp
      (fun st0 : state =>
       (Aexp_of_aexp (AId X) st0 + Aexp_of_aexp (AId Y) st0)%nat) st =
    Aexp_of_aexp (AId Z) st)
   (If1.CIf1 <{ ~ (AId Y) = (ANum 0) }> (If1.CAss X <{ (AId X) + (AId Y) }>))
   (fun st : state => Aexp_of_aexp (AId X) st = Aexp_of_aexp (AId Z) st))).
idtac "Assumptions:".
Abort.
Print Assumptions If1.hoare_if1_good.
Goal True.
idtac " ".

idtac "-------------------  hoare_repeat  --------------------".
idtac " ".

idtac "#> Manually graded: hoare_repeat".
idtac "Advanced".
idtac "Possible points: 6".
print_manual_grade manual_grade_for_hoare_repeat.
idtac " ".

idtac "-------------------  hoare_havoc  --------------------".
idtac " ".

idtac "#> Himp.hoare_havoc".
idtac "Possible points: 3".
check_type @Himp.hoare_havoc (
(forall (Q : Assertion) (X : String.string),
 Himp.hoare_triple (Himp.havoc_pre X Q) (Himp.CHavoc X) Q)).
idtac "Assumptions:".
Abort.
Print Assumptions Himp.hoare_havoc.
Goal True.
idtac " ".

idtac "-------------------  havoc_post  --------------------".
idtac " ".

idtac "#> Himp.havoc_post".
idtac "Possible points: 3".
check_type @Himp.havoc_post (
(forall (P : Assertion) (X : String.string),
 Himp.hoare_triple P (Himp.CHavoc X)
   (fun st : state => exists n : nat, (P [X |-> ANum n]) st))).
idtac "Assumptions:".
Abort.
Print Assumptions Himp.havoc_post.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 31".
idtac "Max points - advanced: 40".
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
idtac "---------- hoare_post_true ---------".
Print Assumptions hoare_post_true.
idtac "---------- hoare_pre_false ---------".
Print Assumptions hoare_pre_false.
idtac "---------- hoare_asgn_wrong ---------".
idtac "MANUAL".
idtac "---------- assn_sub_ex1' ---------".
Print Assumptions assn_sub_ex1'.
idtac "---------- assn_sub_ex2' ---------".
Print Assumptions assn_sub_ex2'.
idtac "---------- hoare_asgn_example4 ---------".
Print Assumptions hoare_asgn_example4.
idtac "---------- swap_exercise ---------".
Print Assumptions swap_exercise.
idtac "---------- invalid_triple ---------".
Print Assumptions invalid_triple.
idtac "---------- if_minus_plus ---------".
Print Assumptions if_minus_plus.
idtac "---------- If1.if1true_test ---------".
Print Assumptions If1.if1true_test.
idtac "---------- If1.if1false_test ---------".
Print Assumptions If1.if1false_test.
idtac "---------- hoare_if1 ---------".
idtac "MANUAL".
idtac "---------- If1.hoare_if1_good ---------".
Print Assumptions If1.hoare_if1_good.
idtac "---------- Himp.hoare_havoc ---------".
Print Assumptions Himp.hoare_havoc.
idtac "---------- Himp.havoc_post ---------".
Print Assumptions Himp.havoc_post.
idtac "".
idtac "********** Advanced **********".
idtac "---------- hoare_asgn_fwd ---------".
Print Assumptions hoare_asgn_fwd.
idtac "---------- hoare_repeat ---------".
idtac "MANUAL".
Abort.

(* 2020-09-09 21:08 *)
