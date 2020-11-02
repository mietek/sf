Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From PLF Require Import HoareAsLogic.

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

From PLF Require Import HoareAsLogic.
Import Check.

Goal True.

idtac "-------------------  provable_true_post  --------------------".
idtac " ".

idtac "#> provable_true_post".
idtac "Possible points: 3".
check_type @provable_true_post (
(forall (c : Imp.com) (P : Hoare.Assertion),
 derivable P c (Hoare.assert_of_Prop True))).
idtac "Assumptions:".
Abort.
Print Assumptions provable_true_post.
Goal True.
idtac " ".

idtac "-------------------  provable_false_pre  --------------------".
idtac " ".

idtac "#> provable_false_pre".
idtac "Possible points: 3".
check_type @provable_false_pre (
(forall (c : Imp.com) (Q : Hoare.Assertion),
 derivable (Hoare.assert_of_Prop False) c Q)).
idtac "Assumptions:".
Abort.
Print Assumptions provable_false_pre.
Goal True.
idtac " ".

idtac "-------------------  hoare_sound  --------------------".
idtac " ".

idtac "#> hoare_sound".
idtac "Possible points: 3".
check_type @hoare_sound (
(forall (P : Hoare.Assertion) (c : Imp.com) (Q : Hoare.Assertion),
 derivable P c Q -> valid P c Q)).
idtac "Assumptions:".
Abort.
Print Assumptions hoare_sound.
Goal True.
idtac " ".

idtac "-------------------  wp_seq  --------------------".
idtac " ".

idtac "#> wp_seq".
idtac "Possible points: 1".
check_type @wp_seq (
(forall (P Q : Hoare.Assertion) (c1 c2 : Imp.com),
 derivable P c1 (wp c2 Q) ->
 derivable (wp c2 Q) c2 Q -> derivable P (Imp.CSeq c1 c2) Q)).
idtac "Assumptions:".
Abort.
Print Assumptions wp_seq.
Goal True.
idtac " ".

idtac "-------------------  wp_invariant  --------------------".
idtac " ".

idtac "#> wp_invariant".
idtac "Possible points: 2".
check_type @wp_invariant (
(forall (b : Imp.bexp) (c : Imp.com) (Q : Hoare.Assertion),
 valid (fun st : Imp.state => wp (Imp.CWhile b c) Q st /\ Hoare.bassn b st) c
   (wp (Imp.CWhile b c) Q))).
idtac "Assumptions:".
Abort.
Print Assumptions wp_invariant.
Goal True.
idtac " ".

idtac "-------------------  hoare_complete  --------------------".
idtac " ".

idtac "#> hoare_complete".
idtac "Possible points: 6".
check_type @hoare_complete (
(forall (P : Hoare.Assertion) (c : Imp.com) (Q : Hoare.Assertion),
 valid P c Q -> derivable P c Q)).
idtac "Assumptions:".
Abort.
Print Assumptions hoare_complete.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 18".
idtac "Max points - advanced: 18".
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
idtac "---------- provable_true_post ---------".
Print Assumptions provable_true_post.
idtac "---------- provable_false_pre ---------".
Print Assumptions provable_false_pre.
idtac "---------- hoare_sound ---------".
Print Assumptions hoare_sound.
idtac "---------- wp_seq ---------".
Print Assumptions wp_seq.
idtac "---------- wp_invariant ---------".
Print Assumptions wp_invariant.
idtac "---------- hoare_complete ---------".
Print Assumptions hoare_complete.
idtac "".
idtac "********** Advanced **********".
Abort.

(* 2020-09-09 21:08 *)
