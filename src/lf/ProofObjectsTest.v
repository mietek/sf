Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From LF Require Import ProofObjects.

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

From LF Require Import ProofObjects.
Import Check.

Goal True.

idtac "-------------------  eight_is_even  --------------------".
idtac " ".

idtac "#> ev_8".
idtac "Possible points: 1".
check_type @ev_8 ((ev 8)).
idtac "Assumptions:".
Abort.
Print Assumptions ev_8.
Goal True.
idtac " ".

idtac "#> ev_8'".
idtac "Possible points: 1".
check_type @ev_8' ((ev 8)).
idtac "Assumptions:".
Abort.
Print Assumptions ev_8'.
Goal True.
idtac " ".

idtac "-------------------  conj_fact  --------------------".
idtac " ".

idtac "#> Props.conj_fact".
idtac "Possible points: 2".
check_type @Props.conj_fact ((forall P Q R : Prop, P /\ Q -> Q /\ R -> P /\ R)).
idtac "Assumptions:".
Abort.
Print Assumptions Props.conj_fact.
Goal True.
idtac " ".

idtac "-------------------  or_commut'  --------------------".
idtac " ".

idtac "#> Props.or_commut'".
idtac "Possible points: 2".
check_type @Props.or_commut' ((forall P Q : Prop, P \/ Q -> Q \/ P)).
idtac "Assumptions:".
Abort.
Print Assumptions Props.or_commut'.
Goal True.
idtac " ".

idtac "-------------------  ex_ev_Sn  --------------------".
idtac " ".

idtac "#> Props.ex_ev_Sn".
idtac "Possible points: 2".
check_type @Props.ex_ev_Sn ((exists n : nat, ev (S n))).
idtac "Assumptions:".
Abort.
Print Assumptions Props.ex_ev_Sn.
Goal True.
idtac " ".

idtac "-------------------  p_implies_true  --------------------".
idtac " ".

idtac "#> Props.p_implies_true".
idtac "Possible points: 1".
check_type @Props.p_implies_true ((forall P : Type, P -> Props.True)).
idtac "Assumptions:".
Abort.
Print Assumptions Props.p_implies_true.
Goal True.
idtac " ".

idtac "-------------------  ex_falso_quodlibet'  --------------------".
idtac " ".

idtac "#> Props.ex_falso_quodlibet'".
idtac "Possible points: 1".
check_type @Props.ex_falso_quodlibet' ((forall P : Type, Props.False -> P)).
idtac "Assumptions:".
Abort.
Print Assumptions Props.ex_falso_quodlibet'.
Goal True.
idtac " ".

idtac "-------------------  equality__leibniz_equality  --------------------".
idtac " ".

idtac "#> MyEquality.equality__leibniz_equality".
idtac "Possible points: 2".
check_type @MyEquality.equality__leibniz_equality (
(forall (X : Type) (x y : X),
 @MyEquality.eq X x y -> forall P : X -> Prop, P x -> P y)).
idtac "Assumptions:".
Abort.
Print Assumptions MyEquality.equality__leibniz_equality.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 12".
idtac "Max points - advanced: 12".
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
idtac "---------- ev_8 ---------".
Print Assumptions ev_8.
idtac "---------- ev_8' ---------".
Print Assumptions ev_8'.
idtac "---------- Props.conj_fact ---------".
Print Assumptions Props.conj_fact.
idtac "---------- Props.or_commut' ---------".
Print Assumptions Props.or_commut'.
idtac "---------- Props.ex_ev_Sn ---------".
Print Assumptions Props.ex_ev_Sn.
idtac "---------- Props.p_implies_true ---------".
Print Assumptions Props.p_implies_true.
idtac "---------- Props.ex_falso_quodlibet' ---------".
Print Assumptions Props.ex_falso_quodlibet'.
idtac "---------- MyEquality.equality__leibniz_equality ---------".
Print Assumptions MyEquality.equality__leibniz_equality.
idtac "".
idtac "********** Advanced **********".
Abort.

(* 2020-09-09 20:51 *)

(* 2020-09-09 20:51 *)
