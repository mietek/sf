Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From VFA Require Import Binom.

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

From VFA Require Import Binom.
Import Check.

Goal True.

idtac "-------------------  empty_priq  --------------------".
idtac " ".

idtac "#> BinomQueue.empty_priq".
idtac "Possible points: 1".
check_type @BinomQueue.empty_priq ((BinomQueue.priq BinomQueue.empty)).
idtac "Assumptions:".
Abort.
Print Assumptions BinomQueue.empty_priq.
Goal True.
idtac " ".

idtac "-------------------  smash_valid  --------------------".
idtac " ".

idtac "#> BinomQueue.smash_valid".
idtac "Possible points: 2".
check_type @BinomQueue.smash_valid (
(forall (n : nat) (t u : BinomQueue.tree),
 BinomQueue.pow2heap n t ->
 BinomQueue.pow2heap n u -> BinomQueue.pow2heap (S n) (BinomQueue.smash t u))).
idtac "Assumptions:".
Abort.
Print Assumptions BinomQueue.smash_valid.
Goal True.
idtac " ".

idtac "-------------------  carry_valid  --------------------".
idtac " ".

idtac "#> BinomQueue.carry_valid".
idtac "Possible points: 3".
check_type @BinomQueue.carry_valid (
(forall (n : nat) (q : list BinomQueue.tree),
 BinomQueue.priq' n q ->
 forall t : BinomQueue.tree,
 t = BinomQueue.Leaf \/ BinomQueue.pow2heap n t ->
 BinomQueue.priq' n (BinomQueue.carry q t))).
idtac "Assumptions:".
Abort.
Print Assumptions BinomQueue.carry_valid.
Goal True.
idtac " ".

idtac "-------------------  priqueue_elems  --------------------".
idtac " ".

idtac "#> Manually graded: BinomQueue.priqueue_elems".
idtac "Possible points: 3".
print_manual_grade BinomQueue.manual_grade_for_priqueue_elems.
idtac " ".

idtac "-------------------  tree_elems_ext  --------------------".
idtac " ".

idtac "#> BinomQueue.tree_elems_ext".
idtac "Possible points: 2".
check_type @BinomQueue.tree_elems_ext (
(forall (t : BinomQueue.tree) (e1 e2 : list BinomQueue.key),
 @Permutation.Permutation BinomQueue.key e1 e2 ->
 BinomQueue.tree_elems t e1 -> BinomQueue.tree_elems t e2)).
idtac "Assumptions:".
Abort.
Print Assumptions BinomQueue.tree_elems_ext.
Goal True.
idtac " ".

idtac "-------------------  tree_perm  --------------------".
idtac " ".

idtac "#> BinomQueue.tree_perm".
idtac "Possible points: 2".
check_type @BinomQueue.tree_perm (
(forall (t : BinomQueue.tree) (e1 e2 : list BinomQueue.key),
 BinomQueue.tree_elems t e1 ->
 BinomQueue.tree_elems t e2 -> @Permutation.Permutation BinomQueue.key e1 e2)).
idtac "Assumptions:".
Abort.
Print Assumptions BinomQueue.tree_perm.
Goal True.
idtac " ".

idtac "-------------------  priqueue_elems_ext  --------------------".
idtac " ".

idtac "#> BinomQueue.priqueue_elems_ext".
idtac "Possible points: 2".
check_type @BinomQueue.priqueue_elems_ext (
(forall (q : list BinomQueue.tree) (e1 e2 : list BinomQueue.key),
 @Permutation.Permutation BinomQueue.key e1 e2 ->
 BinomQueue.priqueue_elems q e1 -> BinomQueue.priqueue_elems q e2)).
idtac "Assumptions:".
Abort.
Print Assumptions BinomQueue.priqueue_elems_ext.
Goal True.
idtac " ".

idtac "-------------------  abs_perm  --------------------".
idtac " ".

idtac "#> BinomQueue.abs_perm".
idtac "Possible points: 2".
check_type @BinomQueue.abs_perm (
(forall (p : BinomQueue.priqueue) (al bl : list BinomQueue.key),
 BinomQueue.priq p ->
 BinomQueue.Abs p al ->
 BinomQueue.Abs p bl -> @Permutation.Permutation BinomQueue.key al bl)).
idtac "Assumptions:".
Abort.
Print Assumptions BinomQueue.abs_perm.
Goal True.
idtac " ".

idtac "-------------------  can_relate  --------------------".
idtac " ".

idtac "#> BinomQueue.can_relate".
idtac "Possible points: 2".
check_type @BinomQueue.can_relate (
(forall p : BinomQueue.priqueue,
 BinomQueue.priq p -> exists al : list BinomQueue.key, BinomQueue.Abs p al)).
idtac "Assumptions:".
Abort.
Print Assumptions BinomQueue.can_relate.
Goal True.
idtac " ".

idtac "-------------------  empty_relate  --------------------".
idtac " ".

idtac "#> BinomQueue.empty_relate".
idtac "Possible points: 1".
check_type @BinomQueue.empty_relate (
(BinomQueue.Abs BinomQueue.empty (@nil BinomQueue.key))).
idtac "Assumptions:".
Abort.
Print Assumptions BinomQueue.empty_relate.
Goal True.
idtac " ".

idtac "-------------------  smash_elems  --------------------".
idtac " ".

idtac "#> BinomQueue.smash_elems".
idtac "Possible points: 3".
check_type @BinomQueue.smash_elems (
(forall (n : nat) (t u : BinomQueue.tree) (bt bu : list BinomQueue.key),
 BinomQueue.pow2heap n t ->
 BinomQueue.pow2heap n u ->
 BinomQueue.tree_elems t bt ->
 BinomQueue.tree_elems u bu ->
 BinomQueue.tree_elems (BinomQueue.smash t u) (bt ++ bu))).
idtac "Assumptions:".
Abort.
Print Assumptions BinomQueue.smash_elems.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 23".
idtac "Max points - advanced: 23".
idtac "".
idtac "Allowed Axioms:".
idtac "functional_extensionality".
idtac "functional_extensionality_dep".
idtac "FunctionalExtensionality.functional_extensionality_dep".
idtac "int".
idtac "Abs".
idtac "Abs_inj".
idtac "ltb".
idtac "ltb_lt".
idtac "leb".
idtac "leb_le".
idtac "Extract.int".
idtac "Extract.Abs".
idtac "Extract.Abs_inj".
idtac "Extract.ltb".
idtac "Extract.ltb_lt".
idtac "Extract.leb".
idtac "Extract.leb_le".
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
idtac "---------- BinomQueue.empty_priq ---------".
Print Assumptions BinomQueue.empty_priq.
idtac "---------- BinomQueue.smash_valid ---------".
Print Assumptions BinomQueue.smash_valid.
idtac "---------- BinomQueue.carry_valid ---------".
Print Assumptions BinomQueue.carry_valid.
idtac "---------- priqueue_elems ---------".
idtac "MANUAL".
idtac "---------- BinomQueue.tree_elems_ext ---------".
Print Assumptions BinomQueue.tree_elems_ext.
idtac "---------- BinomQueue.tree_perm ---------".
Print Assumptions BinomQueue.tree_perm.
idtac "---------- BinomQueue.priqueue_elems_ext ---------".
Print Assumptions BinomQueue.priqueue_elems_ext.
idtac "---------- BinomQueue.abs_perm ---------".
Print Assumptions BinomQueue.abs_perm.
idtac "---------- BinomQueue.can_relate ---------".
Print Assumptions BinomQueue.can_relate.
idtac "---------- BinomQueue.empty_relate ---------".
Print Assumptions BinomQueue.empty_relate.
idtac "---------- BinomQueue.smash_elems ---------".
Print Assumptions BinomQueue.smash_elems.
idtac "".
idtac "********** Advanced **********".
Abort.

(* 2020-08-07 17:10 *)
