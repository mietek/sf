Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From VFA Require Import Trie.

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

From VFA Require Import Trie.
Import Check.

Goal True.

idtac "-------------------  succ_correct  --------------------".
idtac " ".

idtac "#> Integers.succ_correct".
idtac "Possible points: 2".
check_type @Integers.succ_correct (
(forall p : Integers.positive,
 Integers.positive2nat (Integers.succ p) = S (Integers.positive2nat p))).
idtac "Assumptions:".
Abort.
Print Assumptions Integers.succ_correct.
Goal True.
idtac " ".

idtac "-------------------  addc_correct  --------------------".
idtac " ".

idtac "#> Integers.addc_correct".
idtac "Possible points: 3".
check_type @Integers.addc_correct (
(forall (c : bool) (p q : Integers.positive),
 Integers.positive2nat (Integers.addc c p q) =
 (if c then 1 else 0) + Integers.positive2nat p + Integers.positive2nat q)).
idtac "Assumptions:".
Abort.
Print Assumptions Integers.addc_correct.
Goal True.
idtac " ".

idtac "-------------------  compare_correct  --------------------".
idtac " ".

idtac "#> Integers.compare_correct".
idtac "Possible points: 10".
check_type @Integers.compare_correct (
(forall x y : Integers.positive,
 match Integers.compare x y with
 | Integers.Eq => Integers.positive2nat x = Integers.positive2nat y
 | Integers.Lt => Integers.positive2nat x < Integers.positive2nat y
 | Integers.Gt => Integers.positive2nat x > Integers.positive2nat y
 end)).
idtac "Assumptions:".
Abort.
Print Assumptions Integers.compare_correct.
Goal True.
idtac " ".

idtac "-------------------  successor_of_Z_constant_time  --------------------".
idtac " ".

idtac "#> Manually graded: successor_of_Z_constant_time".
idtac "Possible points: 2".
print_manual_grade manual_grade_for_successor_of_Z_constant_time.
idtac " ".

idtac "-------------------  look_leaf  --------------------".
idtac " ".

idtac "#> look_leaf".
idtac "Possible points: 1".
check_type @look_leaf (
(forall (A : Type) (a : A) (j : BinNums.positive), @look A a j (@Leaf A) = a)).
idtac "Assumptions:".
Abort.
Print Assumptions look_leaf.
Goal True.
idtac " ".

idtac "-------------------  look_ins_same  --------------------".
idtac " ".

idtac "#> look_ins_same".
idtac "Possible points: 2".
check_type @look_ins_same (
(forall (A : Type) (a : A) (k : BinNums.positive) (v : A) (t : trie A),
 @look A a k (@ins A a k v t) = v)).
idtac "Assumptions:".
Abort.
Print Assumptions look_ins_same.
Goal True.
idtac " ".

idtac "-------------------  look_ins_same  --------------------".
idtac " ".

idtac "#> look_ins_same".
idtac "Possible points: 3".
check_type @look_ins_same (
(forall (A : Type) (a : A) (k : BinNums.positive) (v : A) (t : trie A),
 @look A a k (@ins A a k v t) = v)).
idtac "Assumptions:".
Abort.
Print Assumptions look_ins_same.
Goal True.
idtac " ".

idtac "-------------------  pos2nat_bijective  --------------------".
idtac " ".

idtac "#> pos2nat_injective".
idtac "Possible points: 1".
check_type @pos2nat_injective (
(forall p q : BinNums.positive, pos2nat p = pos2nat q -> p = q)).
idtac "Assumptions:".
Abort.
Print Assumptions pos2nat_injective.
Goal True.
idtac " ".

idtac "#> nat2pos_injective".
idtac "Possible points: 1".
check_type @nat2pos_injective ((forall i j : nat, nat2pos i = nat2pos j -> i = j)).
idtac "Assumptions:".
Abort.
Print Assumptions nat2pos_injective.
Goal True.
idtac " ".

idtac "-------------------  is_trie  --------------------".
idtac " ".

idtac "#> is_trie".
idtac "Possible points: 2".
check_type @is_trie ((forall A : Type, trie_table A -> Prop)).
idtac "Assumptions:".
Abort.
Print Assumptions is_trie.
Goal True.
idtac " ".

idtac "-------------------  empty_relate  --------------------".
idtac " ".

idtac "#> empty_relate".
idtac "Possible points: 2".
check_type @empty_relate (
(forall (A : Type) (default : A),
 @Abs A (@empty A default) (@Maps.t_empty A default))).
idtac "Assumptions:".
Abort.
Print Assumptions empty_relate.
Goal True.
idtac " ".

idtac "-------------------  lookup_relate  --------------------".
idtac " ".

idtac "#> lookup_relate".
idtac "Possible points: 2".
check_type @lookup_relate (
(forall (A : Type) (i : BinNums.positive) (t : trie_table A)
   (m : Maps.total_map A),
 @is_trie A t -> @Abs A t m -> @lookup A i t = m (pos2nat i))).
idtac "Assumptions:".
Abort.
Print Assumptions lookup_relate.
Goal True.
idtac " ".

idtac "-------------------  insert_relate  --------------------".
idtac " ".

idtac "#> insert_relate".
idtac "Possible points: 3".
check_type @insert_relate (
(forall (A : Type) (k : BinNums.positive) (v : A) 
   (t : trie_table A) (cts : Maps.total_map A),
 @is_trie A t ->
 @Abs A t cts ->
 @Abs A (@insert A k v t) (@Maps.t_update A cts (pos2nat k) v))).
idtac "Assumptions:".
Abort.
Print Assumptions insert_relate.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 34".
idtac "Max points - advanced: 34".
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
idtac "---------- Integers.succ_correct ---------".
Print Assumptions Integers.succ_correct.
idtac "---------- Integers.addc_correct ---------".
Print Assumptions Integers.addc_correct.
idtac "---------- Integers.compare_correct ---------".
Print Assumptions Integers.compare_correct.
idtac "---------- successor_of_Z_constant_time ---------".
idtac "MANUAL".
idtac "---------- look_leaf ---------".
Print Assumptions look_leaf.
idtac "---------- look_ins_same ---------".
Print Assumptions look_ins_same.
idtac "---------- look_ins_same ---------".
Print Assumptions look_ins_same.
idtac "---------- pos2nat_injective ---------".
Print Assumptions pos2nat_injective.
idtac "---------- nat2pos_injective ---------".
Print Assumptions nat2pos_injective.
idtac "---------- is_trie ---------".
Print Assumptions is_trie.
idtac "---------- empty_relate ---------".
Print Assumptions empty_relate.
idtac "---------- lookup_relate ---------".
Print Assumptions lookup_relate.
idtac "---------- insert_relate ---------".
Print Assumptions insert_relate.
idtac "".
idtac "********** Advanced **********".
Abort.

(* 2020-08-07 17:10 *)
