Require Import Lists.
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

Require Import Lists.
Import Check.

Require Export Induction.
Module TestNatList.
Import NatList.
Goal True.
idtac "Entering exercise snd_fst_is_swap (standard): 1 point".
Abort.
Import NatList.
Goal True.
idtac " ".

idtac "#> NatList.snd_fst_is_swap".
check_type @NatList.snd_fst_is_swap (forall (p : natprod), (snd p, fst p) = swap_pair p).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.snd_fst_is_swap.
Goal True.
idtac " ".

idtac "Exiting exercise (snd_fst_is_swap)".
idtac " ".

idtac "Entering exercise list_funs (standard): 2 points".
Abort.
Import NatList.
Goal True.
idtac " ".

idtac "#> NatList.nonzeros".
check_type @NatList.nonzeros (forall (l : natlist), natlist).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.nonzeros.
Goal True.
idtac " ".

idtac "#> NatList.test_nonzeros".
check_type @NatList.test_nonzeros (nonzeros[0 ; 1 ; 0 ; 2 ; 3 ; 0 ; 0] = [1 ; 2 ; 3]).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.test_nonzeros.
Goal True.
idtac " ".

idtac "#> NatList.oddmembers".
check_type @NatList.oddmembers (forall (l : natlist), natlist).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.oddmembers.
Goal True.
idtac " ".

idtac "#> NatList.test_oddmembers".
check_type @NatList.test_oddmembers (oddmembers[0 ; 1 ; 0 ; 2 ; 3 ; 0 ; 0] = [1 ; 3]).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.test_oddmembers.
Goal True.
idtac " ".

idtac "#> NatList.countoddmembers".
check_type @NatList.countoddmembers (forall (l : natlist), nat).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.countoddmembers.
Goal True.
idtac " ".

idtac "#> NatList.test_countoddmembers1".
check_type @NatList.test_countoddmembers1 (countoddmembers[1 ; 0 ; 3 ; 1 ; 4 ; 5] = 4).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.test_countoddmembers1.
Goal True.
idtac " ".

idtac "#> NatList.test_countoddmembers2".
check_type @NatList.test_countoddmembers2 (countoddmembers[0 ; 2 ; 4] = 0).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.test_countoddmembers2.
Goal True.
idtac " ".

idtac "#> NatList.test_countoddmembers3".
check_type @NatList.test_countoddmembers3 (countoddmembers nil = 0).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.test_countoddmembers3.
Goal True.
idtac " ".

idtac "Exiting exercise (list_funs)".
idtac " ".

idtac "Entering exercise alternate (advanced): 3 points".
Abort.
Import NatList.
Goal True.
idtac " ".

idtac "#> NatList.alternate".
check_type @NatList.alternate (forall (l1 l2 : natlist), natlist).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.alternate.
Goal True.
idtac " ".

idtac "#> NatList.test_alternate1".
check_type @NatList.test_alternate1 (alternate[1 ; 2 ; 3][4 ; 5 ; 6] = [1 ; 4 ; 2 ; 5 ; 3 ; 6]).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.test_alternate1.
Goal True.
idtac " ".

idtac "#> NatList.test_alternate2".
check_type @NatList.test_alternate2 (alternate[1][4 ; 5 ; 6] = [1 ; 4 ; 5 ; 6]).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.test_alternate2.
Goal True.
idtac " ".

idtac "#> NatList.test_alternate3".
check_type @NatList.test_alternate3 (alternate[1 ; 2 ; 3][4] = [1 ; 4 ; 2 ; 3]).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.test_alternate3.
Goal True.
idtac " ".

idtac "#> NatList.test_alternate4".
check_type @NatList.test_alternate4 (alternate[][20 ; 30] = [20 ; 30]).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.test_alternate4.
Goal True.
idtac " ".

idtac "Exiting exercise (alternate)".
idtac " ".

idtac "Entering exercise bag_functions (standard): 3 points".
Abort.
Import NatList.
Goal True.
idtac " ".

idtac "#> NatList.count".
check_type @NatList.count (forall (v : nat) (s : bag), nat).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.count.
Goal True.
idtac " ".

idtac "#> NatList.test_count1".
check_type @NatList.test_count1 (count 1[1 ; 2 ; 3 ; 1 ; 4 ; 1] = 3).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.test_count1.
Goal True.
idtac " ".

idtac "#> NatList.test_count2".
check_type @NatList.test_count2 (count 6[1 ; 2 ; 3 ; 1 ; 4 ; 1] = 0).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.test_count2.
Goal True.
idtac " ".

idtac "#> NatList.sum".
check_type @NatList.sum (bag -> bag -> bag).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.sum.
Goal True.
idtac " ".

idtac "#> NatList.test_sum1".
check_type @NatList.test_sum1 (count 1(sum[1 ; 2 ; 3][1 ; 4 ; 1]) = 3).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.test_sum1.
Goal True.
idtac " ".

idtac "#> NatList.add".
check_type @NatList.add (forall (v : nat) (s : bag), bag).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.add.
Goal True.
idtac " ".

idtac "#> NatList.test_add1".
check_type @NatList.test_add1 (count 1(add 1[1 ; 4 ; 1]) = 3).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.test_add1.
Goal True.
idtac " ".

idtac "#> NatList.test_add2".
check_type @NatList.test_add2 (count 5(add 1[1 ; 4 ; 1]) = 0).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.test_add2.
Goal True.
idtac " ".

idtac "#> NatList.member".
check_type @NatList.member (forall (v : nat) (s : bag), bool).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.member.
Goal True.
idtac " ".

idtac "#> NatList.test_member1".
check_type @NatList.test_member1 (member 1[1 ; 4 ; 1] = true).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.test_member1.
Goal True.
idtac " ".

idtac "#> NatList.test_member2".
check_type @NatList.test_member2 (member 2[1 ; 4 ; 1] = false).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.test_member2.
Goal True.
idtac " ".

idtac "Exiting exercise (bag_functions)".
idtac " ".

idtac "Entering exercise bag_theorem (standard): 3 points".
Abort.
Import NatList.
Goal True.
idtac " ".

idtac "Manually graded.".
idtac " ".

idtac "Exiting exercise (bag_theorem)".
idtac " ".

idtac "Entering exercise list_exercises (standard): 3 points".
Abort.
Import NatList.
Goal True.
idtac " ".

idtac "Manually graded.".
idtac " ".

idtac "Exiting exercise (list_exercises)".
idtac " ".

idtac "Entering exercise beq_natlist (standard): 2 points".
Abort.
Import NatList.
Goal True.
idtac " ".

idtac "#> NatList.beq_natlist".
check_type @NatList.beq_natlist (forall (l1 l2 : natlist), bool).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.beq_natlist.
Goal True.
idtac " ".

idtac "#> NatList.test_beq_natlist1".
check_type @NatList.test_beq_natlist1 ((beq_natlist nil nil = true)).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.test_beq_natlist1.
Goal True.
idtac " ".

idtac "#> NatList.test_beq_natlist2".
check_type @NatList.test_beq_natlist2 (beq_natlist[1 ; 2 ; 3][1 ; 2 ; 3] = true).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.test_beq_natlist2.
Goal True.
idtac " ".

idtac "#> NatList.test_beq_natlist3".
check_type @NatList.test_beq_natlist3 (beq_natlist[1 ; 2 ; 3][1 ; 2 ; 4] = false).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.test_beq_natlist3.
Goal True.
idtac " ".

idtac "#> NatList.beq_natlist_refl".
check_type @NatList.beq_natlist_refl (forall l, true = beq_natlist l l).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.beq_natlist_refl.
Goal True.
idtac " ".

idtac "Exiting exercise (beq_natlist)".
idtac " ".

idtac "Entering exercise bag_proofs (advanced): 3 points".
Abort.
Import NatList.
Goal True.
idtac " ".

idtac "#> NatList.count_member_nonzero".
check_type @NatList.count_member_nonzero (forall (s : bag), leb 1(count 1(1 :: s)) = true).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.count_member_nonzero.
Goal True.
idtac " ".

idtac "#> NatList.remove_decreases_count".
check_type @NatList.remove_decreases_count (forall (s : bag), leb(count 0(remove_one 0 s))(count 0 s) = true).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.remove_decreases_count.
Goal True.
idtac " ".

idtac "Exiting exercise (bag_proofs)".
idtac " ".

idtac "Entering exercise rev_injective (advanced): 4 points".
Abort.
Import NatList.
Goal True.
idtac " ".

idtac "Manually graded.".
idtac " ".

idtac "Exiting exercise (rev_injective)".
idtac " ".

idtac "Entering exercise hd_error (standard): 2 points".
Abort.
Import NatList.
Goal True.
idtac " ".

idtac "#> NatList.hd_error".
check_type @NatList.hd_error (forall (l : natlist), natoption).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.hd_error.
Goal True.
idtac " ".

idtac "#> NatList.test_hd_error1".
check_type @NatList.test_hd_error1 (hd_error[] = None).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.test_hd_error1.
Goal True.
idtac " ".

idtac "#> NatList.test_hd_error2".
check_type @NatList.test_hd_error2 (hd_error[1] = Some 1).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.test_hd_error2.
Goal True.
idtac " ".

idtac "#> NatList.test_hd_error3".
check_type @NatList.test_hd_error3 (hd_error[5 ; 6] = Some 5).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.test_hd_error3.
Goal True.
idtac " ".

idtac "Exiting exercise (hd_error)".
idtac " ".
Abort.

End TestNatList.
Goal True.
idtac "Entering exercise beq_id_refl (standard): 1 point".
idtac " ".

idtac "#> beq_id_refl".
check_type @beq_id_refl (forall x, true = beq_id x x).
idtac "Assumptions:".
Abort.
Print Assumptions beq_id_refl.
Goal True.
idtac " ".

idtac "Exiting exercise (beq_id_refl)".
idtac " ".
Abort.

Module TestPartialMap.
Import PartialMap.
Export NatList.
Goal True.
idtac "Entering exercise update_eq (standard): 1 point".
Abort.
Import PartialMap.
Goal True.
idtac " ".

idtac "#> PartialMap.update_eq".
check_type @PartialMap.update_eq (forall (d : partial_map) (x : id) (v : nat), find x(update d x v) = Some v).
idtac "Assumptions:".
Abort.
Print Assumptions PartialMap.update_eq.
Goal True.
idtac " ".

idtac "Exiting exercise (update_eq)".
idtac " ".

idtac "Entering exercise update_neq (standard): 1 point".
Abort.
Import PartialMap.
Goal True.
idtac " ".

idtac "#> PartialMap.update_neq".
check_type @PartialMap.update_neq (forall (d : partial_map) (x y : id) (o : nat), beq_id x y = false -> find x(update d y o) = find x d).
idtac "Assumptions:".
Abort.
Print Assumptions PartialMap.update_neq.
Goal True.
idtac " ".

idtac "Exiting exercise (update_neq)".
idtac " ".
Abort.

End TestPartialMap.
Goal True.
idtac "Entering exercise baz_num_elts (standard): 2 points".
idtac " ".

idtac "Manually graded.".
idtac " ".

idtac "Exiting exercise (baz_num_elts)".
idtac " ".

idtac "Max points - regular: 21".
idtac "Max points - advanced: 31".
Abort.
