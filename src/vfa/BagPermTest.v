Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From VFA Require Import BagPerm.

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

From VFA Require Import BagPerm.
Import Check.

Goal True.

idtac "-------------------  bag_eqv_properties  --------------------".
idtac " ".

idtac "#> bag_eqv_refl".
idtac "Possible points: 0.5".
check_type @bag_eqv_refl ((forall b : bag, bag_eqv b b)).
idtac "Assumptions:".
Abort.
Print Assumptions bag_eqv_refl.
Goal True.
idtac " ".

idtac "#> bag_eqv_sym".
idtac "Possible points: 0.5".
check_type @bag_eqv_sym ((forall b1 b2 : bag, bag_eqv b1 b2 -> bag_eqv b2 b1)).
idtac "Assumptions:".
Abort.
Print Assumptions bag_eqv_sym.
Goal True.
idtac " ".

idtac "#> bag_eqv_trans".
idtac "Possible points: 0.5".
check_type @bag_eqv_trans (
(forall b1 b2 b3 : bag, bag_eqv b1 b2 -> bag_eqv b2 b3 -> bag_eqv b1 b3)).
idtac "Assumptions:".
Abort.
Print Assumptions bag_eqv_trans.
Goal True.
idtac " ".

idtac "#> bag_eqv_cons".
idtac "Possible points: 0.5".
check_type @bag_eqv_cons (
(forall (x : nat) (b1 b2 : bag),
 bag_eqv b1 b2 -> bag_eqv (x :: b1)%list (x :: b2)%list)).
idtac "Assumptions:".
Abort.
Print Assumptions bag_eqv_cons.
Goal True.
idtac " ".

idtac "-------------------  insert_bag  --------------------".
idtac " ".

idtac "#> insert_bag".
idtac "Possible points: 3".
check_type @insert_bag (
(forall (x : nat) (l : list nat), bag_eqv (x :: l)%list (Sort.insert x l))).
idtac "Assumptions:".
Abort.
Print Assumptions insert_bag.
Goal True.
idtac " ".

idtac "-------------------  sort_bag  --------------------".
idtac " ".

idtac "#> sort_bag".
idtac "Possible points: 2".
check_type @sort_bag ((forall l : bag, bag_eqv l (Sort.sort l))).
idtac "Assumptions:".
Abort.
Print Assumptions sort_bag.
Goal True.
idtac " ".

idtac "-------------------  permutations_vs_multiset  --------------------".
idtac " ".

idtac "#> Manually graded: permutations_vs_multiset".
idtac "Possible points: 1".
print_manual_grade manual_grade_for_permutations_vs_multiset.
idtac " ".

idtac "-------------------  perm_bag  --------------------".
idtac " ".

idtac "#> perm_bag".
idtac "Possible points: 3".
check_type @perm_bag (
(forall al bl : list nat, @Permutation.Permutation nat al bl -> bag_eqv al bl)).
idtac "Assumptions:".
Abort.
Print Assumptions perm_bag.
Goal True.
idtac " ".

idtac "-------------------  bag_nil_inv  --------------------".
idtac " ".

idtac "#> bag_nil_inv".
idtac "Advanced".
idtac "Possible points: 2".
check_type @bag_nil_inv ((forall b : bag, bag_eqv (@nil nat) b -> b = @nil nat)).
idtac "Assumptions:".
Abort.
Print Assumptions bag_nil_inv.
Goal True.
idtac " ".

idtac "-------------------  bag_cons_inv  --------------------".
idtac " ".

idtac "#> bag_cons_inv".
idtac "Advanced".
idtac "Possible points: 3".
check_type @bag_cons_inv (
(forall (l : bag) (x n : nat),
 S n = count x l ->
 exists l1 l2 : list nat,
   l = (l1 ++ x :: l2)%list /\ count x (l1 ++ l2)%list = n)).
idtac "Assumptions:".
Abort.
Print Assumptions bag_cons_inv.
Goal True.
idtac " ".

idtac "-------------------  count_insert_other  --------------------".
idtac " ".

idtac "#> count_insert_other".
idtac "Advanced".
idtac "Possible points: 2".
check_type @count_insert_other (
(forall (l1 l2 : list nat) (x y : nat),
 y <> x -> count y (l1 ++ x :: l2)%list = count y (l1 ++ l2)%list)).
idtac "Assumptions:".
Abort.
Print Assumptions count_insert_other.
Goal True.
idtac " ".

idtac "-------------------  bag_perm  --------------------".
idtac " ".

idtac "#> bag_perm".
idtac "Advanced".
idtac "Possible points: 3".
check_type @bag_perm (
(forall al bl : bag, bag_eqv al bl -> @Permutation.Permutation nat al bl)).
idtac "Assumptions:".
Abort.
Print Assumptions bag_perm.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 11".
idtac "Max points - advanced: 21".
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
idtac "---------- bag_eqv_refl ---------".
Print Assumptions bag_eqv_refl.
idtac "---------- bag_eqv_sym ---------".
Print Assumptions bag_eqv_sym.
idtac "---------- bag_eqv_trans ---------".
Print Assumptions bag_eqv_trans.
idtac "---------- bag_eqv_cons ---------".
Print Assumptions bag_eqv_cons.
idtac "---------- insert_bag ---------".
Print Assumptions insert_bag.
idtac "---------- sort_bag ---------".
Print Assumptions sort_bag.
idtac "---------- permutations_vs_multiset ---------".
idtac "MANUAL".
idtac "---------- perm_bag ---------".
Print Assumptions perm_bag.
idtac "".
idtac "********** Advanced **********".
idtac "---------- bag_nil_inv ---------".
Print Assumptions bag_nil_inv.
idtac "---------- bag_cons_inv ---------".
Print Assumptions bag_cons_inv.
idtac "---------- count_insert_other ---------".
Print Assumptions count_insert_other.
idtac "---------- bag_perm ---------".
Print Assumptions bag_perm.
Abort.

(* 2020-08-07 17:08 *)
