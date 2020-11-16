Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From VFA Require Import Redblack.

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

From VFA Require Import Redblack.
Import Check.

Goal True.

idtac "-------------------  balanceP  --------------------".
idtac " ".

idtac "#> balanceP".
idtac "Possible points: 2".
check_type @balanceP (
(forall (V : Type) (P : key -> V -> Prop) (c : color) 
   (l r : tree V) (k : key) (v : V),
 ForallT V P l -> ForallT V P r -> P k v -> ForallT V P (balance V c l k v r))).
idtac "Assumptions:".
Abort.
Print Assumptions balanceP.
Goal True.
idtac " ".

idtac "-------------------  insP  --------------------".
idtac " ".

idtac "#> insP".
idtac "Possible points: 2".
check_type @insP (
(forall (V : Type) (P : key -> V -> Prop) (t : tree V) (k : key) (v : V),
 ForallT V P t -> P k v -> ForallT V P (ins V k v t))).
idtac "Assumptions:".
Abort.
Print Assumptions insP.
Goal True.
idtac " ".

idtac "-------------------  ins_BST  --------------------".
idtac " ".

idtac "#> ins_BST".
idtac "Possible points: 3".
check_type @ins_BST (
(forall (V : Type) (t : tree V) (k : key) (v : V),
 BST V t -> BST V (ins V k v t))).
idtac "Assumptions:".
Abort.
Print Assumptions ins_BST.
Goal True.
idtac " ".

idtac "-------------------  insert_BST  --------------------".
idtac " ".

idtac "#> insert_BST".
idtac "Possible points: 2".
check_type @insert_BST (
(forall (V : Type) (t : tree V) (v : V) (k : key),
 BST V t -> BST V (insert V k v t))).
idtac "Assumptions:".
Abort.
Print Assumptions insert_BST.
Goal True.
idtac " ".

idtac "-------------------  balance_lookup  --------------------".
idtac " ".

idtac "#> balance_lookup".
idtac "Possible points: 6".
check_type @balance_lookup (
(forall (V : Type) (default : V) (c : color) (k k' : key) 
   (v : V) (l r : tree V),
 BST V l ->
 BST V r ->
 ForallT V
   (fun (k'0 : Extract.int) (_ : V) =>
    BinInt.Z.lt (Extract.Abs k'0) (Extract.Abs k)) l ->
 ForallT V
   (fun (k'0 : Extract.int) (_ : V) =>
    BinInt.Z.gt (Extract.Abs k'0) (Extract.Abs k)) r ->
 lookup V default k' (balance V c l k v r) =
 (if BinInt.Z.ltb (Extract.Abs k') (Extract.Abs k)
  then lookup V default k' l
  else
   if BinInt.Z.gtb (Extract.Abs k') (Extract.Abs k)
   then lookup V default k' r
   else v))).
idtac "Assumptions:".
Abort.
Print Assumptions balance_lookup.
Goal True.
idtac " ".

idtac "-------------------  lookup_ins_eq  --------------------".
idtac " ".

idtac "#> lookup_ins_eq".
idtac "Possible points: 3".
check_type @lookup_ins_eq (
(forall (V : Type) (default : V) (t : tree V) (k : key) (v : V),
 BST V t -> lookup V default k (ins V k v t) = v)).
idtac "Assumptions:".
Abort.
Print Assumptions lookup_ins_eq.
Goal True.
idtac " ".

idtac "-------------------  lookup_ins_neq  --------------------".
idtac " ".

idtac "#> lookup_ins_neq".
idtac "Possible points: 3".
check_type @lookup_ins_neq (
(forall (V : Type) (default : V) (t : tree V) (k k' : key) (v : V),
 BST V t ->
 k <> k' -> lookup V default k' (ins V k v t) = lookup V default k' t)).
idtac "Assumptions:".
Abort.
Print Assumptions lookup_ins_neq.
Goal True.
idtac " ".

idtac "-------------------  lookup_insert  --------------------".
idtac " ".

idtac "#> lookup_insert_eq".
idtac "Possible points: 2".
check_type @lookup_insert_eq (
(forall (V : Type) (default : V) (t : tree V) (k : key) (v : V),
 BST V t -> lookup V default k (insert V k v t) = v)).
idtac "Assumptions:".
Abort.
Print Assumptions lookup_insert_eq.
Goal True.
idtac " ".

idtac "#> lookup_insert_neq".
idtac "Possible points: 1".
check_type @lookup_insert_neq (
(forall (V : Type) (default : V) (t : tree V) (k k' : key) (v : V),
 BST V t ->
 k <> k' -> lookup V default k' (insert V k v t) = lookup V default k' t)).
idtac "Assumptions:".
Abort.
Print Assumptions lookup_insert_neq.
Goal True.
idtac " ".

idtac "-------------------  RB_blacken_parent  --------------------".
idtac " ".

idtac "#> RB_blacken_parent".
idtac "Possible points: 2".
check_type @RB_blacken_parent (
(forall (V : Type) (t : tree V) (n : nat), RB V t Red n -> RB V t Black n)).
idtac "Assumptions:".
Abort.
Print Assumptions RB_blacken_parent.
Goal True.
idtac " ".

idtac "-------------------  RB_blacken_root  --------------------".
idtac " ".

idtac "#> RB_blacken_root".
idtac "Possible points: 2".
check_type @RB_blacken_root (
(forall (V : Type) (t : tree V) (n : nat),
 RB V t Black n -> exists n' : nat, RB V (make_black V t) Red n')).
idtac "Assumptions:".
Abort.
Print Assumptions RB_blacken_root.
Goal True.
idtac " ".

idtac "-------------------  ins_RB  --------------------".
idtac " ".

idtac "#> ins_RB".
idtac "Possible points: 10".
check_type @ins_RB (
(forall (V : Type) (k : key) (v : V) (t : tree V) (n : nat),
 (RB V t Black n -> NearlyRB V (ins V k v t) n) /\
 (RB V t Red n -> RB V (ins V k v t) Black n))).
idtac "Assumptions:".
Abort.
Print Assumptions ins_RB.
Goal True.
idtac " ".

idtac "-------------------  insert_RB  --------------------".
idtac " ".

idtac "#> insert_RB".
idtac "Possible points: 2".
check_type @insert_RB (
(forall (V : Type) (t : tree V) (k : key) (v : V) (n : nat),
 RB V t Red n -> exists n' : nat, RB V (insert V k v t) Red n')).
idtac "Assumptions:".
Abort.
Print Assumptions insert_RB.
Goal True.
idtac " ".

idtac "-------------------  redblack_bound  --------------------".
idtac " ".

idtac "#> Manually graded: redblack_bound".
idtac "Advanced".
idtac "Possible points: 6".
print_manual_grade manual_grade_for_redblack_bound.
idtac " ".

idtac " ".

idtac "Max points - standard: 40".
idtac "Max points - advanced: 46".
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
idtac "---------- balanceP ---------".
Print Assumptions balanceP.
idtac "---------- insP ---------".
Print Assumptions insP.
idtac "---------- ins_BST ---------".
Print Assumptions ins_BST.
idtac "---------- insert_BST ---------".
Print Assumptions insert_BST.
idtac "---------- balance_lookup ---------".
Print Assumptions balance_lookup.
idtac "---------- lookup_ins_eq ---------".
Print Assumptions lookup_ins_eq.
idtac "---------- lookup_ins_neq ---------".
Print Assumptions lookup_ins_neq.
idtac "---------- lookup_insert_eq ---------".
Print Assumptions lookup_insert_eq.
idtac "---------- lookup_insert_neq ---------".
Print Assumptions lookup_insert_neq.
idtac "---------- RB_blacken_parent ---------".
Print Assumptions RB_blacken_parent.
idtac "---------- RB_blacken_root ---------".
Print Assumptions RB_blacken_root.
idtac "---------- ins_RB ---------".
Print Assumptions ins_RB.
idtac "---------- insert_RB ---------".
Print Assumptions insert_RB.
idtac "".
idtac "********** Advanced **********".
idtac "---------- redblack_bound ---------".
idtac "MANUAL".
Abort.

(* 2020-08-07 17:10 *)
