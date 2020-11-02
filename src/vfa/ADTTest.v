Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From VFA Require Import ADT.

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

From VFA Require Import ADT.
Import Check.

Goal True.

idtac "-------------------  lists_table  --------------------".
idtac " ".

idtac "#> StringListsTableExamples.StringListsTable.get_empty_default".
idtac "Possible points: 0.5".
check_type @StringListsTableExamples.StringListsTable.get_empty_default (
(forall k : StringListsTableExamples.StringListsTable.key,
 StringListsTableExamples.StringListsTable.get k
   StringListsTableExamples.StringListsTable.empty =
 StringListsTableExamples.StringListsTable.default)).
idtac "Assumptions:".
Abort.
Print Assumptions StringListsTableExamples.StringListsTable.get_empty_default.
Goal True.
idtac " ".

idtac "#> StringListsTableExamples.StringListsTable.get_set_same".
idtac "Possible points: 0.5".
check_type @StringListsTableExamples.StringListsTable.get_set_same (
(forall (k : StringListsTableExamples.StringListsTable.key)
   (v : StringListsTableExamples.StringListsTable.V)
   (t : StringListsTableExamples.StringListsTable.table),
 StringListsTableExamples.StringListsTable.get k
   (StringListsTableExamples.StringListsTable.set k v t) = v)).
idtac "Assumptions:".
Abort.
Print Assumptions StringListsTableExamples.StringListsTable.get_set_same.
Goal True.
idtac " ".

idtac "#> StringListsTableExamples.StringListsTable.get_set_other".
idtac "Possible points: 0.5".
check_type @StringListsTableExamples.StringListsTable.get_set_other (
(forall (k k' : StringListsTableExamples.StringListsTable.key)
   (v : StringListsTableExamples.StringListsTable.V)
   (t : StringListsTableExamples.StringListsTable.table),
 k <> k' ->
 StringListsTableExamples.StringListsTable.get k'
   (StringListsTableExamples.StringListsTable.set k v t) =
 StringListsTableExamples.StringListsTable.get k' t)).
idtac "Assumptions:".
Abort.
Print Assumptions StringListsTableExamples.StringListsTable.get_set_other.
Goal True.
idtac " ".

idtac "#> StringListsTableExamples.ex1".
idtac "Possible points: 0.5".
check_type @StringListsTableExamples.ex1 (
(StringListsTableExamples.StringListsTable.get 0
   StringListsTableExamples.StringListsTable.empty = String.EmptyString)).
idtac "Assumptions:".
Abort.
Print Assumptions StringListsTableExamples.ex1.
Goal True.
idtac " ".

idtac "#> StringListsTableExamples.ex2".
idtac "Possible points: 0.5".
check_type @StringListsTableExamples.ex2 (
(StringListsTableExamples.StringListsTable.get 0
   (StringListsTableExamples.StringListsTable.set 0
      (String.String
         (Ascii.Ascii true false false false false false true false)
         String.EmptyString) StringListsTableExamples.StringListsTable.empty) =
 String.String (Ascii.Ascii true false false false false false true false)
   String.EmptyString)).
idtac "Assumptions:".
Abort.
Print Assumptions StringListsTableExamples.ex2.
Goal True.
idtac " ".

idtac "#> StringListsTableExamples.ex3".
idtac "Possible points: 0.5".
check_type @StringListsTableExamples.ex3 (
(StringListsTableExamples.StringListsTable.get 1
   (StringListsTableExamples.StringListsTable.set 0
      (String.String
         (Ascii.Ascii true false false false false false true false)
         String.EmptyString) StringListsTableExamples.StringListsTable.empty) =
 String.EmptyString)).
idtac "Assumptions:".
Abort.
Print Assumptions StringListsTableExamples.ex3.
Goal True.
idtac " ".

idtac "-------------------  list_etable_abs  --------------------".
idtac " ".

idtac "#> StringListETableAbs.empty_ok".
idtac "Possible points: 0.5".
check_type @StringListETableAbs.empty_ok (
(StringListETableAbs.rep_ok StringListETableAbs.empty)).
idtac "Assumptions:".
Abort.
Print Assumptions StringListETableAbs.empty_ok.
Goal True.
idtac " ".

idtac "#> StringListETableAbs.set_ok".
idtac "Possible points: 0.5".
check_type @StringListETableAbs.set_ok (
(forall (k : StringListETableAbs.key) (v : StringListETableAbs.V)
   (t : StringListETableAbs.table),
 StringListETableAbs.rep_ok t ->
 StringListETableAbs.rep_ok (StringListETableAbs.set k v t))).
idtac "Assumptions:".
Abort.
Print Assumptions StringListETableAbs.set_ok.
Goal True.
idtac " ".

idtac "#> StringListETableAbs.empty_relate".
idtac "Possible points: 0.5".
check_type @StringListETableAbs.empty_relate (
(StringListETableAbs.Abs StringListETableAbs.empty =
 @empty_map StringListETableAbs.V)).
idtac "Assumptions:".
Abort.
Print Assumptions StringListETableAbs.empty_relate.
Goal True.
idtac " ".

idtac "#> StringListETableAbs.bound_relate".
idtac "Possible points: 0.5".
check_type @StringListETableAbs.bound_relate (
(forall (t : StringListETableAbs.table) (k : StringListETableAbs.key),
 StringListETableAbs.rep_ok t ->
 @SearchTree.map_bound StringListETableAbs.V k (StringListETableAbs.Abs t) =
 StringListETableAbs.bound k t)).
idtac "Assumptions:".
Abort.
Print Assumptions StringListETableAbs.bound_relate.
Goal True.
idtac " ".

idtac "#> StringListETableAbs.lookup_relate".
idtac "Possible points: 1.5".
check_type @StringListETableAbs.lookup_relate (
(forall (t : StringListETableAbs.table) (k : StringListETableAbs.key),
 StringListETableAbs.rep_ok t ->
 @map_find StringVal.V StringListETableAbs.default k
   (StringListETableAbs.Abs t) = StringListETableAbs.get k t)).
idtac "Assumptions:".
Abort.
Print Assumptions StringListETableAbs.lookup_relate.
Goal True.
idtac " ".

idtac "#> StringListETableAbs.insert_relate".
idtac "Possible points: 1.5".
check_type @StringListETableAbs.insert_relate (
(forall (t : StringListETableAbs.table) (k : StringListETableAbs.key)
   (v : StringListETableAbs.V),
 StringListETableAbs.rep_ok t ->
 @map_update StringListETableAbs.V k v (StringListETableAbs.Abs t) =
 StringListETableAbs.Abs (StringListETableAbs.set k v t))).
idtac "Assumptions:".
Abort.
Print Assumptions StringListETableAbs.insert_relate.
Goal True.
idtac " ".

idtac "#> StringListETableAbs.elements_relate".
idtac "Possible points: 1".
check_type @StringListETableAbs.elements_relate (
(forall t : StringListETableAbs.table,
 StringListETableAbs.rep_ok t ->
 StringListETableAbs.Abs t =
 @SearchTree.map_of_list StringListETableAbs.V
   (StringListETableAbs.elements t))).
idtac "Assumptions:".
Abort.
Print Assumptions StringListETableAbs.elements_relate.
Goal True.
idtac " ".

idtac "-------------------  list_queue  --------------------".
idtac " ".

idtac "#> ListQueue.is_empty_empty".
idtac "Possible points: 0.5".
check_type @ListQueue.is_empty_empty ((ListQueue.is_empty ListQueue.empty = true)).
idtac "Assumptions:".
Abort.
Print Assumptions ListQueue.is_empty_empty.
Goal True.
idtac " ".

idtac "#> ListQueue.is_empty_nonempty".
idtac "Possible points: 0.5".
check_type @ListQueue.is_empty_nonempty (
(forall (q : ListQueue.queue) (v : ListQueue.V),
 ListQueue.is_empty (ListQueue.enq q v) = false)).
idtac "Assumptions:".
Abort.
Print Assumptions ListQueue.is_empty_nonempty.
Goal True.
idtac " ".

idtac "#> ListQueue.peek_empty".
idtac "Possible points: 0.5".
check_type @ListQueue.peek_empty (
(forall d : ListQueue.V, ListQueue.peek d ListQueue.empty = d)).
idtac "Assumptions:".
Abort.
Print Assumptions ListQueue.peek_empty.
Goal True.
idtac " ".

idtac "#> ListQueue.peek_nonempty".
idtac "Possible points: 0.5".
check_type @ListQueue.peek_nonempty (
(forall (d : ListQueue.V) (q : ListQueue.queue) (v : ListQueue.V),
 ListQueue.peek d (ListQueue.enq q v) = ListQueue.peek v q)).
idtac "Assumptions:".
Abort.
Print Assumptions ListQueue.peek_nonempty.
Goal True.
idtac " ".

idtac "#> ListQueue.deq_empty".
idtac "Possible points: 0.5".
check_type @ListQueue.deq_empty ((ListQueue.deq ListQueue.empty = ListQueue.empty)).
idtac "Assumptions:".
Abort.
Print Assumptions ListQueue.deq_empty.
Goal True.
idtac " ".

idtac "#> ListQueue.deq_nonempty".
idtac "Possible points: 0.5".
check_type @ListQueue.deq_nonempty (
(forall (q : ListQueue.queue) (v : ListQueue.V),
 ListQueue.deq (ListQueue.enq q v) =
 (if ListQueue.is_empty q then q else ListQueue.enq (ListQueue.deq q) v))).
idtac "Assumptions:".
Abort.
Print Assumptions ListQueue.deq_nonempty.
Goal True.
idtac " ".

idtac "-------------------  two_list_queue  --------------------".
idtac " ".

idtac "#> TwoListQueueAbs.empty_relate".
idtac "Possible points: 0.5".
check_type @TwoListQueueAbs.empty_relate (
(TwoListQueueAbs.Abs TwoListQueueAbs.empty = @nil TwoListQueueAbs.V)).
idtac "Assumptions:".
Abort.
Print Assumptions TwoListQueueAbs.empty_relate.
Goal True.
idtac " ".

idtac "#> TwoListQueueAbs.enq_relate".
idtac "Possible points: 0.5".
check_type @TwoListQueueAbs.enq_relate (
(forall (q : TwoListQueueAbs.queue) (v : TwoListQueueAbs.V),
 TwoListQueueAbs.Abs (TwoListQueueAbs.enq q v) =
 (TwoListQueueAbs.Abs q ++ v :: @nil TwoListQueueAbs.V)%list)).
idtac "Assumptions:".
Abort.
Print Assumptions TwoListQueueAbs.enq_relate.
Goal True.
idtac " ".

idtac "#> TwoListQueueAbs.peek_relate".
idtac "Possible points: 1".
check_type @TwoListQueueAbs.peek_relate (
(forall (d : TwoListQueueAbs.V) (q : TwoListQueueAbs.queue),
 TwoListQueueAbs.peek d q =
 @List.hd TwoListQueueAbs.V d (TwoListQueueAbs.Abs q))).
idtac "Assumptions:".
Abort.
Print Assumptions TwoListQueueAbs.peek_relate.
Goal True.
idtac " ".

idtac "#> TwoListQueueAbs.deq_relate".
idtac "Possible points: 1".
check_type @TwoListQueueAbs.deq_relate (
(forall q : TwoListQueueAbs.queue,
 TwoListQueueAbs.Abs (TwoListQueueAbs.deq q) =
 @List.tl TwoListQueueAbs.V (TwoListQueueAbs.Abs q))).
idtac "Assumptions:".
Abort.
Print Assumptions TwoListQueueAbs.deq_relate.
Goal True.
idtac " ".

idtac "-------------------  a_vector  --------------------".
idtac " ".

idtac "#> a_vector".
idtac "Possible points: 1".
check_type @a_vector ((vector nat)).
idtac "Assumptions:".
Abort.
Print Assumptions a_vector.
Goal True.
idtac " ".

idtac "-------------------  vector_cons_correct  --------------------".
idtac " ".

idtac "#> vector_cons_correct".
idtac "Possible points: 2".
check_type @vector_cons_correct (
(forall (X : Type) (x : X) (v : vector X),
 @list_of_vector X (@vector_cons X x v) = (x :: @list_of_vector X v)%list)).
idtac "Assumptions:".
Abort.
Print Assumptions vector_cons_correct.
Goal True.
idtac " ".

idtac "-------------------  vector_app_correct  --------------------".
idtac " ".

idtac "#> vector_app_correct".
idtac "Possible points: 2".
check_type @vector_app_correct (
(forall (X : Type) (v1 v2 : vector X),
 @list_of_vector X (@vector_app X v1 v2) =
 (@list_of_vector X v1 ++ @list_of_vector X v2)%list)).
idtac "Assumptions:".
Abort.
Print Assumptions vector_app_correct.
Goal True.
idtac " ".

idtac "-------------------  ListsETable  --------------------".
idtac " ".

idtac "#> Manually graded: ListsETable".
idtac "Advanced".
idtac "Possible points: 6".
print_manual_grade manual_grade_for_ListsETable.
idtac " ".

idtac " ".

idtac "Max points - standard: 20".
idtac "Max points - advanced: 26".
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
idtac "---------- StringListsTableExamples.StringListsTable.get_empty_default ---------".
Print Assumptions StringListsTableExamples.StringListsTable.get_empty_default.
idtac "---------- StringListsTableExamples.StringListsTable.get_set_same ---------".
Print Assumptions StringListsTableExamples.StringListsTable.get_set_same.
idtac "---------- StringListsTableExamples.StringListsTable.get_set_other ---------".
Print Assumptions StringListsTableExamples.StringListsTable.get_set_other.
idtac "---------- StringListsTableExamples.ex1 ---------".
Print Assumptions StringListsTableExamples.ex1.
idtac "---------- StringListsTableExamples.ex2 ---------".
Print Assumptions StringListsTableExamples.ex2.
idtac "---------- StringListsTableExamples.ex3 ---------".
Print Assumptions StringListsTableExamples.ex3.
idtac "---------- StringListETableAbs.empty_ok ---------".
Print Assumptions StringListETableAbs.empty_ok.
idtac "---------- StringListETableAbs.set_ok ---------".
Print Assumptions StringListETableAbs.set_ok.
idtac "---------- StringListETableAbs.empty_relate ---------".
Print Assumptions StringListETableAbs.empty_relate.
idtac "---------- StringListETableAbs.bound_relate ---------".
Print Assumptions StringListETableAbs.bound_relate.
idtac "---------- StringListETableAbs.lookup_relate ---------".
Print Assumptions StringListETableAbs.lookup_relate.
idtac "---------- StringListETableAbs.insert_relate ---------".
Print Assumptions StringListETableAbs.insert_relate.
idtac "---------- StringListETableAbs.elements_relate ---------".
Print Assumptions StringListETableAbs.elements_relate.
idtac "---------- ListQueue.is_empty_empty ---------".
Print Assumptions ListQueue.is_empty_empty.
idtac "---------- ListQueue.is_empty_nonempty ---------".
Print Assumptions ListQueue.is_empty_nonempty.
idtac "---------- ListQueue.peek_empty ---------".
Print Assumptions ListQueue.peek_empty.
idtac "---------- ListQueue.peek_nonempty ---------".
Print Assumptions ListQueue.peek_nonempty.
idtac "---------- ListQueue.deq_empty ---------".
Print Assumptions ListQueue.deq_empty.
idtac "---------- ListQueue.deq_nonempty ---------".
Print Assumptions ListQueue.deq_nonempty.
idtac "---------- TwoListQueueAbs.empty_relate ---------".
Print Assumptions TwoListQueueAbs.empty_relate.
idtac "---------- TwoListQueueAbs.enq_relate ---------".
Print Assumptions TwoListQueueAbs.enq_relate.
idtac "---------- TwoListQueueAbs.peek_relate ---------".
Print Assumptions TwoListQueueAbs.peek_relate.
idtac "---------- TwoListQueueAbs.deq_relate ---------".
Print Assumptions TwoListQueueAbs.deq_relate.
idtac "---------- a_vector ---------".
Print Assumptions a_vector.
idtac "---------- vector_cons_correct ---------".
Print Assumptions vector_cons_correct.
idtac "---------- vector_app_correct ---------".
Print Assumptions vector_app_correct.
idtac "".
idtac "********** Advanced **********".
idtac "---------- ListsETable ---------".
idtac "MANUAL".
Abort.

(* 2020-08-07 17:08 *)
