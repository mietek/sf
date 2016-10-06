(** * Typechecking: A Typechecker for STLC *)

(** The [has_type] relation of the STLC defines what it means for a
    term to belong to a type (in some context).  But it doesn't, by
    itself, tell us how to _check_ whether or not a term is well
    typed.

    Fortunately, the rules defining [has_type] are _syntax directed_
    -- they exactly follow the shape of the term.  This makes it
    straightforward to translate the typing rules into clauses of a
    typechecking _function_ that takes a term and a context and either
    returns the term's type or else signals that the term is not
    typable.  This short chapter constructs such a function and proves
    it correct. *)

Require Import Coq.Bool.Bool.
Require Import Maps.
Require Import Smallstep.
Require Import Stlc.

Module STLCChecker.
Import STLC.

(* ================================================================= *)
(** ** Comparing Types *)

(** First, we need a function to compare two types for equality... *)

Fixpoint beq_ty (T1 T2:ty) : bool :=
  match T1,T2 with
  | TBool, TBool =>
      true
  | TArrow T11 T12, TArrow T21 T22 =>
      andb (beq_ty T11 T21) (beq_ty T12 T22)
  | _,_ =>
      false
  end.

(** ... and we need to establish the usual two-way connection between
    the boolean result returned by [beq_ty] and the logical
    proposition that its inputs are equal. *)

Lemma beq_ty_refl : forall T1,
  beq_ty T1 T1 = true.
Proof.
  intros T1. induction T1; simpl.
    reflexivity.
    rewrite IHT1_1. rewrite IHT1_2. reflexivity.  Qed.

Lemma beq_ty__eq : forall T1 T2,
  beq_ty T1 T2 = true -> T1 = T2.
Proof with auto.
  intros T1. induction T1; intros T2 Hbeq; destruct T2; inversion Hbeq.
  - (* T1=TBool *)
    reflexivity.
  - (* T1=TArrow T1_1 T1_2 *)
    rewrite andb_true_iff in H0. inversion H0 as [Hbeq1 Hbeq2].
    apply IHT1_1 in Hbeq1. apply IHT1_2 in Hbeq2. subst...  Qed.

(* ================================================================= *)
(** ** The Typechecker *)

(** The typechecker works by walking over the structure of the given
    term, returning either [Some T] or [None].  Each time we make a
    recursive call to find out the types of the subterms, we need to
    pattern-match on the results to make sure that they are not
    [None].  Also, in the [tapp] case, we use pattern matching to
    extract the left- and right-hand sides of the function's arrow
    type (and fail if the type of the function is not [TArrow T11 T12]
    for some [T1] and [T2]). *)

Fixpoint type_check (Gamma:context) (t:tm) : option ty :=
  match t with
  | tvar x => Gamma x
  | tabs x T11 t12 => match type_check (update Gamma x T11) t12 with
                          | Some T12 => Some (TArrow T11 T12)
                          | _ => None
                        end
  | tapp t1 t2 => match type_check Gamma t1, type_check Gamma t2 with
                      | Some (TArrow T11 T12),Some T2 =>
                        if beq_ty T11 T2 then Some T12 else None
                      | _,_ => None
                    end
  | ttrue => Some TBool
  | tfalse => Some TBool
  | tif x t f => match type_check Gamma x with
                     | Some TBool =>
                       match type_check Gamma t, type_check Gamma f with
                         | Some T1, Some T2 =>
                           if beq_ty T1 T2 then Some T1 else None
                         | _,_ => None
                       end
                     | _ => None
                   end
  end.

(* ================================================================= *)
(** ** Properties *)

(** To verify that this typechecking algorithm is correct, we show
    that it is _sound_ and _complete_ for the original [has_type]
    relation -- that is, [type_check] and [has_type] define the same
    partial function. *)

Theorem type_checking_sound : forall Gamma t T,
  type_check Gamma t = Some T -> has_type Gamma t T.
Proof with eauto.
  intros Gamma t. generalize dependent Gamma.
  induction t; intros Gamma T Htc; inversion Htc.
  - (* tvar *) eauto.
  - (* tapp *)
    remember (type_check Gamma t1) as TO1.
    remember (type_check Gamma t2) as TO2.
    destruct TO1 as [T1|]; try solve_by_invert;
    destruct T1 as [|T11 T12]; try solve_by_invert.
    destruct TO2 as [T2|]; try solve_by_invert.
    destruct (beq_ty T11 T2) eqn: Heqb;
    try solve_by_invert.
    apply beq_ty__eq in Heqb.
    inversion H0; subst...
  - (* tabs *)
    rename i into y. rename t into T1.
    remember (update Gamma y T1) as G'.
    remember (type_check G' t0) as TO2.
    destruct TO2; try solve_by_invert.
    inversion H0; subst...
  - (* ttrue *) eauto.
  - (* tfalse *) eauto.
  - (* tif *)
    remember (type_check Gamma t1) as TOc.
    remember (type_check Gamma t2) as TO1.
    remember (type_check Gamma t3) as TO2.
    destruct TOc as [Tc|]; try solve_by_invert.
    destruct Tc; try solve_by_invert.
    destruct TO1 as [T1|]; try solve_by_invert.
    destruct TO2 as [T2|]; try solve_by_invert.
    destruct (beq_ty T1 T2) eqn:Heqb;
    try solve_by_invert.
    apply beq_ty__eq in Heqb.
    inversion H0. subst. subst...
Qed.

Theorem type_checking_complete : forall Gamma t T,
  has_type Gamma t T -> type_check Gamma t = Some T.
Proof with auto.
  intros Gamma t T Hty.
  induction Hty; simpl.
  - (* T_Var *) eauto.
  - (* T_Abs *) rewrite IHHty...
  - (* T_App *)
    rewrite IHHty1. rewrite IHHty2.
    rewrite (beq_ty_refl T11)...
  - (* T_True *) eauto.
  - (* T_False *) eauto.
  - (* T_If *) rewrite IHHty1. rewrite IHHty2.
    rewrite IHHty3. rewrite (beq_ty_refl T)...
Qed.

End STLCChecker.

(** $Date: 2016-07-13 12:41:41 -0400 (Wed, 13 Jul 2016) $ *)
