(** * Records: Adding Records to STLC *)

Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Strings.String.
From PLF Require Import Maps.
From PLF Require Import Smallstep.
From PLF Require Import Stlc.

(* ################################################################# *)
(** * Adding Records *)

(** We saw in chapter [MoreStlc] how records can be treated as just
    syntactic sugar for nested uses of products.  This is OK for
    simple examples, but the encoding is informal (in reality, if we
    actually treated records this way, it would be carried out in the
    parser, which we are eliding here), and anyway it is not very
    efficient.  So it is also interesting to see how records can be
    treated as first-class citizens of the language.  This chapter
    shows how.

    Recall the informal definitions we gave before: *)

(**
    Syntax:
<{
       t ::=                          Terms:
           | {i=t, ..., i=t}             record
           | t.i                         projection
           | ...

       v ::=                          Values:
           | {i=v, ..., i=v}             record value
           | ...

       T ::=                          Types:
           | {i:T, ..., i:T}             record type
           | ...
}>
   Reduction:

                               ti ==> ti'
  -------------------------------------------------------------------- (ST_Rcd)
  {i1=v1, ..., im=vm, in=tn, ...} ==> {i1=v1, ..., im=vm, in=tn', ...}

                                 t1 ==> t1'
                               --------------                        (ST_Proj1)
                               t1.i ==> t1'.i

                          -------------------------                (ST_ProjRcd)
                          {..., i=vi, ...}.i ==> vi

   Typing:

               Gamma |- t1 : T1     ...     Gamma |- tn : Tn
             --------------------------------------------------         (T_Rcd)
             Gamma |- {i1=t1, ..., in=tn} : {i1:T1, ..., in:Tn}

                       Gamma |- t0 : {..., i:Ti, ...}
                       ------------------------------                   (T_Proj)
                             Gamma |- t0.i : Ti
*)

(* ################################################################# *)
(** * Formalizing Records *)

Module STLCExtendedRecords.

(* ----------------------------------------------------------------- *)
(** *** Syntax and Operational Semantics *)

(** The most obvious way to formalize the syntax of record types would
    be this: *)

Module FirstTry.

Definition alist (X : Type) := list (string * X).

Inductive ty : Type :=
  | Base     : string -> ty
  | Arrow    : ty -> ty -> ty
  | TRcd     : (alist ty) -> ty.

(** Unfortunately, we encounter here a limitation in Coq: this type
    does not automatically give us the induction principle we expect:
    the induction hypothesis in the [TRcd] case doesn't give us
    any information about the [ty] elements of the list, making it
    useless for the proofs we want to do.  *)

(* Check ty_ind.
   ====>
    ty_ind :
      forall P : ty -> Prop,
        (forall i : id, P (Base i)) ->
        (forall t : ty, P t -> forall t0 : ty, P t0
                            -> P (Arrow t t0)) ->
        (forall a : alist ty, P (TRcd a)) ->    (* ??? *)
        forall t : ty, P t
*)

End FirstTry.

(** It is possible to get a better induction principle out of Coq, but
    the details of how this is done are not very pretty, and the
    principle we obtain is not as intuitive to use as the ones Coq
    generates automatically for simple [Inductive] definitions.

    Fortunately, there is a different way of formalizing records that
    is, in some ways, even simpler and more natural: instead of using
    the standard Coq [list] type, we can essentially incorporate its
    constructors ("nil" and "cons") in the syntax of our types. *)

Inductive ty : Type :=
  | Ty_Base : string -> ty
  | Ty_Arrow : ty -> ty -> ty
  | Ty_RNil : ty
  | Ty_RCons : string -> ty -> ty -> ty.

(** Similarly, at the level of terms, we have constructors [trnil],
    for the empty record, and [rcons], which adds a single field to
    the front of a list of fields. *)

Inductive tm : Type :=
  | tm_var : string -> tm
  | tm_app : tm -> tm -> tm
  | tm_abs : string -> ty -> tm -> tm
  (* records *)
  | tm_rproj : tm -> string -> tm
  | tm_rnil :  tm
  | tm_rcons : string -> tm -> tm -> tm.

Declare Custom Entry stlc_ty.

Notation "<{ e }>" := e (e custom stlc at level 99).
Notation "<{{ e }}>" := e (e custom stlc_ty at level 99).
Notation "( x )" := x (in custom stlc, x at level 99).
Notation "( x )" := x (in custom stlc_ty, x at level 99).
Notation "x" := x (in custom stlc at level 0, x constr at level 0).
Notation "x" := x (in custom stlc_ty at level 0, x constr at level 0).
Notation "S -> T" := (Ty_Arrow S T) (in custom stlc_ty at level 50, right associativity).
Notation "x y" := (tm_app x y) (in custom stlc at level 1, left associativity).
Notation "\ x : t , y" :=
  (tm_abs x t y) (in custom stlc at level 90, x at level 99,
                     t custom stlc_ty at level 99,
                     y custom stlc at level 99,
                     left associativity).
Coercion tm_var : string >-> tm.

Notation "{ x }" := x (in custom stlc at level 1, x constr).

Notation "'Base' x" := (Ty_Base x) (in custom stlc_ty at level 0).

Notation "  l ':' t1  '::' t2" := (Ty_RCons l t1 t2) (in custom stlc_ty at level 3, right associativity).
Notation " l := e1 '::' e2" := (tm_rcons l e1 e2) (in custom stlc at level 3, right associativity).
Notation "'nil'" := (Ty_RNil) (in custom stlc_ty).
Notation "'nil'" := (tm_rnil) (in custom stlc).
Notation "o --> l" := (tm_rproj o l) (in custom stlc at level 0).

(** Some examples... *)
Open Scope string_scope.

Notation a := "a".
Notation f := "f".
Notation g := "g".
Notation l := "l".
Notation A := <{{ Base "A" }}>.
Notation B := <{{ Base "B" }}>.
Notation k := "k".
Notation i1 := "i1".
Notation i2 := "i2".

(** [{ i1:A }] *)

(* Check (RCons i1 A RNil). *)

(** [{ i1:A->B, i2:A }] *)

(* Check (RCons i1 (Arrow A B)
           (RCons i2 A RNil)). *)

(* ----------------------------------------------------------------- *)
(** *** Well-Formedness *)

(** One issue with generalizing the abstract syntax for records from
    lists to the nil/cons presentation is that it introduces the
    possibility of writing strange types like this... *)

Definition weird_type := <{{  a : A  :: B }}>.

(** where the "tail" of a record type is not actually a record type! *)

(** We'll structure our typing judgement so that no ill-formed types
    like [weird_type] are ever assigned to terms.  To support this, we
    define predicates [record_ty] and [record_tm], which identify
    record types and terms, and [well_formed_ty] which rules out the
    ill-formed types. *)

(** First, a type is a record type if it is built with just [RNil]
    and [RCons] at the outermost level. *)

Inductive record_ty : ty -> Prop :=
  | RTnil :
        record_ty <{{ nil }}>
  | RTcons : forall i T1 T2,
        record_ty <{{ i : T1 :: T2 }}>.

(** With this, we can define well-formed types. *)

Inductive well_formed_ty : ty -> Prop :=
  | wfBase : forall (i : string),
        well_formed_ty <{{ Base i }}>
  | wfArrow : forall T1 T2,
        well_formed_ty T1 ->
        well_formed_ty T2 ->
        well_formed_ty <{{ T1 -> T2 }}>
  | wfRNil :
        well_formed_ty <{{ nil }}>
  | wfRCons : forall i T1 T2,
        well_formed_ty T1 ->
        well_formed_ty T2 ->
        record_ty T2 ->
        well_formed_ty <{{ i : T1 :: T2 }}>.

Hint Constructors record_ty well_formed_ty : core.

(** Note that [record_ty] is not recursive -- it just checks the
    outermost constructor.  The [well_formed_ty] property, on the
    other hand, verifies that the whole type is well formed in the
    sense that the tail of every record (the second argument to
    [RCons]) is a record.

    Of course, we should also be concerned about ill-formed terms, not
    just types; but typechecking can rule those out without the help
    of an extra [well_formed_tm] definition because it already
    examines the structure of terms.  All we need is an analog of
    [record_ty] saying that a term is a record term if it is built
    with [trnil] and [rcons]. *)

Inductive record_tm : tm -> Prop :=
  | rtnil :
        record_tm <{ nil }>
  | rtcons : forall i t1 t2,
        record_tm <{ i := t1 :: t2 }>.

Hint Constructors record_tm : core.

(* ----------------------------------------------------------------- *)
(** *** Substitution *)

(** Substitution extends easily. *)

Reserved Notation "'[' x ':=' s ']' t" (in custom stlc at level 20, x constr).

Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | tm_var y =>
      if eqb_string x y then s else t
  | <{\y:T, t1}> =>
      if eqb_string x y then t else <{\y:T, [x:=s] t1}>
  | <{t1 t2}> =>
      <{([x:=s] t1) ([x:=s] t2)}>
  | <{ t1 --> i }> =>
      <{ ( [x := s] t1) --> i }>
  | <{ nil }> =>
      <{ nil }>
  | <{ i := t1 :: tr }> =>
     <{ i :=  [x := s] t1 :: ( [x := s] tr) }>
  end

where "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc).

(* ----------------------------------------------------------------- *)
(** *** Reduction *)

(** A record is a value if all of its fields are. *)

Inductive value : tm -> Prop :=
  | v_abs : forall x T2 t1,
      value  <{ \ x : T2, t1 }>
  | v_rnil : value <{ nil }>
  | v_rcons : forall i v1 vr,
      value v1 ->
      value vr ->
      value <{ i := v1 :: vr }>.

Hint Constructors value : core.

(** To define reduction, we'll need a utility function for extracting
    one field from record term: *)

Fixpoint tlookup (i:string) (tr:tm) : option tm :=
  match tr with
  | <{ i' := t :: tr'}> => if eqb_string i i' then Some t else tlookup i tr'
  | _ => None
  end.

(** The [step] function uses this term-level lookup function in the
    projection rule. *)

Reserved Notation "t '-->' t'" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T2 t1 v2,
         value v2 ->
         <{(\x:T2, t1) v2}> --> <{ [x:=v2]t1 }>
  | ST_App1 : forall t1 t1' t2,
         t1 --> t1' ->
         <{t1 t2}> --> <{t1' t2}>
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         <{v1 t2}> --> <{v1  t2'}>
  | ST_Proj1 : forall t1 t1' i,
        t1 --> t1' ->
        <{ t1 --> i }> --> <{ t1' --> i }>
  | ST_ProjRcd : forall tr i vi,
        value tr ->
        tlookup i tr = Some vi ->
        <{ tr --> i }> --> vi
  | ST_Rcd_Head : forall i t1 t1' tr2,
        t1 --> t1' ->
        <{ i := t1 :: tr2 }> --> <{ i := t1' :: tr2 }>
  | ST_Rcd_Tail : forall i v1 tr2 tr2',
        value v1 ->
        tr2 --> tr2' ->
        <{ i := v1 :: tr2 }> --> <{ i := v1 :: tr2' }>

where "t '-->' t'" := (step t t').

Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

Hint Constructors step : core.

(* ----------------------------------------------------------------- *)
(** *** Typing *)

(** Next we define the typing rules.  These are nearly direct
    transcriptions of the inference rules shown above: the only
    significant difference is the use of [well_formed_ty].  In the
    informal presentation we used a grammar that only allowed
    well-formed record types, so we didn't have to add a separate
    check.

    One sanity condition that we'd like to maintain is that, whenever
    [has_type Gamma t T] holds, will also be the case that
    [well_formed_ty T], so that [has_type] never assigns ill-formed
    types to terms.  In fact, we prove this theorem below.  However,
    we don't want to clutter the definition of [has_type] with
    unnecessary uses of [well_formed_ty].  Instead, we place
    [well_formed_ty] checks only where needed: where an inductive call
    to [has_type] won't already be checking the well-formedness of a
    type.  For example, we check [well_formed_ty T] in the [T_Var]
    case, because there is no inductive [has_type] call that would
    enforce this.  Similarly, in the [T_Abs] case, we require a proof
    of [well_formed_ty T11] because the inductive call to [has_type]
    only guarantees that [T12] is well-formed. *)

Fixpoint Tlookup (i:string) (Tr:ty) : option ty :=
  match Tr with
  | <{{ i' : T :: Tr' }}> =>
      if eqb_string i i' then Some T else Tlookup i Tr'
  | _ => None
  end.

Definition context := partial_map ty.

Reserved Notation "Gamma '|-' t '\in' T" (at level 40,
                                          t custom stlc, T custom stlc_ty at level 0).

Inductive has_type (Gamma : context) :tm -> ty -> Prop :=
  | T_Var : forall x T,
      Gamma x = Some T ->
      well_formed_ty T ->
      Gamma |- x \in T
  | T_Abs : forall x T11 T12 t12,
      well_formed_ty T11 ->
      (x |-> T11; Gamma) |- t12 \in T12 ->
      Gamma |- \x : T11, t12 \in (T11 -> T12)
  | T_App : forall T1 T2 t1 t2,
      Gamma |- t1 \in (T1 -> T2) ->
      Gamma |- t2 \in T1 ->
      Gamma |- ( t1 t2) \in T2
  (* records: *)
  | T_Proj : forall i t Ti Tr,
      Gamma |- t \in Tr ->
      Tlookup i Tr = Some Ti ->
      Gamma |- (t --> i) \in Ti
 | T_RNil :
      Gamma |- nil \in nil
  | T_RCons : forall i t T tr Tr,
      Gamma |- t \in T ->
      Gamma |- tr \in Tr ->
      record_ty Tr ->
      record_tm tr ->
      Gamma |- ( i := t :: tr) \in ( i : T :: Tr)

where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Hint Constructors has_type : core.

(* ================================================================= *)
(** ** Examples *)

(** **** Exercise: 2 stars, standard (examples) 

    Finish the proofs below.  Feel free to use Coq's automation
    features in this proof.  However, if you are not confident about
    how the type system works, you may want to carry out the proofs
    first using the basic features ([apply] instead of [eapply], in
    particular) and then perhaps compress it using automation.  Before
    starting to prove anything, make sure you understand what it is
    saying. *)

Lemma typing_example_2 :
  empty |- (\a : ( i1 : (A -> A) :: i2 : (B -> B) :: nil), a --> i2)
            ( i1 := (\a : A, a) :: i2 := (\a : B,a ) :: nil )  \in (B -> B).
Proof.
  (* FILL IN HERE *) Admitted.

Example typing_nonexample :
  ~ exists T,
     (a |-> <{{  i2 : (A -> A) :: nil   }}>) |-
       ( i1 := (\a : B, a) :: a ) \in
               T.
Proof.
  (* FILL IN HERE *) Admitted.

Example typing_nonexample_2 : forall y,
  ~ exists T,
    (y |-> A) |-
     (\a : ( i1 : A  :: nil ), a --> i1 )
      ( i1 := y :: i2 := y :: nil )  \in T.
Proof.
  (* FILL IN HERE *) Admitted.

(* ================================================================= *)
(** ** Properties of Typing *)

(** The proofs of progress and preservation for this system are
    essentially the same as for the pure simply typed lambda-calculus,
    but we need to add some technical lemmas involving records. *)

(* ----------------------------------------------------------------- *)
(** *** Well-Formedness *)

Lemma wf_rcd_lookup : forall i T Ti,
  well_formed_ty T ->
  Tlookup i T = Some Ti ->
  well_formed_ty Ti.
Proof with eauto.
  intros i T.
  induction T; intros; try solve_by_invert.
  - (* RCons *)
    inversion H. subst. unfold Tlookup in H0.
    destruct (eqb_string i s)...
    inversion H0. subst...  Qed.

Lemma step_preserves_record_tm : forall tr tr',
  record_tm tr ->
  tr --> tr' ->
  record_tm tr'.
Proof.
  intros tr tr' Hrt Hstp.
  inversion Hrt; subst; inversion Hstp; subst; auto.
Qed.

Lemma has_type__wf : forall Gamma t T,
  Gamma |- t \in T -> well_formed_ty T.
Proof with eauto.
  intros Gamma t T Htyp.
  induction Htyp...
  - (* T_App *)
    inversion IHHtyp1...
  - (* T_Proj *)
    eapply wf_rcd_lookup...
Qed.

(* ----------------------------------------------------------------- *)
(** *** Field Lookup *)

(** Lemma: If [empty |- v : T] and [Tlookup i T] returns [Some Ti],
     then [tlookup i v] returns [Some ti] for some term [ti] such
     that [empty |- ti \in Ti].

    Proof: By induction on the typing derivation [Htyp].  Since
      [Tlookup i T = Some Ti], [T] must be a record type, this and
      the fact that [v] is a value eliminate most cases by inspection,
      leaving only the [T_RCons] case.

      If the last step in the typing derivation is by [T_RCons], then
      [t = rcons i0 t tr] and [T = RCons i0 T Tr] for some [i0],
      [t], [tr], [T] and [Tr].

      This leaves two possiblities to consider - either [i0 = i] or
      not.

      - If [i = i0], then since [Tlookup i (RCons i0 T Tr) = Some
        Ti] we have [T = Ti].  It follows that [t] itself satisfies
        the theorem.

      - On the other hand, suppose [i <> i0].  Then

        Tlookup i T = Tlookup i Tr

        and

        tlookup i t = tlookup i tr,

        so the result follows from the induction hypothesis. []

    Here is the formal statement:
*)

Lemma lookup_field_in_value : forall v T i Ti,
  value v ->
  empty |- v \in T ->
  Tlookup i T = Some Ti ->
  exists ti, tlookup i v = Some ti /\ empty |- ti \in Ti.
Proof with eauto.
  intros v T i Ti Hval Htyp Hget.
  remember empty as Gamma.
  induction Htyp; subst; try solve_by_invert...
  - (* T_RCons *)
    simpl in Hget. simpl. destruct (eqb_string i i0).
    + (* i is first *)
      simpl. injection Hget as Hget. subst.
      exists t...
    + (* get tail *)
      destruct IHHtyp2 as [vi [Hgeti Htypi] ]...
      inversion Hval... Qed.

(* ----------------------------------------------------------------- *)
(** *** Progress *)

Theorem progress : forall t T,
     empty |- t \in T ->
     value t \/ exists t', t --> t'.
Proof with eauto.
  (* Theorem: Suppose empty |- t : T.  Then either
       1. t is a value, or
       2. t --> t' for some t'.
     Proof: By induction on the given typing derivation. *)
  intros t T Ht.
  remember empty as Gamma.
  generalize dependent HeqGamma.
  induction Ht; intros HeqGamma; subst.
  - (* T_Var *)
    (* The final rule in the given typing derivation cannot be
       [T_Var], since it can never be the case that
       [empty |- x : T] (since the context is empty). *)
    inversion H.
  - (* T_Abs *)
    (* If the [T_Abs] rule was the last used, then
       [t = abs x T11 t12], which is a value. *)
    left...
  - (* T_App *)
    (* If the last rule applied was T_App, then [t = t1 t2],
       and we know from the form of the rule that
         [empty |- t1 : T1 -> T2]
         [empty |- t2 : T1]
       By the induction hypothesis, each of t1 and t2 either is a value
       or can take a step. *)
    right.
    destruct IHHt1; subst...
    + (* t1 is a value *)
      destruct IHHt2; subst...
      * (* t2 is a value *)
      (* If both [t1] and [t2] are values, then we know that
         [t1 = abs x T11 t12], since abstractions are the only
         values that can have an arrow type.  But
         [(abs x T11 t12) t2 --> [x:=t2]t12] by [ST_AppAbs]. *)
        inversion H; subst; try solve_by_invert.
        exists <{ [x:=t2]t0 }>...
      * (* t2 steps *)
        (* If [t1] is a value and [t2 --> t2'], then
           [t1 t2 --> t1 t2'] by [ST_App2]. *)
        destruct H0 as [t2' Hstp]. exists <{ t1 t2' }>...
    + (* t1 steps *)
      (* Finally, If [t1 --> t1'], then [t1 t2 --> t1' t2]
         by [ST_App1]. *)
      destruct H as [t1' Hstp]. exists <{ t1' t2 }>...
  - (* T_Proj *)
    (* If the last rule in the given derivation is [T_Proj], then
       [t = rproj t i] and
           [empty |- t : (TRcd Tr)]
       By the IH, [t] either is a value or takes a step. *)
    right. destruct IHHt...
    + (* rcd is value *)
      (* If [t] is a value, then we may use lemma
         [lookup_field_in_value] to show [tlookup i t = Some ti]
         for some [ti] which gives us [rproj i t --> ti] by
         [ST_ProjRcd]. *)
      destruct (lookup_field_in_value _ _ _ _ H0 Ht H)
        as [ti [Hlkup _] ].
      exists ti...
    + (* rcd_steps *)
      (* On the other hand, if [t --> t'], then
         [rproj t i --> rproj t' i] by [ST_Proj1]. *)
      destruct H0 as [t' Hstp]. exists <{ t' --> i }>...
  - (* T_RNil *)
    (* If the last rule in the given derivation is [T_RNil],
       then [t = trnil], which is a value. *)
    left...
  - (* T_RCons *)
    (* If the last rule is [T_RCons], then [t = rcons i t tr] and
         [empty |- t : T]
         [empty |- tr : Tr]
       By the IH, each of [t] and [tr] either is a value or can
       take a step. *)
    destruct IHHt1...
    + (* head is a value *)
      destruct IHHt2; try reflexivity.
      * (* tail is a value *)
      (* If [t] and [tr] are both values, then [rcons i t tr]
         is a value as well. *)
        left...
      * (* tail steps *)
        (* If [t] is a value and [tr --> tr'], then
           [rcons i t tr --> rcons i t tr'] by
           [ST_Rcd_Tail]. *)
        right. destruct H2 as [tr' Hstp].
        exists <{ i := t :: tr'}>...
    + (* head steps *)
      (* If [t --> t'], then
         [rcons i t tr --> rcons i t' tr]
         by [ST_Rcd_Head]. *)
      right. destruct H1 as [t' Hstp].
      exists <{ i := t' :: tr }>...  Qed.

(* ================================================================= *)
(** ** Weakening *)

(** The weakening lemma is proved as in pure STLC. *)

Lemma weakening : forall Gamma Gamma' t T,
     inclusion Gamma Gamma' ->
     Gamma  |- t \in T  ->
     Gamma' |- t \in T.
Proof.
  intros Gamma Gamma' t T H Ht.
  generalize dependent Gamma'.
  induction Ht; eauto using inclusion_update.
Qed.

Lemma weakening_empty : forall Gamma t T,
     empty |- t \in T  ->
     Gamma |- t \in T.
Proof.
  intros Gamma t T.
  eapply weakening.
  discriminate.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Preservation *)

  (* As before, we prove the substitution lemma by induction
     on the term t. The only new case (compared to the proof in
     StlcProp.v) is the case of rcons. For this case, we must do a little
     extra work to show that substituting into a term doesn't change
     whetherit is a record term. *)

Lemma substitution_preserves_typing : forall Gamma x U t v T,
  (x |-> U ; Gamma) |- t \in T ->
  empty |- v \in U   ->
  Gamma |- [x:=v]t \in T.
Proof.
  intros Gamma x U t v T Ht Hv.
  generalize dependent Gamma. generalize dependent T.
  induction t; intros T Gamma H;
  (* in each case, we'll want to get at the derivation of H *)
    inversion H; clear H; subst; simpl; eauto.
  - (* var *)
    rename s into y. destruct (eqb_stringP x y); subst.
    + (* x=y *)
      rewrite update_eq in H1.
      injection H1 as H1; subst.
      apply weakening_empty. assumption.
    + (* x<>y *)
      apply T_Var. rewrite update_neq in H1; auto. assumption.
  - (* abs *)
    rename s into y, t into T.
    destruct (eqb_stringP x y); subst; apply T_Abs; try assumption.
    + (* x=y *)
      rewrite update_shadow in H5. assumption.
    + (* x<>y *)
      apply IHt.
      rewrite update_permute; auto.
  - (* rcons *)   (* <=== only new case compared to pure STLC *)
     apply T_RCons; eauto.
     inversion H7; subst; simpl; auto.
Qed.

Theorem preservation : forall t t' T,
  empty |- t \in T  ->
  t --> t'  ->
  empty |- t' \in T.
Proof with eauto.
  intros t t' T HT. generalize dependent t'.
  remember empty as Gamma.
  induction HT;
       intros t' HE; subst;
       try solve [inversion HE; subst; auto].
  - (* T_App *)
    inversion HE; subst...
    + (* ST_AppAbs *)
      apply substitution_preserves_typing with T1...
      inversion HT1...
  - (* T_Proj *) (* <=== new case compared to pure STLC *)
    (* If the last rule was [T_Proj], then [t = rproj t1 i].
       Two rules could have caused [t --> t']: [T_Proj1] and
       [T_ProjRcd].  The typing of [t'] follows from the IH
       in the former case, so we only consider [T_ProjRcd].

       Here we have that [t] is a record value.  Since rule
       [T_Proj] was used, we know [empty |- t \in Tr] and
       [Tlookup i Tr = Some Ti] for some [i] and [Tr].
       We may therefore apply lemma [lookup_field_in_value]
       to find the record element this projection steps to. *)
    inversion HE; subst...
    destruct (lookup_field_in_value _ _ _ _ H2 HT H)
      as [vi [Hget Htyp] ].
    rewrite H4 in Hget. injection Hget as Hget. subst...
  - (* T_RCons *) (* <=== new case compared to pure STLC *)
    (* If the last rule was [T_RCons], then [t = rcons i t tr]
       for some [i], [t] and [tr] such that [record_tm tr].  If
       the step is by [ST_Rcd_Head], the result is immediate by
       the IH.  If the step is by [ST_Rcd_Tail], [tr --> tr2']
       for some [tr2'] and we must also use lemma [step_preserves_record_tm]
       to show [record_tm tr2']. *)
    inversion HE; subst...
    apply T_RCons... eapply step_preserves_record_tm...
Qed.
(** [] *)

End STLCExtendedRecords.

(* 2020-09-09 21:08 *)
