(** * Verif_append2: Magic wand, partial data structure *)

(* ================================================================= *)
(** ** Separating Implication *)

(** Separating implication is another separation logic operator. It is 
 written as  [-*]  in  Verifiable C. Because of its shape, it is usually
 called "magic wand". The following [Locate] command and [Check] command
 show this notation definition and its typing information. *)

Require VC.Preface. (* Check for the right version of VST *)

Require Import VST.floyd.proofauto.

Locate "-*".
   (* Notation "P '-*' Q" := wand P Q : logic (default interpretation) *)
Check wand. (* : mpred -> mpred -> mpred *)

(** In separation logic, a heaplet (piece of memory) [m] satisfies [P -* Q]
  if and only if: for any possible heaplet [n], if [n] and [m] are disjoint
  and [n] satisfies [P], then the combination of [n] and [m] will satisfy [Q].

  The most important proof rule for separating implication is the adjoint
  property. It says, [P*Q] derives [R] if and only if [P] derives [Q-*R].
  This rule is called [wand_sepcon_adjoint] in Verifiable C. *)

Check wand_sepcon_adjoint.
  (* : forall P Q R : mpred, P * Q |-- R   <->   P |-- Q -* R *)

(** Because of this property, we also call [-*] a right adjoint of [*].
  In propositional logic, 
  implication [->] is a right adjoint of conjunction [/\].
 *)

Lemma implies_and_adjoint:
   forall P Q R : Prop, (P /\ Q -> R)  <->  (P -> (Q -> R)).
Proof. intuition. Qed.

(** This intrinsic similarity gives [-*] the name "separating implication".
  The following are two other important properties of [-*]; we can easily
  find their counterparts about propositional-logic "implication". *)

(** Proof rules for separating implication: *)

Check wand_derives.
  (* : forall P P' Q Q' : mpred,
       P' |-- P -> Q |-- Q' -> P -* Q |-- P' -* Q' *)

Check modus_ponens_wand.
  (*   : forall P Q : mpred, P * (P -* Q) |-- Q  *)

(** Now, we learn to use the adjoint property to prove other 
  separation-logic rules about [-*]. We will start from an easy one. *)

Lemma wand_trivial: forall P Q: mpred, P |-- Q -* (P * Q).
Proof.
  intros.
  rewrite <- wand_sepcon_adjoint.
  apply derives_refl.
Qed.

(** Then, we will reprove the modus ponens rule for [-*] and [*] from 
  the adjoint property. *)

Lemma modus_ponens_wand_from_adjoint: forall P Q : mpred, P * (P -* Q) |-- Q.
Proof.
  intros.
  rewrite sepcon_comm.
  rewrite -> wand_sepcon_adjoint.
  apply derives_refl.
Qed.

(** Now prove [wand_derives] using [wand_sepcon_adjoint] and
 [modus_ponens_wand]. You can use other proof rules about [*], such as
 [sepcon_derives].  Also, the tactic [sep_apply] may be useful. *)

(** **** Exercise: 2 stars, standard: (wand_derives) *)
Lemma wand_derives_from_adjoint_and_modus_ponens:
  forall P P' Q Q' : mpred, 
   P' |-- P  ->  Q |-- Q'  ->  P -* Q |-- P' -* Q'.
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

(** Theorem [wand_frame_ver] is the counterpart of implication's transitivity.
  As we will see, it allows "vertical composition" of wand frames.  *)

Check wand_frame_ver.
  (*   : forall P Q R : mpred, (P -* Q) * (Q -* R) |-- P -* R  *)

(** Prove it by [wand_sepcon_adjoint] and [sep_apply (modus_ponens_wand ...)] *)

(** **** Exercise: 2 stars, standard: (wand_frame_ver) *)
Lemma wand_frame_ver_from_adjoint_and_modus_ponens:
  forall P Q R : mpred, (P -* Q) * (Q -* R) |-- P -* R.
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

(** More exercises: prove that [emp -* emp] and [emp] are equivalent. *)

(** **** Exercise: 3 stars, standard: (emp_wand_emp) *)
Lemma emp_wand_emp_right: emp |-- emp -* emp.
Proof.
(* FILL IN HERE *) Admitted.

Lemma emp_wand_emp_left: emp -* emp |-- emp.
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** List segments by magic wand *)

Require Import VC.append.
Require Import VC.Verif_append1.

(** In [Verif_append1], we recursively defined a new separation logic
  predicate: list segment. That predicate describes a heaplet that contains
  a partial linked list.

  In this chapter, we learn a different way of describing partial data
  structures--we use magic wand together with quantifiers.

  This is a natural idea. Using linked lists as an example, adding a linked
  list to the tail of a partial linked list (or a list segment) will result
  in a complete linked list from the head. Thus, a partial linked list
  can be described by "the added list -* the complete list". Formally: *)

Definition wlseg (contents: list val) (x y: val) : mpred :=
  ALL tail: list val, listrep tail y -* listrep (contents ++ tail) x.

(** Here, "w" in "wlseg" represents "wand". 

   This definition is very different from [lseg] and is beautifully
   simple, and it generalizes nicely to other data structures such as trees.

   Let's prove some basic properties of [wlseg]. The following lemmas
   show how a wand expression can be introduced ([emp_wlseg] and
   [singleton_wlseg]), how a wand expression can be eliminated ([wlseg_list])
   and how two wand expressions can merge ([wlseg_wlseg]).

   There are two logical operators in this definition, [-*] and the
   universal quantifier. Previously, we have learned how to prove 
   properties about [*] and [-*].  To prove properties about universal 
   quantifiers, we will use [allp_left] and [allp_right]. *)

Check allp_left.
  (*  : forall (P : ?B -> mpred) (x : ?B) (Q : mpred),
       P x |-- Q -> ALL x : _ , P x |-- Q   *)
Check allp_right.
  (*  : forall (P : mpred) (Q : ?B -> mpred),
       (forall v : ?B, P |-- Q v) -> P |-- ALL x : _ , Q x  *)

(** The first property of [wlseg] is that we can introduce [wlseg] from
   [emp]. *)

Lemma emp_wlseg: forall (x: val),
  emp |-- wlseg [] x x.
Proof.
  intros.
  unfold wlseg.
  apply allp_right; intro tail.
  rewrite <- wand_sepcon_adjoint.
  rewrite emp_sepcon.
  simpl app.
  apply derives_refl.
Qed.

(** Next, we show that two [wlseg] predicates can be merged into one. *)

Lemma wlseg_wlseg: forall (s1 s2: list val) (x y z: val),
  wlseg s2 y z * wlseg s1 x y |-- wlseg (s1 ++ s2) x z.
Proof.
 intros.
 unfold wlseg.
 (** First, extract the universally quantified variable [tail] on 
    the right side. *)
 apply allp_right; intro tail.
 (** Next, instantiate the first quantified [tail0] on the left 
    with [tail]. *)
 rewrite -> wand_sepcon_adjoint.
 apply (allp_left _ tail).
 rewrite <- wand_sepcon_adjoint.
 (** Then, instantiate the other quantified [tail0] on the left 
    with [s2 ++ tail]. *)
 rewrite sepcon_comm, -> wand_sepcon_adjoint.
 apply (allp_left _ (s2 ++ tail)).
 rewrite <- wand_sepcon_adjoint, sepcon_comm.
 (** Finally, complete the proof with wand_frame_ver. *)
 rewrite <- app_assoc.
 apply wand_frame_ver.
Qed.

(** This theorem [wlseg_wlseg] shares the same form with [lseg_lseg].
 In fact, properties about [lseg] and [wlseg] are very similar. 
 The following exercises are to prove the counterparts of
 [singleton_lseg] and [lseg_list]. *)

(** **** Exercise: 2 stars, standard: (singleton_wlseg) *)
Lemma singleton_wlseg: forall (a: val) (x y: val),
  data_at Tsh t_list (a, y) x |-- wlseg [a] x y.
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard: (wlseg_list) *)
Lemma wlseg_list: forall (s1 s2: list val) (x y: val),
  wlseg s1 x y * listrep s2 y |-- listrep (s1 ++ s2) x.
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** Proof of the [append] function by [wlseg] *)

(** Now, we are ready to reprove the correctness for the C program [append].  
    This time, we will use [wlseg] to write the loop invariant. *)

(** **** Exercise: 3 stars, standard: (body_append_alter2) *)
Lemma body_append_alter2: semax_body Vprog Gprog f_append append_spec.
Proof.
start_function.
forward_if. (* if (x == NULL) *)
- (* If-then *)
  rewrite (listrep_null _ x) by auto.
  (* FILL IN HERE *) admit.
- (* If-else *)
  rewrite (listrep_nonnull _ x) by auto.
  Intros h r u.
  forward. (* t = x; *)
  forward. (* u = t -> tail; *)
  (** Here, we use [wlseg] to represent a list segment. *)
  forward_while
    (EX s1a: list val, EX b: val, EX s1c: list val, EX t: val, EX u: val,
       PROP (s1 = s1a ++ b :: s1c)
       LOCAL (temp _x x; temp _t t; temp _u u; temp _y y)
       SEP (wlseg s1a x t;
            data_at Tsh t_list (b, u) t;
            listrep s1c u;
            listrep s2 y))%assert.
 + (* current assertion implies loop invariant *)
   (** To derive a loop invariant from the current assertion, the key
     point is to introduce [wlseg]. You may find [emp_wlseg] helpful here. *)
  (* FILL IN HERE *) admit.
 + (* loop test is safe to execute *)
     entailer!.
 + (* loop body preserves invariant *)
   (** Step forward through the loop body; along the way you'll need to do
  other transformations on the current assertion, to uncover opportunities
  to step [forward]. At the end of the loop body, you need to prove that a
  list segment for [s1a] and a singleton cell for [b] forms a longer list
  segment, whose contents is [s1a ++ b :: nil]. You may find
  [singleton_wlseg] and [wlseg_wlseg] useful there. *)
  (* FILL IN HERE *) admit.
 + (* after the loop *)
   (** After you symbolicly execute the return command, you need to establish
    one single linked list with contents [s1a ++ b :: s2] from a list segment
    for [s1a], a singleton cell for [b] and another linked list for [s2].
    You may find [singleton_wlseg] and [wlseg_list] useful there. *)
  (* FILL IN HERE *) admit.
(* FILL IN HERE *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** The general idea: magic wand as frame *)

(** Let's review the proof script above. Before the loop, we first derive
[wlseg [] x x] from [emp]. After every iteration of the loop body, we merge
a piece of singleton list segment [wlseg [b] t u] into it. When exiting the
loop, we get [wlseg [s1a] x t] where [s1 = s1a ++ [b]]. Eventually, this
list segment is merged with a tail [listrep ([b] ++ s2) t], which results in
[listrep (s1 ++ s2) x].

From where the list segment is introduced in the proof, to where the list
segment is eliminated by merging, the C program never modifies the submemory
described by that [wlseg] predicate. In separation logic, such a separating
conjunct is called a "frame". Thus, the general idea here is to use a wand
expression to describe a partial data structure and this wand expression
 will act as a frame in program verification.

In the proof of [body_append_alter2], we only need four of [wlseg]'s
properties: [emp_wlseg], [singleton_wlseg], [wlseg_wlseg] and [wlseg_list].
They are used to introduce, merge and eliminate [wlseg] predicates. Here are
some general patterns beyond these specific rules. *)

Lemma wandQ_frame_elim_mpred: forall {A: Type} (P Q: A -> mpred) (a: A),
  (ALL x : A, P x -* Q x) * P a |-- Q a.
Proof.
  intros.
  rewrite -> wand_sepcon_adjoint.
  apply (allp_left _ a).
  apply derives_refl.
Qed.

(** "ver" in the name of the next lemma stands for "vertical composition"
   of wand frames.   One wand-frame is nested inside another.  *)
Lemma wandQ_frame_ver_mpred: forall {A: Type} (P Q R: A -> mpred),
  (ALL x : A, P x -* Q x) * (ALL x: A, Q x -* R x) |-- ALL x: A, P x -* R x.
Proof.
  intros.
  apply allp_right; intro a.
  rewrite -> wand_sepcon_adjoint.
  apply (allp_left _ a).
  rewrite <- wand_sepcon_adjoint.
  rewrite sepcon_comm, -> wand_sepcon_adjoint.
  apply (allp_left _ a).
  rewrite <- wand_sepcon_adjoint, sepcon_comm.
  apply wand_frame_ver.
Qed.

(* ================================================================= *)
(** ** Case study: list segments for linked list box *)

(** In the following exercise, you are going to apply the magic-wand-as-frame
method on a slightly different data structure.

   Consider the following C function, [append2].

struct list * append2 (struct list * x, struct list * y) {
  struct list **retp, **curp;
  retp = & x;
  curp = & x;
  while ( *curp != NULL ) {
    curp = & (( *curp ) -> tail);
  }
  *curp = y;
  return *retp;
}

 In comparison, this is [append].

struct list *append (struct list *x, struct list *y) {
  struct list *t, *u;
  if (x==NULL)
    return y;
  else {
    t = x;
    u = t->tail;
    while (u!=NULL) {
      t = u;
      u = t->tail;
    }
    t->tail = y;
    return x;
  }
}

  In [append], [u] always equals [t -> tail] after every iteration. When
  exiting the loop, the value of [u] is always null; that is not important.
  More important is the address from whence the null value is loaded. A new
  value will be stored into that location in memory. The program variable
  [t] is used to remember that address.

  The C function [append2] implements linked-list append in an
  alternative way.  In this function, [curp]'s value is not an address
  in the linked list. Instead, it records where a linked list address is
  stored in memory. Specifically, when [curp] points the head
  pointer [x], the value of [curp] is the address of [x].  When [curp]
  points to some intermediate linked list node, the value of [curp] is
  the predecessor node's [tail] field address. Using this implementation, 
  we do not need to test whether [x] is null in the beginning.

  The following separation logic predicate defines this data structure. *)

Definition t_list_box := tptr t_list.

Definition listboxrep (contents: list val) (x: val) :=
  EX y: val, data_at Tsh t_list_box y x * listrep contents x.

Definition lbseg (contents: list val) (x y: val) :=
  ALL tail: list val, listboxrep tail y -* listboxrep (contents ++ tail) x.

(** Previously, we have shown that we can introduce, eliminate and merge
  wand expressions by proving [emp_wlseg], [singleton_wlseg], [wlseg_list]
  and [wlseg_wlseg]. Now, your task is to prove [lbseg]'s properties. Hint:
  proving [wlseg]'s properties and proving [lbseg]'s properties should be very
  similar. *)

(** **** Exercise: 1 star, standard: (emp_lbseg)

    Introducing a wand expression, [lbseg], from [emp]. *)
Lemma emp_lbseg: forall (x: val),
  emp |-- lbseg [] x x.
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard: (lbseg_lbseg)

    Merging two wand expressions. *)
Lemma lbseg_lbseg: forall (s1 s2: list val) (x y z: val),
  lbseg s2 y z * lbseg s1 x y |-- lbseg (s1 ++ s2) x z.
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard: (listbox_lbseg)

    Eliminating a wand expression. *)
Lemma listbox_lbseg: forall (s1 s2: list val) (x y: val),
  lbseg s1 x y * listboxrep s2 y |-- listboxrep (s1 ++ s2) x.
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** Comparison and connection: [lseg] vs. [wlseg] *)

(** We have demonstrated two different approaches to define a
  separation logic predicate for list segments. In [Verif_append1]
  we define it using recursive definition over the list. In this chapter,
  we use a quantifed magic wand expression.  It is natural to ask: what 
  is the relation between [lseg] and [wlseg]? Are they equivalent to each
  other? They following theorems can offer a brief answer. *)

(** First of all, recursive defined [lseg] is a logically stronger 
  predicate than [wlseg]. *)
Lemma lseg2wlseg: forall s x y, lseg s x y |-- wlseg s x y.
Proof.
  intros.
  unfold wlseg.
  apply allp_right; intros tail.
  rewrite <- wand_sepcon_adjoint.
  sep_apply (lseg_list s tail x y).
  apply derives_refl.
Qed.

(** In some special cases, [wlseg] derives [lseg] as well. *)
Lemma wlseg2lseg_nullval: forall s x, wlseg s x nullval |-- lseg s x nullval.
Proof.
  intros.
  unfold wlseg.
  apply allp_left with (@nil val).
  unfold listrep at 1.
  rewrite prop_true_andp by auto.
  entailer!.
  rewrite <- app_nil_end.

  (** The proof goal now has the form: a wand expression derives some
  wand-free assertion.  Usually, this is a tough task because there is
  no good way to eliminate magic wand on left side. But this proof
  goal is special. We can add an extra separating conjunct [emp] to
  the left side and use [modus_ponens_wand] to eliminate wand. *)
  rewrite <- (emp_sepcon (emp -* listrep s x)).
  sep_apply (modus_ponens_wand emp (listrep s x)).

  (** Then, easy! *)
  apply listrep2lseg.
Qed.

(** Combining these two lemmas above together, we know that 
  [wlseg]-to-null equals [lseg]. *)
Lemma wlseg_nullval: forall s x, wlseg s x nullval = lseg s x nullval.
Proof.
  intros.
  apply pred_ext.
  + apply wlseg2lseg_nullval.
  + apply lseg2wlseg.
Qed.

Corollary wlseg_listrep_equiv: forall s x, wlseg s x nullval = listrep s x.
Proof.
  intros.
  rewrite wlseg_nullval, lseg_listrep_equiv.
  reflexivity.
Qed.

(** However, [wlseg] does not derive [lseg] in general. As mentioned
  above, to eliminate magic wand on the left side is hard. When 
  [y <> nullval], we cannot instantiate the universally quantified variable
  [tail] inside [(wlseg s x y)] to get the form [emp -* _].  The
  following is a counterexample of the general entailment from [wlseg]
  to [lseg].  On one hand, it is obvious that
  [data_at_ Tsh t_list y |-/- lseg [a] x y]. On the other hand, 
  [data_at_ Tsh t_list y |-- wlseg [a] x y]. See the following theorem: *)

Lemma wlseg_weird: forall a x y,
  data_at_ Tsh t_list y |-- wlseg [a] x y.
Proof.
  intros.
  unfold wlseg.
  apply allp_right; intros s.
  rewrite <- wand_sepcon_adjoint.
  destruct s.
  + unfold listrep at 1.
    entailer!.
    destruct H as [H _].
    contradiction.
  + unfold listrep at 1; fold listrep.
    Intros u.
    sep_apply (data_at_conflict Tsh t_list (default_val t_list) (v, u) y); auto.
    entailer!.
Qed.

(* 2020-09-18 15:39 *)
