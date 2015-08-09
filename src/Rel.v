(** * Rel: Properties of Relations *)

Require Export SfLib.

(** This short, optional chapter develops some basic definitions and a
    few theorems about binary relations in Coq.  The key definitions
    are repeated where they are actually used (in the [Smallstep]
    chapter), so readers who are already comfortable with these ideas
    can safely skim or skip this chapter.  However, relations are also
    a good source of exercises for developing facility with Coq's
    basic reasoning facilities, so it may be useful to look at it just
    after the [Logic] chapter. *)

(** A (binary) _relation_ on a set [X] is a family of propositions
    parameterized by two elements of [X] -- i.e., a proposition about
    pairs of elements of [X].  *)

Definition relation (X: Type) := X->X->Prop.

(** Somewhat confusingly, the Coq standard library hijacks the generic
    term "relation" for this specific instance. To maintain
    consistency with the library, we will do the same.  So, henceforth
    the Coq identifier [relation] will always refer to a binary
    relation between some set and itself, while the English word
    "relation" can refer either to the specific Coq concept or the
    more general concept of a relation between any number of possibly
    different sets.  The context of the discussion should always make
    clear which is meant. *)

(** An example relation on [nat] is [le], the less-that-or-equal-to
    relation which we usually write like this [n1 <= n2]. *)

Print le.
(* ====> Inductive le (n : nat) : nat -> Prop :=
             le_n : n <= n
           | le_S : forall m : nat, n <= m -> n <= S m *)
Check le : nat -> nat -> Prop.
Check le : relation nat.

(* ######################################################### *)
(** * Basic Properties of Relations *)

(** As anyone knows who has taken an undergraduate discrete math
    course, there is a lot to be said about relations in general --
    ways of classifying relations (are they reflexive, transitive,
    etc.), theorems that can be proved generically about classes of
    relations, constructions that build one relation from another,
    etc.  For example... *)

(** A relation [R] on a set [X] is a _partial function_ if, for every
    [x], there is at most one [y] such that [R x y] -- i.e., if [R x
    y1] and [R x y2] together imply [y1 = y2]. *)

Definition partial_function {X: Type} (R: relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2. 

(** For example, the [next_nat] relation defined earlier is a partial
    function. *)

Print next_nat.
(* ====> Inductive next_nat (n : nat) : nat -> Prop := 
           nn : next_nat n (S n) *)
Check next_nat : relation nat.

Theorem next_nat_partial_function : 
   partial_function next_nat.
Proof. 
  unfold partial_function.
  intros x y1 y2 H1 H2.
  inversion H1. inversion H2.
  reflexivity.  Qed. 

(** However, the [<=] relation on numbers is not a partial function.
    In short: Assume, for a contradiction, that [<=] is a partial
    function.  But then, since [0 <= 0] and [0 <= 1], it follows that
    [0 = 1].  This is nonsense, so our assumption was
    contradictory. *)

Theorem le_not_a_partial_function :
  ~ (partial_function le).
Proof.
  unfold not. unfold partial_function. intros Hc.
  assert (0 = 1) as Nonsense.
   Case "Proof of assertion".
   apply Hc with (x := 0). 
     apply le_n. 
     apply le_S. apply le_n. 
  inversion Nonsense.   Qed.

(** **** Exercise: 2 stars, optional  *)
(** Show that the [total_relation] defined in earlier is not a partial
    function. *)

(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 2 stars, optional  *)
(** Show that the [empty_relation] defined earlier is a partial
    function. *)

(* FILL IN HERE *)
(** [] *)

(** A _reflexive_ relation on a set [X] is one for which every element
    of [X] is related to itself. *)

Definition reflexive {X: Type} (R: relation X) :=
  forall a : X, R a a.

Theorem le_reflexive :
  reflexive le.
Proof. 
  unfold reflexive. intros n. apply le_n.  Qed.

(** A relation [R] is _transitive_ if [R a c] holds whenever [R a b]
    and [R b c] do. *)

Definition transitive {X: Type} (R: relation X) :=
  forall a b c : X, (R a b) -> (R b c) -> (R a c).

Theorem le_trans :
  transitive le.
Proof.
  intros n m o Hnm Hmo.
  induction Hmo.
  Case "le_n". apply Hnm.
  Case "le_S". apply le_S. apply IHHmo.  Qed.

Theorem lt_trans:
  transitive lt.
Proof. 
  unfold lt. unfold transitive. 
  intros n m o Hnm Hmo.
  apply le_S in Hnm. 
  apply le_trans with (a := (S n)) (b := (S m)) (c := o).
  apply Hnm.
  apply Hmo. Qed.

(** **** Exercise: 2 stars, optional  *)
(** We can also prove [lt_trans] more laboriously by induction,
    without using le_trans.  Do this.*)

Theorem lt_trans' :
  transitive lt.
Proof.
  (* Prove this by induction on evidence that [m] is less than [o]. *)
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  induction Hmo as [| m' Hm'o].
    (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, optional  *)
(** Prove the same thing again by induction on [o]. *)

Theorem lt_trans'' :
  transitive lt.
Proof.
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  induction o as [| o'].
  (* FILL IN HERE *) Admitted.
(** [] *)

(** The transitivity of [le], in turn, can be used to prove some facts
    that will be useful later (e.g., for the proof of antisymmetry
    below)... *)

Theorem le_Sn_le : forall n m, S n <= m -> n <= m.
Proof. 
  intros n m H. apply le_trans with (S n).
    apply le_S. apply le_n.
    apply H.  Qed.

(** **** Exercise: 1 star, optional  *)
Theorem le_S_n : forall n m,
  (S n <= S m) -> (n <= m).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, optional (le_Sn_n_inf)  *)
(** Provide an informal proof of the following theorem:
 
    Theorem: For every [n], [~(S n <= n)]
 
    A formal proof of this is an optional exercise below, but try
    the informal proof without doing the formal proof first.
 
    Proof:
    (* FILL IN HERE *)
    []
 *)

(** **** Exercise: 1 star, optional  *)
Theorem le_Sn_n : forall n,
  ~ (S n <= n).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** Reflexivity and transitivity are the main concepts we'll need for
    later chapters, but, for a bit of additional practice working with
    relations in Coq, here are a few more common ones.

   A relation [R] is _symmetric_ if [R a b] implies [R b a]. *)

Definition symmetric {X: Type} (R: relation X) :=
  forall a b : X, (R a b) -> (R b a).

(** **** Exercise: 2 stars, optional  *)
Theorem le_not_symmetric :
  ~ (symmetric le).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** A relation [R] is _antisymmetric_ if [R a b] and [R b a] together
    imply [a = b] -- that is, if the only "cycles" in [R] are trivial
    ones. *)

Definition antisymmetric {X: Type} (R: relation X) :=
  forall a b : X, (R a b) -> (R b a) -> a = b.

(** **** Exercise: 2 stars, optional  *)
Theorem le_antisymmetric :
  antisymmetric le.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, optional  *)
Theorem le_step : forall n m p,
  n < m ->
  m <= S p ->
  n <= p.
Proof. 
  (* FILL IN HERE *) Admitted.
(** [] *)

(** A relation is an _equivalence_ if it's reflexive, symmetric, and
    transitive.  *)

Definition equivalence {X:Type} (R: relation X) :=
  (reflexive R) /\ (symmetric R) /\ (transitive R).

(** A relation is a _partial order_ when it's reflexive,
    _anti_-symmetric, and transitive.  In the Coq standard library
    it's called just "order" for short. *)

Definition order {X:Type} (R: relation X) :=
  (reflexive R) /\ (antisymmetric R) /\ (transitive R).

(** A preorder is almost like a partial order, but doesn't have to be
    antisymmetric. *)

Definition preorder {X:Type} (R: relation X) :=
  (reflexive R) /\ (transitive R).

Theorem le_order :
  order le.
Proof.
  unfold order. split. 
    Case "refl". apply le_reflexive.
    split. 
      Case "antisym". apply le_antisymmetric. 
      Case "transitive.". apply le_trans.  Qed.

(* ########################################################### *)
(** * Reflexive, Transitive Closure *)

(** The _reflexive, transitive closure_ of a relation [R] is the
    smallest relation that contains [R] and that is both reflexive and
    transitive.  Formally, it is defined like this in the Relations
    module of the Coq standard library: *)

Inductive clos_refl_trans {A: Type} (R: relation A) : relation A :=
    | rt_step : forall x y, R x y -> clos_refl_trans R x y
    | rt_refl : forall x, clos_refl_trans R x x
    | rt_trans : forall x y z,
          clos_refl_trans R x y ->
          clos_refl_trans R y z ->
          clos_refl_trans R x z.

(** For example, the reflexive and transitive closure of the
    [next_nat] relation coincides with the [le] relation. *)

Theorem next_nat_closure_is_le : forall n m,
  (n <= m) <-> ((clos_refl_trans next_nat) n m).
Proof.
  intros n m. split.
    Case "->".
      intro H. induction H.
      SCase "le_n". apply rt_refl.
      SCase "le_S".
        apply rt_trans with m. apply IHle. apply rt_step. apply nn.
    Case "<-".
      intro H. induction H.
      SCase "rt_step". inversion H. apply le_S. apply le_n.
      SCase "rt_refl". apply le_n.
      SCase "rt_trans".
        apply le_trans with y.
        apply IHclos_refl_trans1.
        apply IHclos_refl_trans2. Qed.

(** The above definition of reflexive, transitive closure is
    natural -- it says, explicitly, that the reflexive and transitive
    closure of [R] is the least relation that includes [R] and that is
    closed under rules of reflexivity and transitivity.  But it turns
    out that this definition is not very convenient for doing
    proofs -- the "nondeterminism" of the [rt_trans] rule can sometimes
    lead to tricky inductions.
 
    Here is a more useful definition... *)

Inductive refl_step_closure {X:Type} (R: relation X) : relation X :=
  | rsc_refl  : forall (x : X), refl_step_closure R x x
  | rsc_step : forall (x y z : X),
                    R x y ->
                    refl_step_closure R y z ->
                    refl_step_closure R x z.

(** (Note that, aside from the naming of the constructors, this
    definition is the same as the [multi] step relation used in many
    other chapters.) *)

(** (The following [Tactic Notation] definitions are explained in
    another chapter.  You can ignore them if you haven't read the
    explanation yet.) *)

Tactic Notation "rt_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "rt_step" | Case_aux c "rt_refl" 
  | Case_aux c "rt_trans" ].

Tactic Notation "rsc_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "rsc_refl" | Case_aux c "rsc_step" ].

(** Our new definition of reflexive, transitive closure "bundles"
    the [rt_step] and [rt_trans] rules into the single rule step.
    The left-hand premise of this step is a single use of [R],
    leading to a much simpler induction principle.
 
    Before we go on, we should check that the two definitions do
    indeed define the same relation...
    
    First, we prove two lemmas showing that [refl_step_closure] mimics
    the behavior of the two "missing" [clos_refl_trans]
    constructors.  *)

Theorem rsc_R : forall (X:Type) (R:relation X) (x y : X),
       R x y -> refl_step_closure R x y.
Proof.
  intros X R x y H.
  apply rsc_step with y. apply H. apply rsc_refl.   Qed.

(** **** Exercise: 2 stars, optional (rsc_trans)  *)
Theorem rsc_trans :
  forall (X:Type) (R: relation X) (x y z : X),
      refl_step_closure R x y  ->
      refl_step_closure R y z ->
      refl_step_closure R x z.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** Then we use these facts to prove that the two definitions of
    reflexive, transitive closure do indeed define the same
    relation. *)

(** **** Exercise: 3 stars, optional (rtc_rsc_coincide)  *)
Theorem rtc_rsc_coincide : 
         forall (X:Type) (R: relation X) (x y : X),
  clos_refl_trans R x y <-> refl_step_closure R x y.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** $Date: 2014-12-31 15:31:47 -0500 (Wed, 31 Dec 2014) $ *)
