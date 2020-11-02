(** * Perm: Basic Techniques for Comparisons and Permutations *)

(** Consider these algorithms and data structures:
    - sort a sequence of numbers
    - finite maps from numbers to (arbitrary-type) data
    - finite maps from any ordered type to (arbitrary-type) data
    - priority queues: finding/deleting the highest number in a set

    To prove the correctness of such programs, we need to reason about
    comparisons, and about whether two collections have the same
    contents.  In this chapter, we introduce some techniques for
    reasoning about:

    - less-than comparisons on natural numbers, and
    - permutations (rearrangements of lists).

    In later chapters, we'll apply these proof techniques to reasoning
    about algorithms and data structures. *)

Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Strings.String.  (* for manual grading *)
From Coq Require Export Bool.Bool.
From Coq Require Export Arith.Arith.
From Coq Require Export Arith.EqNat.
From Coq Require Export Omega.
From Coq Require Export Lists.List.
Export ListNotations.
From Coq Require Export Permutation.

(* ################################################################# *)
(** * The Less-Than Order on the Natural Numbers *)

(** In our proofs about searching and sorting algorithms, we often
    have to reason about the less-than order on natural numbers.
    greater-than. Recall that the Coq standard library contains both
    propositional and Boolean less-than operators on natural numbers.
    We write [x < y] for the proposition that [x] is less than [y]: *)

Locate "_ < _". (* "x < y" := lt x y *)
Check lt : nat -> nat -> Prop.

(** And we write [x <? y] for the computation that returns [true] or
    [false] depending on whether [x] is less than [y]: *)

Locate "_ <? _". (* x <? y  := Nat.ltb x y *)
Check Nat.ltb : nat -> nat -> bool.

(** Operation [<] is a reflection of [<?], as discussed in
    [Logic] and [IndProp]. The [Nat] module has a
    theorem showing how they relate: *)

Check Nat.ltb_lt : forall n m : nat, (n <? m) = true <-> n < m.

(** The [Nat] module contains a synonym for [lt]. *)

Print Nat.lt. (* Nat.lt = lt *)

(** For unknown reasons, [Nat] does not define notations
    for [>?] or [>=?].  So we define them here: *)

Notation  "a >=? b" := (Nat.leb b a)
                          (at level 70) : nat_scope.
Notation  "a >? b"  := (Nat.ltb b a)
                         (at level 70) : nat_scope.

(* ================================================================= *)
(** ** The Omega Tactic *)

(** Reasoning about inequalities by hand can be a little painful. Luckily, Coq
    provides a tactic called [omega] that is quite helpful. *)

Theorem omega_example1:
 forall i j k,
    i < j ->
    ~ (k - 3 <= j) ->
   k > i.
Proof.
  intros.

(** The hard way to prove this is by hand. *)

  (* try to remember the name of the lemma about negation and [<=] *)
  Search (~ _ <= _ -> _).
  apply not_le in H0.
  (* try to remember the name of the transitivity lemma about [>] *)
  Search (_ > _ -> _ > _ -> _ > _).
  apply gt_trans with j.
  apply gt_trans with (k-3).
  (* Is [k] greater than [k-3]? On the integers, sure. But we're working
     with natural numbers, which truncate subtraction at zero. *)
Abort.

Theorem truncated_subtraction: ~ (forall k:nat, k > k - 3).
Proof.
  intros contra.
  (* [specialize] applies a hypothesis to an argument *)
  specialize (contra 0).
  simpl in contra.
  inversion contra.
Qed.

(** Since subtraction is truncated, does [omega_example1] actually hold?
    It does. Let's try again, the hard way, to find the proof. *)

Theorem omega_example1:
 forall i j k,
    i < j ->
    ~ (k - 3 <= j) ->
   k > i.
Proof. (* try again! *)
  intros.
  apply not_le in H0.
  unfold gt in H0.
  unfold gt.
  (* try to remember the name ... *)
  Search (_ < _ -> _ <= _ -> _ < _).
  apply lt_le_trans with j.
  apply H.
  apply le_trans with (k-3).
  Search (_ < _ -> _ <= _).
  apply lt_le_weak.
  auto.
  apply le_minus.
Qed.

(** That was tedious.  Here's a much easier way: *)

Theorem omega_example2:
 forall i j k,
    i < j ->
    ~ (k - 3 <= j) ->
   k > i.
Proof.
  intros.
  omega.
Qed.

(** Omega is a decision procedure invented in 1991 by William Pugh for
    integer linear programming (ILP). The [omega] tactic was made
    available by importing [Coq.omega.Omega], at the beginning of the
    file.  It is an implementation of Pugh's algorithm.  The tactic
    works with Coq types [Z] and [nat], and these operators: [<] [=] [>]
    [<=] [>=] [+] [-] [~], as well as multiplication by small integer
    literals (such as 0,1,2,3...), and some uses of [\/] and [/\].

    Omega does not "understand" other operators.  It treats
    expressions such as [a * b] and [f x y] as variables.  That is, it
    can prove [f x y > a * b -> f x y + 3 >= a * b], in the same way it
    would prove [u > v -> u + 3 >= v]. But it cannot reason about, e.g.,
    multiplication. *)

Theorem omega_example_3 : forall (f : nat -> nat -> nat) a b x y,
    f x y > a * b -> f x y + 3 >= a * b.
Proof.
  intros. omega.
Qed.

Theorem omega_example_4 : forall a b,
    a * b = b * a.
Proof.
  intros. Fail omega.
Abort.

(** The Omega algorithm is NP-complete, so we might expect that
    this tactic is exponential-time in the worst case.  Indeed,
    if you have [N] equations, it could take [2^N] time.
    But in the typical cases that result from reasoning about
    programs, [omega] is much faster than that. *)

(* ################################################################# *)
(** * Swapping *)

(** Consider trying to sort a list of natural numbers.  As a small piece of
    a sorting algorithm, we might need to swap the first two elements of a list
    if they are out of order. *)

Definition maybe_swap (al: list nat) : list nat :=
  match al with
  | a :: b :: ar => if a >? b then b :: a :: ar else a :: b :: ar
  | _ => al
  end.

Example maybe_swap_123:
  maybe_swap [1; 2; 3] = [1; 2; 3].
Proof. reflexivity. Qed.

Example maybe_swap_321:
  maybe_swap [3; 2; 1] = [2; 3; 1].
Proof. reflexivity. Qed.

(** Applying [maybe_swap] twice should give the same result as applying it once.
    That is, [maybe_swap] is _idempotent_. *)

Theorem maybe_swap_idempotent: forall al,
    maybe_swap (maybe_swap al) = maybe_swap al.
Proof.
  intros [ | a [ | b al]]; simpl; try reflexivity.
  destruct (b <? a) eqn:Hb_lt_a; simpl.
  - destruct (a <? b) eqn:Ha_lt_b; simpl.
    + (** Now what?  We have a contradiction in the hypotheses: it
          cannot hold that [a] is less than [b] and [b] is less than
          [a].  Unfortunately, [omega] cannot immediately show that
          for us, because it reasons about comparisons in [Prop] not
          [bool]. *)
      Fail omega.
Abort.

(** Of course we could finish the proof by reasoning directly about
    inequalities in [bool].  But this situation is going to occur
    repeatedly in our study of sorting. *)

(** Let's set up some machinery to enable using [omega] on boolean
    tests. *)

(* ================================================================= *)
(** ** Reflection *)

(** The [reflect] type, defined in the standard library (and presented
    in [IndProp]), relates a proposition to a Boolean. That is,
    a value of type [reflect P b] contains a proof of [P] if [b] is
    [true], or a proof of [~ P] if [b] is [false]. *)

Print reflect.
(*
Inductive reflect (P : Prop) : bool -> Set :=
  | ReflectT :   P -> reflect P true
  | ReflectF : ~ P -> reflect P false
 *)

(** The standard library proves a theorem that says if [P] is provable
    whenever [b = true] is provable, then [P] reflects [b]. *)

Check iff_reflect : forall (P : Prop) (b : bool),
    P <-> b = true -> reflect P b.

(** Using that theorem, we can quickly prove that the propositional
    (in)equality operators are reflections of the Boolean
    operators. *)

Lemma eqb_reflect : forall x y, reflect (x = y) (x =? y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply Nat.eqb_eq.
Qed.

Lemma ltb_reflect : forall x y, reflect (x < y) (x <? y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply Nat.ltb_lt.
Qed.

Lemma leb_reflect : forall x y, reflect (x <= y) (x <=? y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply Nat.leb_le.
Qed.

(** Here's an example of how you could use these lemmas.  Suppose you
    have this simple program, [(if a <? 5 then a else 2)], and you
    want to prove that it evaluates to a number smaller than 6.  You
    can use [ltb_reflect] "by hand": *)

Example reflect_example1: forall a,
    (if a <? 5 then a else 2) < 6.
Proof.
  intros a.
  (* The next two lines aren't strictly necessary, but they
     help make it clear what [destruct] does. *)
  assert (R: reflect (a < 5) (a <? 5)) by apply ltb_reflect.
  remember (a <? 5) as guard.
  destruct R as [H|H] eqn:HR.
  * (* ReflectT *) omega.
  * (* ReflectF *) omega.
Qed.

(** For the [ReflectT] constructor, the guard [a <? 5] must be equal
    to [true]. The [if] expression in the goal has already been
    simplified to take advantage of that fact. Also, for [ReflectT] to
    have been used, there must be evidence [H] that [a < 5] holds.
    From there, all that remains is to show [a < 5] entails [a < 6].
    The [omega] tactic, which is capable of automatically proving some
    theorems about inequalities, succeeds.

    For the [ReflectF] constructor, the guard [a <? 5] must be equal
    to [false]. So the [if] expression simplifies to [2 < 6], which is
    immediately provable by [omega]. *)

(** A less didactic version of the above proof wouldn't do the
    [assert] and [remember]: we can directly skip to [destruct]. *)

Example reflect_example1': forall a,
    (if a <? 5 then a else 2) < 6.
Proof.
  intros a. destruct (ltb_reflect a 5); omega.
Qed.

(** But even that proof is a little unsatisfactory. The original expression,
    [a <? 5], is not perfectly apparent from the expression [ltb_reflect a 5]
    that we pass to [destruct]. *)

(** It would be nice to be able to just say something like [destruct
    (a <? 5)] and get the reflection "for free."  That's what we'll
    engineer, next. *)

(* ================================================================= *)
(** ** A Tactic for Boolean Destruction *)

(** We're now going to build a tactic that you'll want to _use_, but
    you won't need to understand the details of how to _build_ it
    yourself.

    Let's put several of these [reflect] lemmas into a Hint database.
    We call it [bdestruct], because we'll use it in our
    boolean-destruction tactic: *)

Hint Resolve ltb_reflect leb_reflect eqb_reflect : bdestruct.

(** Here is the tactic, the body of which you do not need to
    understand.  Invoking [bdestruct] on Boolean expression [b] does
    the same kind of reasoning we did above: reflection and
    destruction.  It also attempts to simplify negations involving
    inequalities in hypotheses. *)

Ltac bdestruct X :=
  let H := fresh in let e := fresh "e" in
   evar (e: Prop);
   assert (H: reflect e X); subst e;
    [eauto with bdestruct
    | destruct H as [H|H];
       [ | try first [apply not_lt in H | apply not_le in H]]].

(** This tactic makes quick, easy-to-read work of our running example. *)

Example reflect_example2: forall a,
    (if a <? 5 then a else 2) < 6.
Proof.
  intros.
  bdestruct (a <? 5);  (* instead of: [destruct (ltb_reflect a 5)]. *)
  omega.
Qed.

(* ================================================================= *)
(** ** Finishing the [maybe_swap] Proof *)

(** Now that we have [bdestruct], we can finish the proof of [maybe_swap]'s
    idempotence. *)

Theorem maybe_swap_idempotent: forall al,
    maybe_swap (maybe_swap al) = maybe_swap al.
Proof.
  intros [ | a [ | b al]]; simpl; try reflexivity.
  bdestruct (a >? b); simpl.
  (** Note how [b < a] is a hypothesis, rather than [b <? a = true]. *)
  - bdestruct (b >? a); simpl.
    + (** [omega] can take care of the contradictory propositional inequalities. *)
      omega.
    + reflexivity.
  - bdestruct (a >? b); simpl.
    + omega.
    + reflexivity.
Qed.

(** When proving theorems about a program that uses Boolean
    comparisons, use [bdestruct] followed by [omega], rather than
    [destruct] followed by application of various theorems about
    Boolean operators. *)

(* ################################################################# *)
(** * Permutations *)

(** Another useful fact about [maybe_swap] is that it doesn't add or
    remove elements from the list: it only reorders them.  That is,
    the output list is a permutation of the input.  List [al] is a
    _permutation_ of list [bl] if the elements of [al] can be
    reordered to get the list [bl].  Note that reordering does not
    permit adding or removing duplicate elements. *)

(** Coq's [Permutation] library has an inductive definition of
    permutations. *)

Print Permutation.

(*
 Inductive Permutation {A : Type} : list A -> list A -> Prop :=
    perm_nil : Permutation [] []
  | perm_skip : forall (x : A) (l l' : list A),
                Permutation l l' ->
                Permutation (x :: l) (x :: l')
  | perm_swap : forall (x y : A) (l : list A),
                Permutation (y :: x :: l) (x :: y :: l)
  | perm_trans : forall l l' l'' : list A,
                 Permutation l l' ->
                 Permutation l' l'' ->
                 Permutation l l''.
 *)

(** You might wonder, "is that really the right definition?"  And
    indeed, it's important that we get a right definition, because
    [Permutation] is going to be used in our specifications of
    searching and sorting algorithms.  If we have the wrong
    specification, then all our proofs of "correctness" will be
    useless.

    It's not obvious that this is indeed the right specification of
    permutations. (It happens to be, but that's not obvious.) To gain
    confidence that we have the right specification, let's use it
    prove some properties that permutations ought to have. *)

(** **** Exercise: 2 stars, standard (Permutation_properties) 

    Think of some desirable properties of the [Permutation] relation
    and write them down informally in English, or a mix of Coq and
    English.  Here are four to get you started:

     - 1. If [Permutation al bl], then [length al = length bl].
     - 2. If [Permutation al bl], then [Permutation bl al].
     - 3. [[1;1]] is NOT a permutation of [[1;2]].
     - 4. [[1;2;3;4]] IS a permutation of [[3;4;2;1]].

   YOUR TASK: Add three more properties. Write them here: *)

(** Now, let's examine all the theorems in the Coq library about
    permutations: *)

Search Permutation.  (* Browse through the results of this query! *)

(** Which of the properties that you wrote down above have already
    been proved as theorems by the Coq library developers?  Answer
    here:

*)
(* Do not modify the following line: *)
Definition manual_grade_for_Permutation_properties : option (nat*string) := None.
(** [] *)

(** Let's use the permutation theorems in the library to prove the
    following theorem. *)

Example butterfly: forall b u t e r f l y : nat,
  Permutation ([b;u;t;t;e;r]++[f;l;y]) ([f;l;u;t;t;e;r]++[b;y]).
Proof.
  intros.
  (** Let's group [[u;t;t;e;r]] together on both sides.  Tactic
      [change t with u] replaces [t] with [u].  Terms [t] and [u] must
      be _convertible_, here meaning that they evalute to the same
      term. *)
  change [b;u;t;t;e;r] with ([b]++[u;t;t;e;r]).
  change [f;l;u;t;t;e;r] with ([f;l]++[u;t;t;e;r]).

  (** We don't actually need to know the list elements in
      [[u;t;t;e;r]].  Let's forget about them and just remember them
      as a variable named [utter]. *)
  remember [u;t;t;e;r] as utter. clear Hequtter.

  (** Likewise, let's group [[f;l]] and remember it as a variable. *)
  change [f;l;y] with ([f;l]++[y]).
  remember [f;l] as fl. clear Heqfl.

  (** Next, let's cancel [fl] from both sides.  In order to do that,
      we need to bring it to the beginning of each list. For the right
      list, that follows easily from the associativity of [++].  *)
  replace ((fl ++ utter) ++ [b;y]) with (fl ++ utter ++ [b;y])
    by apply app_assoc.

  (** But for the left list, we can't just use associativity.
      Instead, we need to reason about permutations and use some
      library theorems. *)
  apply perm_trans with (fl ++ [y] ++ ([b] ++ utter)).
  - replace (fl ++ [y] ++ [b] ++ utter) with ((fl ++ [y]) ++ [b] ++ utter).
    + apply Permutation_app_comm.
    + rewrite <- app_assoc. reflexivity.

  - (** A library theorem will now help us cancel [fl]. *)
    apply Permutation_app_head.

  (** Next let's cancel [utter]. *)
    apply perm_trans with (utter ++ [y] ++ [b]).
    + replace ([y] ++ [b] ++ utter) with (([y] ++ [b]) ++ utter).
      * apply Permutation_app_comm.
      * rewrite app_assoc. reflexivity.
    + apply Permutation_app_head.

      (** Finally we're left with just [y] and [b]. *)
      apply perm_swap.
Qed.

(** That example illustrates a general method for proving permutations
    involving cons [::] and append [++]:

    - Identify some portion appearing in both sides.
    - Bring that portion to the front on each side using lemmas such
      as [Permutation_app_comm] and [perm_swap], with generous use of
      [perm_trans].
    - Use [Permutation_app_head] to cancel an appended head.  You can
      also use [perm_skip] to cancel a single element. *)

(** **** Exercise: 3 stars, standard (permut_example) 

    Use the permutation rules in the library to prove the following
    theorem.  The following [Check] commands are a hint about useful
    lemmas.  You don't need all of them, and depending on your
    approach you will find lemmas to be more useful than others. Use
    [Search Permutation] to find others, if you like. *)

Check perm_skip.
Check perm_trans.
Check Permutation_refl.
Check Permutation_app_comm.
Check app_assoc.
Check app_nil_r.
Check app_comm_cons.

Example permut_example: forall (a b: list nat),
  Permutation (5 :: 6 :: a ++ b) ((5 :: b) ++ (6 :: a ++ [])).
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard (not_a_permutation) 

    Prove that [[1;1]] is not a permutation of [[1;2]].
    Hints are given as [Check] commands. *)

Check Permutation_cons_inv.
Check Permutation_length_1_inv.

Example not_a_permutation:
  ~ Permutation [1;1] [1;2].
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** Correctness of [maybe_swap] *)

(** Now we can prove that [maybe_swap] is a permutation: it reorders
    elements but does not add or remove any. *)

Theorem maybe_swap_perm: forall al,
  Permutation al (maybe_swap al).
Proof.
  (* WORKED IN CLASS *)
  unfold maybe_swap.
  destruct al as [ | a [ | b al]].
  - simpl. apply perm_nil.
  - apply Permutation_refl.
  - bdestruct (b <? a).
    + apply perm_swap.
    + apply Permutation_refl.
Qed.

(** And, we can prove that [maybe_swap] permutes elements such that
    the first is less than or equal to the second. *)

Definition first_le_second (al: list nat) : Prop :=
  match al with
  | a :: b :: _ => a <= b
  | _ => True
  end.

Theorem maybe_swap_correct: forall al,
    Permutation al (maybe_swap al)
    /\ first_le_second (maybe_swap al).
Proof.
  intros. split.
  - apply maybe_swap_perm.
  - (* WORKED IN CLASS *)
    unfold maybe_swap.
    destruct al as [ | a [ | b al]]; simpl; auto.
    bdestruct (a >? b); simpl; omega.
Qed.

(* ################################################################# *)
(** * Summary: Comparisons and Permutations *)

(** To prove correctness of algorithms for sorting and searching,
    we'll reason about comparisons and permutations using the tools
    developed in this chapter.  The [maybe_swap] program is a tiny
    little example of a sorting program.  The proof style in
    [maybe_swap_correct] will be applied (at a larger scale) in
    the next few chapters. *)

(** **** Exercise: 3 stars, standard (Forall_perm) 

    To close, we define a utility tactic and lemma.  First, the
    tactic. *)

(** Coq's [inversion H] tactic is so good at extracting
    information from the hypothesis [H] that [H] sometimes becomes
    completely redundant, and one might as well [clear] it from the
    goal.  Then, since the [inversion] typically creates some equality
    facts, why not then [subst] ?  Tactic [inv] does just that. *)

Ltac inv H := inversion H; clear H; subst.

(** Second, the lemma.  You will find [inv] useful in proving it.

    [Forall] is Coq library's version of the [All] proposition defined
    in [Logic], but defined as an inductive proposition rather
    than a fixpoint.  Prove this lemma by induction.  You will need to
    decide what to induct on: [al], [bl], [Permutation al bl], and
    [Forall f al] are possibilities. *)

Theorem Forall_perm: forall {A} (f: A -> Prop) al bl,
  Permutation al bl ->
  Forall f al -> Forall f bl.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)


(* 2020-08-07 17:08 *)
