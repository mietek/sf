(** * Verif_reverse: Linked lists in Verifiable C *)

(** This chapter demonstrates some more features of Verifiable C. 
  There are no exercises in this chapter. *)

(* ================================================================= *)
(** ** Running Example *)

(** Here is a little C program, [reverse.c]:

    #include <stddef.h>

    struct list {unsigned head; struct list *tail;};

    struct list *reverse (struct list *p) {
      struct list *w, *t, *v;
      w = NULL;
      v = p;
      while (v) {
        t = v->tail;
        v->tail = w;
        w = v;
        v = t;
      }
      return w;
    }

This program reverses the linked list [p], by updating all the [tail]
pointers without touching any of the [head] values.  You can "see it run"
by flipping through the slides of Reverse-Slides.pdf, distributed with
this chapter.    Let's prove this program correct!
*)

(** SEE ALSO VC.pdf Chapter 46 (_Proof of the reverse program_) *)

(** As usual, we import the Verifiable C system [VST.floyd.proofauto],
    then the program to be verified, in this case [reverse].  Then we
    give the standard boilerplate definitions of [CompSpecs] and [Vprog]. *)

Require VC.Preface. (* Check for the right version of VST *)
Require Import VST.floyd.proofauto.
Require Import VC.reverse.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

(* ================================================================= *)
(** ** Inductive definition of linked lists *)

(** [Tstruct _list noattr] is the AST (abstract syntax tree) description
 of the C-language type [struct list].  We will be using this a lot,
 so we make an abbreviation for it, t_list: *)

Definition t_list := Tstruct _list noattr.

(** We will define a separation-logic predicate, [listrep sigma p],
 to describe the concept that the address [p] in memory is a linked
 list that represents the mathematical sequence [sigma].
 Here, [sigma] is a list of [val],  which is C's "value" type:
 integers, pointers, floats, etc. *)

Fixpoint listrep (sigma: list val) (p: val) : mpred :=
 match sigma with
 | h::hs =>
    EX y:val, data_at Tsh t_list (h,y) p  *  listrep hs y
 | nil =>
    !! (p = nullval) && emp
 end.

(** This says, if [sigma] has head [h] and tail [hs], then
  there is a cons cell at address [p] with components [(h,y)].
  This cons cell is described by [data_at Tsh t_list (h,y) p].
  Separate from that, at address [y], there is the representation
  of the rest of the list, [listrep hs y].  The memory footprint
  for [listrep (h::hs) p] contains the first cons cell at address [p],
  and the rest of the cons cells in the list starting at address [y].

  But if [sigma] is [nil], then [p] is the null pointer, and the
  memory footprint is empty ([emp]).  The fact [p=nullval] is a pure
  proposition (Coq [Prop]); we inject this into the assertion language
  (Coq [mpred]) using the [!!] operator.

  Because [!!P] (for a proposition [P]) does not specify any footprint
  (whether empty or otherwise), we do not use the separating conjunction
  [*] to combine it with [emp];  [!!P] has no _spatial_ specification
  to separate from.  Instead, we use the ordinary conjunction [&&].

 Now, we want to prevent the [simpl] tactic from automatically
 unfolding [listrep].  This is a design choice that you might make
 differently, in which case, leave out the [Arguments] command. *)

Arguments listrep sigma p : simpl never.

(* ================================================================= *)
(** ** Hint databases for spatial operators *)

(** Whenever you define a new spatial operator--a definition of type
  [mpred] such as [listrep]--it's useful to populate two hint  databases.
  - The [saturate_local] hint is a lemma that extracts
     pure propositional facts from a spatial fact.
  - The [valid_pointer] hint is a lemma that extracts a
     valid-pointer fact from a spatial lemma.

   Consider this proof goal: *)

Lemma data_at_isptr_example1:
  forall (h y p : val) ,
   data_at Tsh t_list (h,y) p |-- !! isptr p.
Proof.
intros.
 (** [isptr p] means [p] is a non-null pointer, not NULL or Vundef
      or a floating-point number: *)
Print isptr.
  (* = fun v : val => match v with Vptr _ _ => True | _ => False end

    The goal solves automatically, using [entailer!] *)
entailer!.
Qed.

Lemma data_at_isptr_example2:
  forall (h y p : val) ,
   data_at Tsh t_list (h,y) p |-- !! isptr p.
Proof.
intros.
(** Let's look more closely at how [entailer!] solves this goal.
    First, it finds all the pure propositions [Prop] that it can deduce from
    the [mpred] conjuncts on the left-hand side, and puts them above the line. *)
saturate_local.
(** The [saturate_local] tactic uses a Hint database (also called
   [saturate_local]) to look up the individual conjuncts on the left-hand side
   (this particular entailment has just one conjunct). *)
Print HintDb saturate_local.
(** In this case, the new propositions above the line are labeled [H] and [H0].

    Next, if the proof goal has just a proposition [!!P] on the right,
    [entailer!] throws away the left-hand-side and tries to prove [P].
    (This is rather aggressive, and can sometimes lose information, that is,
     sometimes [entailer!] will turn a provable goal into an unprovable goal.) *)

apply prop_right.

(** It happens that [field_compatible _ _ p] implies [isptr p], *)
Check field_compatible_isptr.
   (* : forall (t : type) (path : list gfield) (p : val),
       field_compatible t path p -> isptr p *)

(** So therefore, [field_compatible_isptr] solves the goal. *)
eapply field_compatible_isptr; eauto.
(** Now you have some insight into how [entailer!] works. *)
Qed.

(** But when you define a new spatial predicate [mpred] such as [listrep],
   the [saturate_local] tactic does not know how to deduce [Prop] facts
   from the [listrep] conjunct: *)

Lemma listrep_facts_example:
 forall sigma p,
   listrep sigma p |-- !! (isptr p \/ p=nullval).
Proof.
intros.
entailer!.
(** Here, [entailer!] threw away the left-hand-side and left an unprovable goal.
   Let's see why. *)
Abort.

Lemma listrep_facts_example:
 forall sigma p,
   listrep sigma p |-- !! (isptr p \/ p=nullval).
Proof.
intros.
(** First [entailer!] would use [saturate_local] to see (from the Hint database)
   what can be deduced from [listrep sigma p]. *)
saturate_local.
(** But [saturate_local] did not add anything above the line.  That's because
   there's no Hint in the Hint database for [listrep].
   Therefore we must add one.   The conventional name for such a lemma
   is  [f_local_facts], if your new predicate is named [f]. *)
Abort.

Lemma listrep_local_facts:
  forall sigma p,
   listrep sigma p |--
   !! (is_pointer_or_null p /\ (p=nullval <-> sigma=nil)).

(** For each spatial predicate [Definition f(_): mpred],
  there should be _one_ "local fact", a lemma of the form
  [f(_) |-- !! _].  On the right hand side, put all the propositions
  you can derive from [f(_)].  In this case, we know:
  - [p] is either a pointer or null (it's never [Vundef], or [Vfloat],
     or a nonzero [Vint]).
  - [p] is null, if and only if [sigma] is nil. *)
Proof.
intros.
(** We will prove this entailment by induction on sigma *)
revert p; induction sigma; intros p.
- (** In the base case, [sigma] is nil.  We can unfold the definition
   of [listrep] to see what that means. *)
 unfold listrep.
 (** Now we have an entailment with a proposition [p=nullval] on the left.
 To move that proposition above the line, we could do [Intros], but
 it's easier just to call on [entailer!] to see how it can simplify (and perhaps
 partially solve) this entailment goal: *)
  entailer!.
 (* The [entailer!] has left an ordinary proposition, which is easy to solve. *)
  split; auto.
- (** In the inductive case, we can again unfold the definition
   of [listrep (a::sigma)]; but then it's good to fold [listrep sigma].
   Replace the semicolon [;] with a period in the next line, to see why. *)
 unfold listrep; fold listrep.

 (** Warning!  Sometimes [entailer!] is too aggressive.  If we use it
  here, it will throw away the left-hand side because it doesn't
  understand how to look inside an EXistential quantitier.  The
  exclamation point [!] is a warning that [entailer!] can turn a
  provable goal into an unprovable goal.  Uncomment the next line
  and see what happens.  Then put the comment marks back. *)
 (* entailer!. *)

 (** The preferred way to handle [EX y:t] on the left-hand-side of an
 entailment is to use [Intros y.]  Uncomment this to try it out, then
 put the comment marks back. *)
 (* Intros y. *)

 (** A less agressive entailment-reducer is [entailer] without the
    exclamation point. This one never turns a provable goal into an
    unprovable goal.  Here it will Intro the EX-bound variable y. *)
 entailer.

 (** Should you use [entailer!] or [entailer] in ordinary proofs?
  Usually [entailer!] is best: it's faster, and it does more work for you.
  Only if you  find that [entailer!] has gone into a dead end, should
  you use [entailer] instead. *)

 (** Here it is safe to use [entailer!] *)
 entailer!.
 (** Notice that entailer! has put several facts above the line:
  [field_compatible t_list [] p] and [value_fits t_list (a,y)] come from the
  [saturate_local] hint database, from the [data_at] conjunct;  and
  [is_pointer_or_null y] and [y=nullval <-> sigma=[]] come from the
  the [listrep] conjunct, using the induction hypothesis [IHsigma].

  Now, let's split the goal and take the two cases separately. *)
 split; intro.
 +
  clear - H H2.
  subst p.
  (** It happens that [field_compatible _ _ p] implies [isptr p], *)
Check field_compatible_isptr.
   (* : forall (t : type) (path : list gfield) (p : val),
       field_compatible t path p -> isptr p *)
   (**  The predicate isptr excludes the null pointer, *)
Print isptr.
  (* = fun v : val => match v with Vptr _ _ => True | _ => False end *)
Print nullval.
  (* = if Archi.ptr64 then Vlong Int64.zero else Vint Int.zero *)
  (** Therefore [H] is a contradiction.  We can proceed with, *)
Check field_compatible_nullval.
  (* = forall (CS : compspecs) (t : type) (f : list gfield) (P : Type),
       field_compatible t f nullval -> P *)
  eapply field_compatible_nullval; eauto.
 + (*The case  [a::sigma=[] -> p=nullval] is easy, by inversion: *)
   inversion H2.
Qed.

(** Now we add this lemma to the Hint database called [saturate_local] *)
Hint Resolve listrep_local_facts : saturate_local.

(* ----------------------------------------------------------------- *)
(** *** Valid pointers, and the [valid_pointer] Hint database *)

(** In the C language, you can do a pointer comparison such as [p!=NULL] or
    [p==q] only if [p] is a _valid pointer_, that is, either NULL or actually
    pointing within an allocated object.  One way to prove that [p] is
    valid is if, for example,   [data_at Tsh t_list (h,y) p], meaning that [p]
    is pointing at a list cell.  There is a hint database [valid_pointer] from
    which the predicate [valid_pointer p] can be proved automatically.
    For example: *)

Lemma struct_list_valid_pointer_example:
  forall h y p,
   data_at Tsh t_list (h,y) p |-- valid_pointer p.
Proof.
  intros.
  auto with valid_pointer.
Qed.

(** However, the hint database does not know about user-defined
    separation-logic predicates ([mpred]) such as [listrep]; for example: *)

Lemma listrep_valid_pointer_example:
 forall sigma p,
   listrep sigma p |-- valid_pointer p.
Proof.
 intros.
 auto with valid_pointer.
 (** Notice that [auto with...] did not solve the proof goal *)
Abort.

(** Therefore, we should prove the appropriate lemma, and add it to the
   Hint database.  *)

Lemma listrep_valid_pointer:
  forall sigma p,
   listrep sigma p |-- valid_pointer p.
Proof.
 intros.
 (** The main point is to unfold listrep. *)
 unfold listrep.
 (** Now we can prove it by case analysis on sigma; we don't even need
   induction. *)
 destruct sigma; simpl.
- (** The  nil case is easy: *)
  hint.
  entailer!.
- (**  The cons case *)
  Intros y.
  (** Now this solves using the Hint database [valid_pointer], because the
     [data_at Tsh t_list (v,y) p] on the left is enough to prove the goal. *)
  auto with valid_pointer.
Qed.

(** Now we add this lemma to the Hint database *)
Hint Resolve listrep_valid_pointer : valid_pointer.

(* ================================================================= *)
(** ** Specification of the [reverse] function.

    A [funspec] characterizes the precondition required for calling the function
  and the postcondition guaranteed by the function. *)
Definition reverse_spec : ident * funspec :=
 DECLARE _reverse
  WITH sigma : list val, p: val
  PRE  [ tptr t_list ]
     PROP ()  PARAMS (p)  SEP (listrep sigma p)
  POST [ (tptr t_list) ]
    EX q:val,
     PROP ()  RETURN (q)  SEP (listrep(rev sigma) q).

(**
  - The WITH clause says, there is a value [sigma: list val]
      and a value [p: val], visible in both the precondition and
      the postcondition.
  - The PREcondition says,
     - There is one function-parameter, whose C type is
         "pointer to struct list"
     - PARAMS:  The parameter contains the Coq value [p];
     - SEP: in memory at address [p] there is a linked list
          representing [sigma].
  - The POSTcondition says,
     - the function returns a value whose C type is
           "pointer to struct list"; and
     - there exists a value [q: val], such that
     - RETURN: the function's return value is [q]
     - SEP: in memory at address [q] there is a linked list representing
           [rev sigma].

  The global function spec characterizes the preconditions/postconditions of
  all the functions that your proved-correct program will call. Normally you
  include all the functions here, but in this tutorial example we include
  only one. *)
Definition Gprog : funspecs := [ reverse_spec ].

(* ================================================================= *)
(** ** Proof of the [reverse] function *)

(** For each function definition in the C program, prove that the
 function-body (in this case, f_reverse) satisfies its specification
  (in this case, reverse_spec).  *)
Lemma body_reverse: semax_body Vprog Gprog f_reverse reverse_spec.
Proof.

(** The start_function tactic "opens up" a semax_body
    proof goal into a Hoare triple. *)

start_function.

(**  As usual, the current assertion (precondition) is derived from the PRE
  clause of the function specification, [reverse_spec], and the current command 
  [ w=0; ...more... ] is the function body of [f_reverse].

  The first statement (command) in the function-body is the assignment
  statement  [w=NULL;], where [NULL] is a C [#define] that exands to
  "cast 0 to void-pointer", [(void * )0], here ugly-printed as
  [(tptr tvoid)(0)].  To apply the separation-logic assignment rule to
  this command, simply use the tactic [forward] : *)

forward.  (* w = NULL; *)

(** The new [semax] judgment is for the rest of the function body _after_
  the command [w=NULL].  The precondition of this [semax] is actually the
  postcondition of the [w=NULL] statement.  It's much like the precondition
  of [w=NULL], but contains the additional LOCAL fact,
  [temp _w (Vint (Int.repr 0))], that is, the variable [_w] contains [nullval].

  We can view the Hoare-logic proof of this program as a "symbolic execution",
  where the symbolic states are assertions.  We can symbolically execute
  the next command by saying [forward] again. *)

forward.  (* v = p; *)

(** Examine the precondition, and notice that now we have the additional
    fact, [temp _v p]. *)

(** We cannot the next step using [forward] ... *)

Fail forward.

(** ... because the next command is a [while] loop. *)

(* ================================================================= *)
(** ** The loop invariant *)

(** To prove a while-loop, you must supply a loop invariant,
    such as

     (EX s1 ... PROP(...)LOCAL(...)SEP(...). 
*)

forward_while
   (EX s1: list val, EX s2 : list val,
    EX w: val, EX v: val,
     PROP (sigma = rev s1 ++ s2)
     LOCAL (temp _w w; temp _v v)
     SEP (listrep s1 w; listrep s2 v)).

(** The forward_while tactic leaves four subgoals, 
  which we mark with - (the Coq "bullet") *)
- (* Prove that (current) precondition implies the loop invariant *)
hint.

(** On the left-hand side of this entailment is the precondition
  (that we had already established by forward symbolic execution to this
  point) for the entire while-loop.  On the right-hand side is the loop
  invariant, that we just gave to the [forward_while] tactic.  Because
  the right_hand side has for existentials, a good proof strategy is to
  choose values for them, using the [Exists] tactic. *)

Exists (@nil val) sigma nullval p.

(** Now we have a quantifier-free proof goal; let us see whether [entailer!]
    can solve some parts of it. *)

entailer!.

(** Indeed, the [entailer!] did a fine job.  What's left is a property of our
    user-defined [listrep] predicate:  [emp |-- listrep [] nullval]. *)

unfold listrep.

(** Now that the user-defined predicate is unfolded, [entailer!] can solve
     the residual entailment. *)

entailer!.

- (* Prove that loop invariant implies typechecking of loop condition *)
hint.

(** The second subgoal of [forward_while] is to prove that the loop-test
     condition can execute without crashing.   Consider, for example,
     the C-language while loop,  [while (a[i]>0) ...], where the value of [i]
     might exceed the bounds of the array.  Then this would be a
     "buffer overrun", and is "undefined behavior" ("stuck") in the C semantics.
     We must prove that, given the current precondition (in this case,
     the loop invariant), the loop test is not "undefined behavior."
     This proof goal takes the form, [current-precondition |-- tc_expr Delta e],
     where [e] is the loop-test expression.  You can pronounce [tc_expr] as
     "type-check expression", since the Verifiable C type-checker ensures
     that such expressions are safe (sometimes with a subgoal for you to prove).

     Fortunately, in most cases the [entailer!] solves [tc_expr] goals
     completely automatically:  *)

entailer!.

- (* Prove that loop body preserves invariant *)
hint.

(** As usual in any Hoare logic (including Separation Logic), we need to prove
   that the loop body preserves the loop invariant, more precisely,
   - {Inv /\ Test} body {Inv}
   where Test is the loop-test condition.  Here, the loop-test condition
   in the original C code is [(v)], and its manifestation above the line is
   the hypothesis [HRE: isptr v], meaning that [v] is a (non-null) pointer.

   The loop invariant was [EX s1:_, EX s2:_, EX w:_, EX v:_, ...], and here
   all the existentially quantified variables on the left side of the entailment
   have been moved above the line:  [s1, s2: val] and [w,v: val].

   The PROP part of the loop invariant was [sigma = rev s1 ++ s2], and
   it has also been moved above the line, as hypothesis [H].

   So now we would like to do forward-symbolic execution through
   the four assignment statements in the loop body. *)

Fail forward.

(** But we cannot go forward through [t=v->tail;] because that would
   require a SEP conjunct in the precondition of the form
   [data_at sh t_list (_,_) v], and there is no such conjunct.  Actually,
   there is such a conjunct, but it is hiding inside [listrep s2 v].
   That is, there is such a conjunct as long as [s2] is not [nil].
   Let's do case analysis on s2: *)

destruct s2 as [ | h r].
 + (* s2=nil *)

   (** Suppose [s2=nil].  If we unfold [listrep] . . . *)
   unfold listrep at 2.
   (** then we learn that [v=nullval].  To move this fact (or any proposition)
    from the precondition to above-the-line, we use [Intros]: *)

   Intros.

   (** Now, above the line, we have [v=nullval] and [isptr v]; 
       this is a contradiction. *)

   subst. contradiction.

 + (* s2=h::r *)

   (** Suppose [s2=h::r].  We can unfold/fold the [listrep] conjunct for [h::r];
    if you don't remember why we do [unfold/fold], then replace the semicolon
    (between the fold and the unfold) with a period and see what happens. *)

   unfold listrep at 2; fold listrep.

   (** By the definition of [listrep], at address [v] there must exist a value [y]
     and a list cell containing (h,y).  So let us move [y] above the line: *)

   Intros y.

   (** Now we have the appropriate SEP conjuncts to be able to go [forward]
   through the loop body *)

   forward. (* t = v->tail *)
   forward. (* v->tail = w; *)
   forward. (* w = v; *)
   forward. (* v = t; *)

   (** At the end of loop body; we must reestablish the loop invariant.
   The left-hand-side of this entailment is the current assertion (after
   the loop body); the right-hand side is simply our loop invariant.
   (Unfortunately, the [forward_while] tactic has "uncurried" the existentials
   into a single EX that binds a 4-tuple.)
   Since the proof goal is a complicated-looking entailment, let's see
   if [entailer!] can simplify it a bit: *)

   entailer!.

   (** Now, we can provide new values for [s1,s2,w,v] to instantiate the
   four existentials; these are, respectively, [h::s1,r,v,y]. *)

   Exists (h::s1,r,v,y).

   (** Again, we have a complicated-looking entailment; we ask [entailer!]
   to reduce it some more. *)

   entailer!.
   * simpl. rewrite app_ass. auto.
   * unfold listrep at 3; fold listrep.
     Exists w. entailer!.

- (* after the loop *)
  (** As usual in any Hoare logic (including Separation Logic), the 
    postcondition of a while-loop is {Inv /\ not Test}, where Inv is the 
    loop invariant and Test is the loop test.  Here, all the EXistentials
    and PROPs of the loop invariant have been moved above the line as
    [s1,s2,w,v,HRE,H].

    We can always go [forward] through a [return] statement: *)
forward.  (* return w;

    Now we must prove that the current assertion (after the while-loop)
  entails the function postcondition.  The left-hand side of this entailment
  is what we had just before [forward] through the [return];
  the right-hand side is the postcondition of [reverse_spec],
  after the local variables (etc.) have been simplified away.  We must
  demonstrate a pointer [q] (here it's called [x]) that satisfies the various
  conditions.  Here it's easy to find [x], since it's constrained to be
  equal to [w]: *)

Exists w; entailer!.
rewrite (proj1 H1) by auto.
unfold listrep at 2; fold listrep.
entailer!.
rewrite <- app_nil_end, rev_involutive.
auto.
Qed.

(* ================================================================= *)
(** ** Why separation logic? *)

(** If we review our functional correctness proof for [reverse.c], it may
  not be obvious why we need separation logic at all. Let's take a close look.

First, we build "separation" into the definition of [listrep]. The following is
our definition:

  Fixpoint listrep (sigma: list val) (p: val) : mpred :=
   match sigma with
   | h::hs => EX y:val, data_at Tsh t_list (h,y) p  *  listrep hs y
   | nil =>  !! (p = nullval) && emp
   end.

In the nonempty list case, the head element is described by

   data_at Tsh t_list (h,y) p

which is separated (by the separating conjunction * ) from the rest of the list

   listrep hs y.

This separation ensures that no address could be used for more than once in a
linked list. For example, considering a linked list of length at least 2,

   listrep (a :: b :: l) x.

We know that there must be two addresses [y] and [z] such that

      data_at Tsh t_list (a,y) x *
      data_at Tsh t_list (b,z) y *
      listrep l z.

The "separating conjunction" [*] tells us that [x] and [y] must be different!
Formally, we can prove the following two lemmas: *)

Lemma listrep_len_ge2_fact: forall (a b x: val) (l: list val),
  listrep (a :: b :: l) x |--
  EX y: val, EX z: val,
      data_at Tsh t_list (a,y) x *
      data_at Tsh t_list (b,z) y *
      listrep l z.
Proof.
  intros.
  unfold listrep; fold listrep.
  Intros y z.
  Exists y z.
  cancel.
Qed.

Lemma listrep_len_ge2_address_different: forall (a b x y z: val) (l: list val),
  data_at Tsh t_list (a,y) x *
  data_at Tsh t_list (b,z) y *
  listrep l z |--
  !! (x <> y).
Proof.
  intros.
  (** To prove that the addresses are different, we do case analysis first.
    If [x = y], we use the following theorem: *)
  Check data_at_conflict.
    (* : forall (sh : Share.t) (t : type) (v v' : reptype t) (p : val),
         sepalg.nonidentity sh -> 0 < sizeof t ->
         data_at sh t v p * data_at sh t v' p |-- FF *)
  (** It says that we can derives address anti-aliasing from the "separation"
    defined by [*]. *)
  (** If [x <> y], the right side is already proved. *)
  destruct (Val.eq x y); [| apply prop_right; auto].
  subst x.
  sep_apply (data_at_conflict Tsh t_list (a, y)).
  + auto.
  + entailer!.
Qed.

(** Actually, even the property [x<>y] is not strong enough!  We need to
  know that [x] does not overlap with _any field_ of record [y],
  for example (in C notation)  [x != &(y->tail)] and [&(x->tail) != y].
  Otherwise, when storing into [y->tail], we couldn't know that [x->head]
  is not altered.

 Without separation logic, we could still define [listrep'] using extra
 clauses for address anti-aliasing. For example, a length-3 linked list
 [listrep (a :: b :: c :: nil) x] can be: exists [y] and [z], such that [(a, y)]
 is stored at [x], [(b, z)] is stored at [y], [(c, nullval)] is stored at [z] and
 [x], [y] and [z] are different from each other. In general, that assertion will
 be quadratically long (as a function of the length of the linked list).
 Then, to make sure [x->head] is not at the same address as [y->tail], we'd need
 even more assertions.

 In our program correctness proof, we do (implicitly) use the fact that
 different [SEP] clauses describe disjoint heaplets. Here is an
 intermediate step in the proof of [body_reverse].

 (We rarely state intermediate proof goals such as this one.
  We do it here to illustrate a point about separating conjunction.  *)

Lemma body_reverse_step: forall
  {Espec : OracleKind}
  (sigma : list val)
  (s1 : list val)
  (h : val)
  (r : list val)
  (w v : val)
  (HRE : isptr v)
  (H : sigma = rev s1 ++ h :: r)
  (y : val),
  semax (func_tycontext f_reverse Vprog Gprog nil)
    (PROP ( )
     LOCAL (temp _t y; temp _w w; temp _v v)
     SEP (listrep s1 w; data_at Tsh t_list (h, y) v; listrep r y))
    (Ssequence
       (Sassign
          (Efield
             (Ederef (Etempvar _v (tptr (Tstruct _list noattr)))
                     (Tstruct _list noattr))
             _tail (tptr (Tstruct _list noattr)))
          (Etempvar _w (tptr (Tstruct _list noattr))))
       (Ssequence (Sset _w (Etempvar _v (tptr (Tstruct _list noattr))))
                  (Sset _v (Etempvar _t (tptr (Tstruct _list noattr))))))
    (normal_ret_assert
       (PROP ( )
        LOCAL (temp _v y; temp _w v; temp _t y)
        SEP (listrep s1 w; data_at Tsh t_list (h, w) v; listrep r y))).
Proof.
  intros.
  abbreviate_semax.
(** Now, our proof goal is:

  semax Delta
    (PROP ( )
     LOCAL (temp _t y; temp _w w; temp _v v)
     SEP (listrep s1 w; data_at Tsh t_list (h, y) v; listrep r y))
    ((_v -> _tail) = _w; MORE_COMMANDS)
    POSTCONDITION.

The next [forward] tactic will do symbolic execution of [v->tail = w]. *)
   forward. (* v->tail = w;

    It turns the precondition into:

     PROP ( )
     LOCAL (temp _t y; temp _w w; temp _v v)
     SEP (listrep s1 w; data_at Tsh t_list (h, w) v; listrep r y).

It is no problem that the separating conjunct [data_at Tsh t_list (h, y) v] is
turned into [data_at Tsh t_list (h, w) v]. But why weren't the other separating
conjuncts like [listrep s1 w] affected?

Because they are separated! The separation ensures that address [v] is not used
in the linked list described by [listrep s1 w]. *)
Abort.

(** When C programs manipulate pointer data structures (or slices of arrays),
  address anti-aliasing plays an important role in their  correctness proofs.
  Separation logic is essential for reasoning about updates to these structures.
  Verifiable C's SEP clause ensures separation between all its conjuncts. *)

(* 2020-09-18 15:39 *)
