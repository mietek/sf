(** * MoreInd: More on Induction *)

Require Export "ProofObjects".

(* ##################################################### *)
(** * Induction Principles *)

(** This is a good point to pause and take a deeper look at induction
    principles. 

    Every time we declare a new [Inductive] datatype, Coq
    automatically generates and proves an _induction principle_ 
    for this type.

    The induction principle for a type [t] is called [t_ind].  Here is
    the one for natural numbers: *)

Check nat_ind.
(*  ===> nat_ind : 
           forall P : nat -> Prop,
              P 0  ->
              (forall n : nat, P n -> P (S n))  ->
              forall n : nat, P n  *)

(** *** *)
(** The [induction] tactic is a straightforward wrapper that, at
    its core, simply performs [apply t_ind].  To see this more
    clearly, let's experiment a little with using [apply nat_ind]
    directly, instead of the [induction] tactic, to carry out some
    proofs.  Here, for example, is an alternate proof of a theorem
    that we saw in the [Basics] chapter. *)

Theorem mult_0_r' : forall n:nat, 
  n * 0 = 0.
Proof.
  apply nat_ind. 
  Case "O". reflexivity.
  Case "S". simpl. intros n IHn. rewrite -> IHn. 
    reflexivity.  Qed.


(** This proof is basically the same as the earlier one, but a
    few minor differences are worth noting.  First, in the induction
    step of the proof (the ["S"] case), we have to do a little
    bookkeeping manually (the [intros]) that [induction] does
    automatically.

    Second, we do not introduce [n] into the context before applying
    [nat_ind] -- the conclusion of [nat_ind] is a quantified formula,
    and [apply] needs this conclusion to exactly match the shape of
    the goal state, including the quantifier.  The [induction] tactic
    works either with a variable in the context or a quantified
    variable in the goal.

    Third, the [apply] tactic automatically chooses variable names for
    us (in the second subgoal, here), whereas [induction] lets us
    specify (with the [as...]  clause) what names should be used.  The
    automatic choice is actually a little unfortunate, since it
    re-uses the name [n] for a variable that is different from the [n]
    in the original theorem.  This is why the [Case] annotation is
    just [S] -- if we tried to write it out in the more explicit form
    that we've been using for most proofs, we'd have to write [n = S
    n], which doesn't make a lot of sense!  All of these conveniences
    make [induction] nicer to use in practice than applying induction
    principles like [nat_ind] directly.  But it is important to
    realize that, modulo this little bit of bookkeeping, applying
    [nat_ind] is what we are really doing. *)

(** **** Exercise: 2 stars, optional (plus_one_r')  *)
(** Complete this proof as we did [mult_0_r'] above, without using
    the [induction] tactic. *)

Theorem plus_one_r' : forall n:nat, 
  n + 1 = S n.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** Coq generates induction principles for every datatype defined with
    [Inductive], including those that aren't recursive. (Although 
    we don't need induction to prove properties of non-recursive 
    datatypes, the idea of an induction principle still makes sense
    for them: it gives a way to prove that a property holds for all
    values of the type.)
    
    These generated principles follow a similar pattern. If we define a
    type [t] with constructors [c1] ... [cn], Coq generates a theorem
    with this shape:
    t_ind :
       forall P : t -> Prop,
            ... case for c1 ... ->
            ... case for c2 ... ->
            ...                
            ... case for cn ... ->
            forall n : t, P n
    The specific shape of each case depends on the arguments to the
    corresponding constructor.  Before trying to write down a general
    rule, let's look at some more examples. First, an example where
    the constructors take no arguments: *)

Inductive yesno : Type :=
  | yes : yesno
  | no : yesno.

Check yesno_ind. 
(* ===> yesno_ind : forall P : yesno -> Prop, 
                      P yes  ->
                      P no  ->
                      forall y : yesno, P y *)

(** **** Exercise: 1 star, optional (rgb)  *)
(** Write out the induction principle that Coq will generate for the
    following datatype.  Write down your answer on paper or type it
    into a comment, and then compare it with what Coq prints. *)

Inductive rgb : Type :=
  | red : rgb
  | green : rgb
  | blue : rgb.
Check rgb_ind.
(** [] *)

(** Here's another example, this time with one of the constructors
    taking some arguments. *)

Inductive natlist : Type :=
  | nnil : natlist
  | ncons : nat -> natlist -> natlist.

Check natlist_ind.
(* ===> (modulo a little variable renaming for clarity)
   natlist_ind :
      forall P : natlist -> Prop,
         P nnil  ->
         (forall (n : nat) (l : natlist), P l -> P (ncons n l)) ->
         forall n : natlist, P n *)

(** **** Exercise: 1 star, optional (natlist1)  *)
(** Suppose we had written the above definition a little
   differently: *)

Inductive natlist1 : Type :=
  | nnil1 : natlist1
  | nsnoc1 : natlist1 -> nat -> natlist1.

(** Now what will the induction principle look like? *)
(** [] *)

(** From these examples, we can extract this general rule:

    - The type declaration gives several constructors; each
      corresponds to one clause of the induction principle.
    - Each constructor [c] takes argument types [a1]...[an].
    - Each [ai] can be either [t] (the datatype we are defining) or
      some other type [s].
    - The corresponding case of the induction principle
      says (in English):
        - "for all values [x1]...[xn] of types [a1]...[an], if [P]
           holds for each of the inductive arguments (each [xi] of
           type [t]), then [P] holds for [c x1 ... xn]". 

*)



(** **** Exercise: 1 star, optional (byntree_ind)  *)
(** Write out the induction principle that Coq will generate for the
    following datatype.  Write down your answer on paper or type it
    into a comment, and then compare it with what Coq prints. *)

Inductive byntree : Type :=
 | bempty : byntree  
 | bleaf  : yesno -> byntree
 | nbranch : yesno -> byntree -> byntree -> byntree.
(** [] *)


(** **** Exercise: 1 star, optional (ex_set)  *)
(** Here is an induction principle for an inductively defined
    set.
      ExSet_ind :
         forall P : ExSet -> Prop,
             (forall b : bool, P (con1 b)) ->
             (forall (n : nat) (e : ExSet), P e -> P (con2 n e)) ->
             forall e : ExSet, P e
    Give an [Inductive] definition of [ExSet]: *)

Inductive ExSet : Type :=
  (* FILL IN HERE *)
.
(** [] *)

(** What about polymorphic datatypes?

    The inductive definition of polymorphic lists
      Inductive list (X:Type) : Type :=
        | nil : list X
        | cons : X -> list X -> list X.
    is very similar to that of [natlist].  The main difference is
    that, here, the whole definition is _parameterized_ on a set [X]:
    that is, we are defining a _family_ of inductive types [list X],
    one for each [X].  (Note that, wherever [list] appears in the body
    of the declaration, it is always applied to the parameter [X].)
    The induction principle is likewise parameterized on [X]:
     list_ind :
       forall (X : Type) (P : list X -> Prop),
          P [] ->
          (forall (x : X) (l : list X), P l -> P (x :: l)) ->
          forall l : list X, P l
   Note the wording here (and, accordingly, the form of [list_ind]):
   The _whole_ induction principle is parameterized on [X].  That is,
   [list_ind] can be thought of as a polymorphic function that, when
   applied to a type [X], gives us back an induction principle
   specialized to the type [list X]. *)

(** **** Exercise: 1 star, optional (tree)  *)
(** Write out the induction principle that Coq will generate for
   the following datatype.  Compare your answer with what Coq
   prints. *)

Inductive tree (X:Type) : Type :=
  | leaf : X -> tree X
  | node : tree X -> tree X -> tree X.
Check tree_ind.
(** [] *)

(** **** Exercise: 1 star, optional (mytype)  *)
(** Find an inductive definition that gives rise to the
    following induction principle:
      mytype_ind :
        forall (X : Type) (P : mytype X -> Prop),
            (forall x : X, P (constr1 X x)) ->
            (forall n : nat, P (constr2 X n)) ->
            (forall m : mytype X, P m -> 
               forall n : nat, P (constr3 X m n)) ->
            forall m : mytype X, P m                   
*) 
(** [] *)

(** **** Exercise: 1 star, optional (foo)  *)
(** Find an inductive definition that gives rise to the
    following induction principle:
      foo_ind :
        forall (X Y : Type) (P : foo X Y -> Prop),
             (forall x : X, P (bar X Y x)) ->
             (forall y : Y, P (baz X Y y)) ->
             (forall f1 : nat -> foo X Y,
               (forall n : nat, P (f1 n)) -> P (quux X Y f1)) ->
             forall f2 : foo X Y, P f2       
*) 
(** [] *)

(** **** Exercise: 1 star, optional (foo')  *)
(** Consider the following inductive definition: *)

Inductive foo' (X:Type) : Type :=
  | C1 : list X -> foo' X -> foo' X
  | C2 : foo' X.

(** What induction principle will Coq generate for [foo']?  Fill
   in the blanks, then check your answer with Coq.)
     foo'_ind :
        forall (X : Type) (P : foo' X -> Prop),
              (forall (l : list X) (f : foo' X),
                    _______________________ -> 
                    _______________________   ) ->
             ___________________________________________ ->
             forall f : foo' X, ________________________
*)

(** [] *)

(* ##################################################### *)
(** ** Induction Hypotheses *)

(** Where does the phrase "induction hypothesis" fit into this story?

    The induction principle for numbers
       forall P : nat -> Prop,
            P 0  ->
            (forall n : nat, P n -> P (S n))  ->
            forall n : nat, P n
   is a generic statement that holds for all propositions
   [P] (strictly speaking, for all families of propositions [P]
   indexed by a number [n]).  Each time we use this principle, we
   are choosing [P] to be a particular expression of type
   [nat->Prop].

   We can make the proof more explicit by giving this expression a
   name.  For example, instead of stating the theorem [mult_0_r] as
   "[forall n, n * 0 = 0]," we can write it as "[forall n, P_m0r
   n]", where [P_m0r] is defined as... *)

Definition P_m0r (n:nat) : Prop := 
  n * 0 = 0.

(** ... or equivalently... *)

Definition P_m0r' : nat->Prop := 
  fun n => n * 0 = 0.

(** Now when we do the proof it is easier to see where [P_m0r]
    appears. *)

Theorem mult_0_r'' : forall n:nat, 
  P_m0r n.
Proof.
  apply nat_ind.
  Case "n = O". reflexivity.
  Case "n = S n'". 
    (* Note the proof state at this point! *)
    intros n IHn. 
    unfold P_m0r in IHn. unfold P_m0r. simpl. apply IHn. Qed.

(** This extra naming step isn't something that we'll do in
    normal proofs, but it is useful to do it explicitly for an example
    or two, because it allows us to see exactly what the induction
    hypothesis is.  If we prove [forall n, P_m0r n] by induction on
    [n] (using either [induction] or [apply nat_ind]), we see that the
    first subgoal requires us to prove [P_m0r 0] ("[P] holds for
    zero"), while the second subgoal requires us to prove [forall n',
    P_m0r n' -> P_m0r n' (S n')] (that is "[P] holds of [S n'] if it
    holds of [n']" or, more elegantly, "[P] is preserved by [S]").
    The _induction hypothesis_ is the premise of this latter
    implication -- the assumption that [P] holds of [n'], which we are
    allowed to use in proving that [P] holds for [S n']. *)

(* ##################################################### *)
(** ** More on the [induction] Tactic *)

(** The [induction] tactic actually does even more low-level
    bookkeeping for us than we discussed above.

    Recall the informal statement of the induction principle for
    natural numbers:
      - If [P n] is some proposition involving a natural number n, and
        we want to show that P holds for _all_ numbers n, we can
        reason like this:
          - show that [P O] holds
          - show that, if [P n'] holds, then so does [P (S n')]
          - conclude that [P n] holds for all n.
    So, when we begin a proof with [intros n] and then [induction n],
    we are first telling Coq to consider a _particular_ [n] (by
    introducing it into the context) and then telling it to prove
    something about _all_ numbers (by using induction).

    What Coq actually does in this situation, internally, is to
    "re-generalize" the variable we perform induction on.  For
    example, in our original proof that [plus] is associative...
*)

Theorem plus_assoc' : forall n m p : nat, 
  n + (m + p) = (n + m) + p.   
Proof.
  (* ...we first introduce all 3 variables into the context,
     which amounts to saying "Consider an arbitrary [n], [m], and
     [p]..." *)
  intros n m p. 
  (* ...We now use the [induction] tactic to prove [P n] (that
     is, [n + (m + p) = (n + m) + p]) for _all_ [n],
     and hence also for the particular [n] that is in the context
     at the moment. *)
  induction n as [| n'].
  Case "n = O". reflexivity.
  Case "n = S n'". 
    (* In the second subgoal generated by [induction] -- the
       "inductive step" -- we must prove that [P n'] implies 
       [P (S n')] for all [n'].  The [induction] tactic 
       automatically introduces [n'] and [P n'] into the context
       for us, leaving just [P (S n')] as the goal. *)
    simpl. rewrite -> IHn'. reflexivity.  Qed.


(** It also works to apply [induction] to a variable that is
   quantified in the goal. *)

Theorem plus_comm' : forall n m : nat, 
  n + m = m + n.
Proof.
  induction n as [| n']. 
  Case "n = O". intros m. rewrite -> plus_0_r. reflexivity.
  Case "n = S n'". intros m. simpl. rewrite -> IHn'. 
    rewrite <- plus_n_Sm. reflexivity.  Qed.

(** Note that [induction n] leaves [m] still bound in the goal --
    i.e., what we are proving inductively is a statement beginning
    with [forall m].

    If we do [induction] on a variable that is quantified in the goal
    _after_ some other quantifiers, the [induction] tactic will
    automatically introduce the variables bound by these quantifiers
    into the context. *)

Theorem plus_comm'' : forall n m : nat, 
  n + m = m + n.
Proof.
  (* Let's do induction on [m] this time, instead of [n]... *)
  induction m as [| m']. 
  Case "m = O". simpl. rewrite -> plus_0_r. reflexivity.
  Case "m = S m'". simpl. rewrite <- IHm'.
    rewrite <- plus_n_Sm. reflexivity.  Qed.

(** **** Exercise: 1 star, optional (plus_explicit_prop)  *)
(** Rewrite both [plus_assoc'] and [plus_comm'] and their proofs in
    the same style as [mult_0_r''] above -- that is, for each theorem,
    give an explicit [Definition] of the proposition being proved by
    induction, and state the theorem and proof in terms of this
    defined proposition.  *)

(* FILL IN HERE *)
(** [] *)


(** ** Generalizing Inductions. *)

(** One potentially confusing feature of the [induction] tactic is
that it happily lets you try to set up an induction over a term
that isn't sufficiently general.  The net effect of this will be 
to lose information (much as [destruct] can do), and leave
you unable to complete the proof. Here's an example: *)

Lemma one_not_beautiful_FAILED: ~ beautiful 1. 
Proof.
  intro H.
  (* Just doing an [inversion] on [H] won't get us very far in the [b_sum]
    case. (Try it!). So we'll need induction. A naive first attempt: *)
  induction H. 
  (* But now, although we get four cases, as we would expect from
     the definition of [beautiful], we lose all information about [H] ! *) 
Abort.

(** The problem is that [induction] over a Prop only works properly over 
   completely general instances of the Prop, i.e. one in which all
   the arguments are free (unconstrained) variables. 
   In this respect it behaves more
   like [destruct] than like [inversion]. 

   When you're tempted to do use [induction] like this, it is generally
   an indication that you need to be proving something more general.
   But in some cases, it suffices to pull out any concrete arguments
   into separate equations, like this: *)

Lemma one_not_beautiful: forall n, n = 1 -> ~ beautiful n. 
Proof.
 intros n E H.
  induction H  as [| | | p q Hp IHp Hq IHq]. 
    Case "b_0".
      inversion E.
    Case "b_3". 
      inversion E. 
    Case "b_5". 
      inversion E. 
    Case "b_sum". 
      (* the rest is a tedious case analysis *)
      destruct p as [|p'].
      SCase "p = 0".
        destruct q as [|q'].
        SSCase "q = 0". 
          inversion E.
        SSCase "q = S q'".
          apply IHq. apply E. 
      SCase "p = S p'". 
        destruct q as [|q'].
        SSCase "q = 0". 
          apply IHp.  rewrite plus_0_r in E. apply E. 
        SSCase "q = S q'".
          simpl in E. inversion E.  destruct p'.  inversion H0.  inversion H0. 
Qed.

(** There's a handy [remember] tactic that can generate the second
proof state out of the original one. *)

Lemma one_not_beautiful': ~ beautiful 1. 
Proof.
  intros H.  
  remember 1 as n eqn:E. 
  (* now carry on as above *)
  induction H.   
Admitted.


(* ####################################################### *)
(** * Informal Proofs (Advanced) *)

(** Q: What is the relation between a formal proof of a proposition
       [P] and an informal proof of the same proposition [P]?

    A: The latter should _teach_ the reader how to produce the
       former.

    Q: How much detail is needed??

    Unfortunately, There is no single right answer; rather, there is a
    range of choices.

    At one end of the spectrum, we can essentially give the reader the
    whole formal proof (i.e., the informal proof amounts to just
    transcribing the formal one into words).  This gives the reader
    the _ability_ to reproduce the formal one for themselves, but it
    doesn't _teach_ them anything.

   At the other end of the spectrum, we can say "The theorem is true
   and you can figure out why for yourself if you think about it hard
   enough."  This is also not a good teaching strategy, because
   usually writing the proof requires some deep insights into the
   thing we're proving, and most readers will give up before they
   rediscover all the same insights as we did.

   In the middle is the golden mean -- a proof that includes all of
   the essential insights (saving the reader the hard part of work
   that we went through to find the proof in the first place) and
   clear high-level suggestions for the more routine parts to save the
   reader from spending too much time reconstructing these
   parts (e.g., what the IH says and what must be shown in each case
   of an inductive proof), but not so much detail that the main ideas
   are obscured.

   Another key point: if we're comparing a formal proof of a
   proposition [P] and an informal proof of [P], the proposition [P]
   doesn't change.  That is, formal and informal proofs are _talking
   about the same world_ and they _must play by the same rules_. *)
(** ** Informal Proofs by Induction *)

(** Since we've spent much of this chapter looking "under the hood" at
    formal proofs by induction, now is a good moment to talk a little
    about _informal_ proofs by induction.

    In the real world of mathematical communication, written proofs
    range from extremely longwinded and pedantic to extremely brief
    and telegraphic.  The ideal is somewhere in between, of course,
    but while you are getting used to the style it is better to start
    out at the pedantic end.  Also, during the learning phase, it is
    probably helpful to have a clear standard to compare against.
    With this in mind, we offer two templates below -- one for proofs
    by induction over _data_ (i.e., where the thing we're doing
    induction on lives in [Type]) and one for proofs by induction over
    _evidence_ (i.e., where the inductively defined thing lives in
    [Prop]).  In the rest of this course, please follow one of the two
    for _all_ of your inductive proofs. *)

(** *** Induction Over an Inductively Defined Set *)
 
(** _Template_: 

       - _Theorem_: <Universally quantified proposition of the form
         "For all [n:S], [P(n)]," where [S] is some inductively defined
         set.>

         _Proof_: By induction on [n].

           <one case for each constructor [c] of [S]...>

           - Suppose [n = c a1 ... ak], where <...and here we state
             the IH for each of the [a]'s that has type [S], if any>.
             We must show <...and here we restate [P(c a1 ... ak)]>.

             <go on and prove [P(n)] to finish the case...>

           - <other cases similarly...>                        []
 
    _Example_:
 
      - _Theorem_: For all sets [X], lists [l : list X], and numbers
        [n], if [length l = n] then [index (S n) l = None].

        _Proof_: By induction on [l].

        - Suppose [l = []].  We must show, for all numbers [n],
          that, if length [[] = n], then [index (S n) [] =
          None].

          This follows immediately from the definition of index.

        - Suppose [l = x :: l'] for some [x] and [l'], where
          [length l' = n'] implies [index (S n') l' = None], for
          any number [n'].  We must show, for all [n], that, if
          [length (x::l') = n] then [index (S n) (x::l') =
          None].

          Let [n] be a number with [length l = n].  Since
            length l = length (x::l') = S (length l'),
          it suffices to show that 
            index (S (length l')) l' = None.
]]  
          But this follows directly from the induction hypothesis,
          picking [n'] to be length [l'].  [] *)
 
(** *** Induction Over an Inductively Defined Proposition *)

(** Since inductively defined proof objects are often called
    "derivation trees," this form of proof is also known as _induction
    on derivations_. 

    _Template_:
 
       - _Theorem_: <Proposition of the form "[Q -> P]," where [Q] is
         some inductively defined proposition (more generally,
         "For all [x] [y] [z], [Q x y z -> P x y z]")>

         _Proof_: By induction on a derivation of [Q].  <Or, more
         generally, "Suppose we are given [x], [y], and [z].  We
         show that [Q x y z] implies [P x y z], by induction on a
         derivation of [Q x y z]"...>

           <one case for each constructor [c] of [Q]...>

           - Suppose the final rule used to show [Q] is [c].  Then
             <...and here we state the types of all of the [a]'s
             together with any equalities that follow from the
             definition of the constructor and the IH for each of
             the [a]'s that has type [Q], if there are any>.  We must
             show <...and here we restate [P]>.

             <go on and prove [P] to finish the case...>

           - <other cases similarly...>                        []

    _Example_
 
       - _Theorem_: The [<=] relation is transitive -- i.e., for all
         numbers [n], [m], and [o], if [n <= m] and [m <= o], then
         [n <= o].

         _Proof_: By induction on a derivation of [m <= o].

           - Suppose the final rule used to show [m <= o] is
             [le_n]. Then [m = o] and we must show that [n <= m],
             which is immediate by hypothesis.

           - Suppose the final rule used to show [m <= o] is
             [le_S].  Then [o = S o'] for some [o'] with [m <= o'].
             We must show that [n <= S o'].
             By induction hypothesis, [n <= o'].

             But then, by [le_S], [n <= S o'].  [] *)



(* ##################################################### *)
(** * Induction Principles in [Prop] (Advanced) *)

(** The remainder of this chapter offers some additional details on
    how induction works in Coq, the process of building proof trees,
    and the "trusted computing base" that underlies Coq proofs.  It
    can safely be skimmed on a first reading.  (As with the other
    advanced sections, we recommend skimming rather than skipping over
    it outright: it answers some questions that occur to many Coq
    users at some point, so it is useful to have a rough idea of
    what's here.) *)



(** Earlier, we looked in detail at the induction principles that Coq
    generates for inductively defined _sets_.  The induction
    principles for inductively defined _propositions_ like [gorgeous]
    are a tiny bit more complicated.  As with all induction
    principles, we want to use the induction principle on [gorgeous]
    to prove things by inductively considering the possible shapes
    that something in [gorgeous] can have -- either it is evidence
    that [0] is gorgeous, or it is evidence that, for some [n], [3+n]
    is gorgeous, or it is evidence that, for some [n], [5+n] is
    gorgeous and it includes evidence that [n] itself is.  Intuitively
    speaking, however, what we want to prove are not statements about
    _evidence_ but statements about _numbers_.  So we want an
    induction principle that lets us prove properties of numbers by
    induction on evidence.

    For example, from what we've said so far, you might expect the
    inductive definition of [gorgeous]...
    Inductive gorgeous : nat -> Prop :=
         g_0 : gorgeous 0
       | g_plus3 : forall n, gorgeous n -> gorgeous (3+m)
       | g_plus5 : forall n, gorgeous n -> gorgeous (5+m).
    ...to give rise to an induction principle that looks like this...
    gorgeous_ind_max :
       forall P : (forall n : nat, gorgeous n -> Prop),
            P O g_0 ->
            (forall (m : nat) (e : gorgeous m), 
               P m e -> P (3+m) (g_plus3 m e) ->
            (forall (m : nat) (e : gorgeous m), 
               P m e -> P (5+m) (g_plus5 m e) ->
            forall (n : nat) (e : gorgeous n), P n e
    ... because:

     - Since [gorgeous] is indexed by a number [n] (every [gorgeous]
       object [e] is a piece of evidence that some particular number
       [n] is gorgeous), the proposition [P] is parameterized by both
       [n] and [e] -- that is, the induction principle can be used to
       prove assertions involving both a gorgeous number and the
       evidence that it is gorgeous.

     - Since there are three ways of giving evidence of gorgeousness
       ([gorgeous] has three constructors), applying the induction
       principle generates three subgoals:

         - We must prove that [P] holds for [O] and [b_0].

         - We must prove that, whenever [n] is a gorgeous
           number and [e] is an evidence of its gorgeousness,
           if [P] holds of [n] and [e],
           then it also holds of [3+m] and [g_plus3 n e].

         - We must prove that, whenever [n] is a gorgeous
           number and [e] is an evidence of its gorgeousness,
           if [P] holds of [n] and [e],
           then it also holds of [5+m] and [g_plus5 n e].

     - If these subgoals can be proved, then the induction principle
       tells us that [P] is true for _all_ gorgeous numbers [n] and
       evidence [e] of their gorgeousness.

    But this is a little more flexibility than we actually need or
    want: it is giving us a way to prove logical assertions where the
    assertion involves properties of some piece of _evidence_ of
    gorgeousness, while all we really care about is proving
    properties of _numbers_ that are gorgeous -- we are interested in
    assertions about numbers, not about evidence.  It would therefore
    be more convenient to have an induction principle for proving
    propositions [P] that are parameterized just by [n] and whose
    conclusion establishes [P] for all gorgeous numbers [n]:
       forall P : nat -> Prop,
          ... ->
             forall n : nat, gorgeous n -> P n
    For this reason, Coq actually generates the following simplified
    induction principle for [gorgeous]: *)



Check gorgeous_ind.
(* ===>  gorgeous_ind
     : forall P : nat -> Prop,
       P 0 ->
       (forall n : nat, gorgeous n -> P n -> P (3 + n)) ->
       (forall n : nat, gorgeous n -> P n -> P (5 + n)) ->
       forall n : nat, gorgeous n -> P n *)

(** In particular, Coq has dropped the evidence term [e] as a
    parameter of the the proposition [P], and consequently has
    rewritten the assumption [forall (n : nat) (e: gorgeous n), ...]
    to be [forall (n : nat), gorgeous n -> ...]; i.e., we no longer
    require explicit evidence of the provability of [gorgeous n]. *)

(** In English, [gorgeous_ind] says:

    - Suppose, [P] is a property of natural numbers (that is, [P n] is
      a [Prop] for every [n]).  To show that [P n] holds whenever [n]
      is gorgeous, it suffices to show:
  
      - [P] holds for [0],
  
      - for any [n], if [n] is gorgeous and [P] holds for
        [n], then [P] holds for [3+n],

      - for any [n], if [n] is gorgeous and [P] holds for
        [n], then [P] holds for [5+n]. *)

(** As expected, we can apply [gorgeous_ind] directly instead of using [induction]. *)

Theorem gorgeous__beautiful' : forall n, gorgeous n -> beautiful n.
Proof.
   intros.
   apply gorgeous_ind.
   Case "g_0".
       apply b_0.
   Case "g_plus3".
       intros.
       apply b_sum. apply b_3.
       apply H1.
   Case "g_plus5".
       intros.
       apply b_sum. apply b_5.
       apply H1.
   apply H.
Qed.



(** The precise form of an Inductive definition can affect the
    induction principle Coq generates.

For example, in [Logic], we have defined [<=] as: *)

(* Inductive le : nat -> nat -> Prop :=
     | le_n : forall n, le n n
     | le_S : forall n m, (le n m) -> (le n (S m)). *)

(** This definition can be streamlined a little by observing that the 
    left-hand argument [n] is the same everywhere in the definition, 
    so we can actually make it a "general parameter" to the whole 
    definition, rather than an argument to each constructor. *)

Inductive le (n:nat) : nat -> Prop :=
  | le_n : le n n
  | le_S : forall m, (le n m) -> (le n (S m)).

Notation "m <= n" := (le m n).

(** The second one is better, even though it looks less symmetric.
    Why?  Because it gives us a simpler induction principle. *)

Check le_ind.
(* ===>  forall (n : nat) (P : nat -> Prop),
           P n ->
           (forall m : nat, n <= m -> P m -> P (S m)) ->
           forall n0 : nat, n <= n0 -> P n0 *)

(** By contrast, the induction principle that Coq calculates for the
    first definition has a lot of extra quantifiers, which makes it
    messier to work with when proving things by induction.  Here is
    the induction principle for the first [le]: *)

(* le_ind : 
     forall P : nat -> nat -> Prop,
     (forall n : nat, P n n) ->
     (forall n m : nat, le n m -> P n m -> P n (S m)) ->
     forall n n0 : nat, le n n0 -> P n n0 *)


(* ##################################################### *)
(** * Additional Exercises *)

(** **** Exercise: 2 stars, optional (foo_ind_principle)  *)
(** Suppose we make the following inductive definition:
   Inductive foo (X : Set) (Y : Set) : Set :=
     | foo1 : X -> foo X Y
     | foo2 : Y -> foo X Y
     | foo3 : foo X Y -> foo X Y.
   Fill in the blanks to complete the induction principle that will be
   generated by Coq. 
   foo_ind
        : forall (X Y : Set) (P : foo X Y -> Prop),   
          (forall x : X, __________________________________) ->
          (forall y : Y, __________________________________) ->
          (________________________________________________) ->
           ________________________________________________

*)
(** [] *)

(** **** Exercise: 2 stars, optional (bar_ind_principle)  *)
(** Consider the following induction principle:
   bar_ind
        : forall P : bar -> Prop,
          (forall n : nat, P (bar1 n)) ->
          (forall b : bar, P b -> P (bar2 b)) ->
          (forall (b : bool) (b0 : bar), P b0 -> P (bar3 b b0)) ->
          forall b : bar, P b
   Write out the corresponding inductive set definition.
   Inductive bar : Set :=
     | bar1 : ________________________________________
     | bar2 : ________________________________________
     | bar3 : ________________________________________.

*)
(** [] *)

(** **** Exercise: 2 stars, optional (no_longer_than_ind)  *)
(** Given the following inductively defined proposition:
  Inductive no_longer_than (X : Set) : (list X) -> nat -> Prop :=
    | nlt_nil  : forall n, no_longer_than X [] n
    | nlt_cons : forall x l n, no_longer_than X l n -> 
                               no_longer_than X (x::l) (S n)
    | nlt_succ : forall l n, no_longer_than X l n -> 
                             no_longer_than X l (S n).
  write the induction principle generated by Coq.
  no_longer_than_ind
       : forall (X : Set) (P : list X -> nat -> Prop),
         (forall n : nat, ____________________) ->
         (forall (x : X) (l : list X) (n : nat),
          no_longer_than X l n -> ____________________ -> 
                                  _____________________________ ->
         (forall (l : list X) (n : nat),
          no_longer_than X l n -> ____________________ -> 
                                  _____________________________ ->
         forall (l : list X) (n : nat), no_longer_than X l n -> 
           ____________________

*)
(** [] *)


(* ##################################################### *)
(** ** Induction Principles for other Logical Propositions *)

(** Similarly, in [Logic] we have defined [eq] as: *)

(* Inductive eq (X:Type) : X -> X -> Prop :=
       refl_equal : forall x, eq X x x. *)

(** In the Coq standard library, the definition of equality is 
    slightly different: *)

Inductive eq' (X:Type) (x:X) : X -> Prop :=
    refl_equal' : eq' X x x.

(** The advantage of this definition is that the induction
    principle that Coq derives for it is precisely the familiar
    principle of _Leibniz equality_: what we mean when we say "[x] and
    [y] are equal" is that every property on [P] that is true of [x]
    is also true of [y].  (One philosophical quibble should be noted,
    though: Here, the "Leibniz equality principle" is a _consequence_
    of the way we've defined equality as an inductive type.  Leibniz
    viewed things exactly the other way around: for him, this
    principle itself _is the definition_ of equality.) *)

Check eq'_ind.
(* ===> 
     forall (X : Type) (x : X) (P : X -> Prop),
       P x -> forall y : X, x =' y -> P y 

   ===>  (i.e., after a little reorganization)
     forall (X : Type) (x : X) forall y : X, 
       x =' y -> 
       forall P : X -> Prop, P x -> P y *)



(** The induction principles for conjunction and disjunction are a
    good illustration of Coq's way of generating simplified induction
    principles for [Inductive]ly defined propositions, which we
    discussed above.  You try first: *)

(** **** Exercise: 1 star, optional (and_ind_principle)  *)
(** See if you can predict the induction principle for conjunction. *)

(* Check and_ind. *)
(** [] *)

(** **** Exercise: 1 star, optional (or_ind_principle)  *)
(** See if you can predict the induction principle for disjunction. *)

(* Check or_ind. *)
(** [] *)

Check and_ind.

(** From the inductive definition of the proposition [and P Q]
     Inductive and (P Q : Prop) : Prop :=
       conj : P -> Q -> (and P Q).
    we might expect Coq to generate this induction principle
     and_ind_max :
       forall (P Q : Prop) (P0 : P /\ Q -> Prop),
            (forall (a : P) (b : Q), P0 (conj P Q a b)) ->
            forall a : P /\ Q, P0 a
    but actually it generates this simpler and more useful one:
     and_ind :
       forall P Q P0 : Prop,
            (P -> Q -> P0) ->
            P /\ Q -> P0
    In the same way, when given the inductive definition of [or P Q]
     Inductive or (P Q : Prop) : Prop :=
       | or_introl : P -> or P Q
       | or_intror : Q -> or P Q.
    instead of the "maximal induction principle"
     or_ind_max :
       forall (P Q : Prop) (P0 : P \/ Q -> Prop),
            (forall a : P, P0 (or_introl P Q a)) ->
            (forall b : Q, P0 (or_intror P Q b)) ->
            forall o : P \/ Q, P0 o
    what Coq actually generates is this:
     or_ind :
       forall P Q P0 : Prop,
            (P -> P0) ->
            (Q -> P0) ->
            P \/ Q -> P0
]] 
*)

(** **** Exercise: 1 star, optional (False_ind_principle)  *)
(** Can you predict the induction principle for falsehood? *)

(* Check False_ind. *)
(** [] *)

(** Here's the induction principle that Coq generates for existentials: *)

Check ex_ind.
(* ===>  forall (X:Type) (P: X->Prop) (Q: Prop),
         (forall witness:X, P witness -> Q) -> 
          ex X P -> 
           Q *)

(** This induction principle can be understood as follows: If we have
         a function [f] that can construct evidence for [Q] given _any_
        witness of type [X] together with evidence that this witness has
        property [P], then from a proof of [ex X P] we can extract the
        witness and evidence that must have been supplied to the
        constructor, give these to [f], and thus obtain a proof of [Q]. *)



(* ######################################################### *)
(** ** Explicit Proof Objects for Induction *)


(** Although tactic-based proofs are normally much easier to
    work with, the ability to write a proof term directly is sometimes
    very handy, particularly when we want Coq to do something slightly
    non-standard.  *)
    
(** Recall the induction principle on naturals that Coq generates for
    us automatically from the Inductive declation for [nat]. *)

Check nat_ind.
(* ===> 
   nat_ind : forall P : nat -> Prop,
      P 0 -> 
      (forall n : nat, P n -> P (S n)) -> 
      forall n : nat, P n  *)

(** There's nothing magic about this induction lemma: it's just
   another Coq lemma that requires a proof.  Coq generates the proof
   automatically too...  *)

Print nat_ind.
Print nat_rect.
(* ===> (after some manual inlining and tidying)
   nat_ind =
    fun (P : nat -> Prop) 
        (f : P 0) 
        (f0 : forall n : nat, P n -> P (S n)) =>
          fix F (n : nat) : P n :=
             match n with
            | 0 => f
            | S n0 => f0 n0 (F n0)
            end.
*)

(** We can read this as follows: 
     Suppose we have evidence [f] that [P] holds on 0,  and 
     evidence [f0] that [forall n:nat, P n -> P (S n)].  
     Then we can prove that [P] holds of an arbitrary nat [n] via 
     a recursive function [F] (here defined using the expression 
     form [Fix] rather than by a top-level [Fixpoint] 
     declaration).  [F] pattern matches on [n]: 
      - If it finds 0, [F] uses [f] to show that [P n] holds.
      - If it finds [S n0], [F] applies itself recursively on [n0] 
         to obtain evidence that [P n0] holds; then it applies [f0] 
         on that evidence to show that [P (S n)] holds. 
    [F] is just an ordinary recursive function that happens to 
    operate on evidence in [Prop] rather than on terms in [Set].
 
*)

 
(**  We can adapt this approach to proving [nat_ind] to help prove
    _non-standard_ induction principles too.  Recall our desire to
    prove that

    [forall n : nat, even n -> ev n].
 
    Attempts to do this by standard induction on [n] fail, because the
    induction principle only lets us proceed when we can prove that
    [even n -> even (S n)] -- which is of course never provable.  What
    we did in [Logic] was a bit of a hack:
 
    [Theorem even__ev : forall n : nat,
     (even n -> ev n) /\ (even (S n) -> ev (S n))].
 
    We can make a much better proof by defining and proving a
    non-standard induction principle that goes "by twos":
 
 *)
 
 Definition nat_ind2 : 
    forall (P : nat -> Prop), 
    P 0 -> 
    P 1 -> 
    (forall n : nat, P n -> P (S(S n))) -> 
    forall n : nat , P n :=
       fun P => fun P0 => fun P1 => fun PSS => 
          fix f (n:nat) := match n with 
                             0 => P0 
                           | 1 => P1 
                           | S (S n') => PSS n' (f n') 
                          end.
 
 (** Once you get the hang of it, it is entirely straightforward to
     give an explicit proof term for induction principles like this.
     Proving this as a lemma using tactics is much less intuitive (try
     it!).

     The [induction ... using] tactic variant gives a convenient way to
     specify a non-standard induction principle like this. *)
 
Lemma even__ev' : forall n, even n -> ev n.
Proof. 
 intros.  
 induction n as [ | |n'] using nat_ind2. 
  Case "even 0". 
    apply ev_0.  
  Case "even 1". 
    inversion H.
  Case "even (S(S n'))". 
    apply ev_SS. 
    apply IHn'.  unfold even.  unfold even in H.  simpl in H. apply H. 
Qed. 

(* ######################################################### *)
(** ** The Coq Trusted Computing Base *)

(** One issue that arises with any automated proof assistant is "why
    trust it?": what if there is a bug in the implementation that
    renders all its reasoning suspect?

    While it is impossible to allay such concerns completely, the fact
    that Coq is based on the Curry-Howard correspondence gives it a
    strong foundation. Because propositions are just types and proofs
    are just terms, checking that an alleged proof of a proposition is
    valid just amounts to _type-checking_ the term.  Type checkers are
    relatively small and straightforward programs, so the "trusted
    computing base" for Coq -- the part of the code that we have to
    believe is operating correctly -- is small too.

    What must a typechecker do?  Its primary job is to make sure that
    in each function application the expected and actual argument
    types match, that the arms of a [match] expression are constructor
    patterns belonging to the inductive type being matched over and
    all arms of the [match] return the same type, and so on.

    There are a few additional wrinkles:

    - Since Coq types can themselves be expressions, the checker must
      normalize these (by using the computation rules) before
      comparing them.

    - The checker must make sure that [match] expressions are
      _exhaustive_.  That is, there must be an arm for every possible
      constructor.  To see why, consider the following alleged proof
      object:
      Definition or_bogus : forall P Q, P \/ Q -> P :=
        fun (P Q : Prop) (A : P \/ Q) =>
           match A with
           | or_introl H => H
           end. 
      All the types here match correctly, but the [match] only
      considers one of the possible constructors for [or].  Coq's
      exhaustiveness check will reject this definition.

    - The checker must make sure that each [fix] expression
      terminates.  It does this using a syntactic check to make sure
      that each recursive call is on a subexpression of the original
      argument.  To see why this is essential, consider this alleged
      proof:
          Definition nat_false : forall (n:nat), False :=
             fix f (n:nat) : False := f n. 
      Again, this is perfectly well-typed, but (fortunately) Coq will
      reject it. *)

(** Note that the soundness of Coq depends only on the correctness of
    this typechecking engine, not on the tactic machinery.  If there
    is a bug in a tactic implementation (and this certainly does
    happen!), that tactic might construct an invalid proof term.  But
    when you type [Qed], Coq checks the term for validity from
    scratch.  Only lemmas whose proofs pass the type-checker can be
    used in further proof developments.  *)

(** $Date: 2014-12-31 15:31:47 -0500 (Wed, 31 Dec 2014) $ *)


