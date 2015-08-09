(** * Stlc: The Simply Typed Lambda-Calculus *)

Require Export Types.

(* ###################################################################### *)
(** * The Simply Typed Lambda-Calculus *)

(** The simply typed lambda-calculus (STLC) is a tiny core calculus
    embodying the key concept of _functional abstraction_, which shows
    up in pretty much every real-world programming language in some
    form (functions, procedures, methods, etc.).
    
    We will follow exactly the same pattern as in the previous
    chapter when formalizing this calculus (syntax, small-step
    semantics, typing rules) and its main properties (progress and
    preservation).  The new technical challenges (which will take some
    work to deal with) all arise from the mechanisms of _variable
    binding_ and _substitution_. *)

(* ###################################################################### *)
(** ** Overview *)

(** The STLC is built on some collection of _base types_ -- booleans,
    numbers, strings, etc.  The exact choice of base types doesn't
    matter -- the construction of the language and its theoretical
    properties work out pretty much the same -- so for the sake of
    brevity let's take just [Bool] for the moment.  At the end of the
    chapter we'll see how to add more base types, and in later
    chapters we'll enrich the pure STLC with other useful constructs
    like pairs, records, subtyping, and mutable state.

    Starting from the booleans, we add three things:
        - variables
        - function abstractions
        - application

    This gives us the following collection of abstract syntax
    constructors (written out here in informal BNF notation -- we'll
    formalize it below).

*)

(** Informal concrete syntax: 
       t ::= x                       variable
           | \x:T1.t2                abstraction
           | t1 t2                   application
           | true                    constant true
           | false                   constant false
           | if t1 then t2 else t3   conditional
*)

(** The [\] symbol (backslash, in ascii) in a function abstraction
    [\x:T1.t2] is generally written as a greek letter "lambda" (hence
    the name of the calculus).  The variable [x] is called the
    _parameter_ to the function; the term [t2] is its _body_.  The
    annotation [:T] specifies the type of arguments that the function
    can be applied to. *)

(** Some examples:

      - [\x:Bool. x]

        The identity function for booleans.

      - [(\x:Bool. x) true]

        The identity function for booleans, applied to the boolean [true].

      - [\x:Bool. if x then false else true]

        The boolean "not" function.

      - [\x:Bool. true]

        The constant function that takes every (boolean) argument to
        [true]. *)
(**  
      - [\x:Bool. \y:Bool. x]

        A two-argument function that takes two booleans and returns
        the first one.  (Note that, as in Coq, a two-argument function
        is really a one-argument function whose body is also a
        one-argument function.)

      - [(\x:Bool. \y:Bool. x) false true]

        A two-argument function that takes two booleans and returns
        the first one, applied to the booleans [false] and [true].

        Note that, as in Coq, application associates to the left --
        i.e., this expression is parsed as [((\x:Bool. \y:Bool. x)
        false) true].

      - [\f:Bool->Bool. f (f true)]

        A higher-order function that takes a _function_ [f] (from
        booleans to booleans) as an argument, applies [f] to [true],
        and applies [f] again to the result.

      - [(\f:Bool->Bool. f (f true)) (\x:Bool. false)]

        The same higher-order function, applied to the constantly
        [false] function. *)

(** As the last several examples show, the STLC is a language of
    _higher-order_ functions: we can write down functions that take
    other functions as arguments and/or return other functions as
    results.  

    Another point to note is that the STLC doesn't provide any
    primitive syntax for defining _named_ functions -- all functions
    are "anonymous."  We'll see in chapter [MoreStlc] that it is easy
    to add named functions to what we've got -- indeed, the
    fundamental naming and binding mechanisms are exactly the same.  

    The _types_ of the STLC include [Bool], which classifies the
    boolean constants [true] and [false] as well as more complex
    computations that yield booleans, plus _arrow types_ that classify
    functions. *)
(**
      T ::= Bool
          | T1 -> T2
    For example:

      - [\x:Bool. false] has type [Bool->Bool]

      - [\x:Bool. x] has type [Bool->Bool]

      - [(\x:Bool. x) true] has type [Bool]

      - [\x:Bool. \y:Bool. x] has type [Bool->Bool->Bool] (i.e. [Bool -> (Bool->Bool)])

      - [(\x:Bool. \y:Bool. x) false] has type [Bool->Bool]

      - [(\x:Bool. \y:Bool. x) false true] has type [Bool]
*)





(* ###################################################################### *)
(** ** Syntax *)

Module STLC.

(* ################################### *)
(** *** Types *)

Inductive ty : Type := 
  | TBool  : ty 
  | TArrow : ty -> ty -> ty.

(* ################################### *)
(** *** Terms *)

Inductive tm : Type :=
  | tvar : id -> tm
  | tapp : tm -> tm -> tm
  | tabs : id -> ty -> tm -> tm
  | ttrue : tm
  | tfalse : tm
  | tif : tm -> tm -> tm -> tm.

Tactic Notation "t_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "tvar" | Case_aux c "tapp" 
  | Case_aux c "tabs" | Case_aux c "ttrue" 
  | Case_aux c "tfalse" | Case_aux c "tif" ].

(** Note that an abstraction [\x:T.t] (formally, [tabs x T t]) is
    always annotated with the type [T] of its parameter, in contrast
    to Coq (and other functional languages like ML, Haskell, etc.),
    which use _type inference_ to fill in missing annotations.  We're
    not considering type inference here, to keep things simple. *)

(** Some examples... *)

Definition x := (Id 0).
Definition y := (Id 1).
Definition z := (Id 2).
Hint Unfold x.
Hint Unfold y.
Hint Unfold z.

(** [idB = \x:Bool. x] *)

Notation idB := 
  (tabs x TBool (tvar x)).

(** [idBB = \x:Bool->Bool. x] *)

Notation idBB := 
  (tabs x (TArrow TBool TBool) (tvar x)).

(** [idBBBB = \x:(Bool->Bool) -> (Bool->Bool). x] *)

Notation idBBBB :=
  (tabs x (TArrow (TArrow TBool TBool) 
                      (TArrow TBool TBool)) 
    (tvar x)).

(** [k = \x:Bool. \y:Bool. x] *)

Notation k := (tabs x TBool (tabs y TBool (tvar x))).

(** [notB = \x:Bool. if x then false else true] *)

Notation notB := (tabs x TBool (tif (tvar x) tfalse ttrue)).


(** (We write these as [Notation]s rather than [Definition]s to make
    things easier for [auto].) *)

(* ###################################################################### *)
(** ** Operational Semantics *)

(** To define the small-step semantics of STLC terms, we begin -- as
    always -- by defining the set of values.  Next, we define the
    critical notions of _free variables_ and _substitution_, which are
    used in the reduction rule for application expressions.  And
    finally we give the small-step relation itself. *)

(* ################################### *)
(** *** Values *)

(** To define the values of the STLC, we have a few cases to consider.

    First, for the boolean part of the language, the situation is
    clear: [true] and [false] are the only values.  An [if]
    expression is never a value. *)

(** Second, an application is clearly not a value: It represents a
    function being invoked on some argument, which clearly still has
    work left to do. *)

(** Third, for abstractions, we have a choice:

      - We can say that [\x:T.t1] is a value only when [t1] is a
        value -- i.e., only if the function's body has been
        reduced (as much as it can be without knowing what argument it
        is going to be applied to).

      - Or we can say that [\x:T.t1] is always a value, no matter
        whether [t1] is one or not -- in other words, we can say that
        reduction stops at abstractions.

    Coq, in its built-in functional programming langauge, makes the
    first choice -- for example,
         Eval simpl in (fun x:bool => 3 + 4)
    yields [fun x:bool => 7].  

    Most real-world functional programming languages make the second
    choice -- reduction of a function's body only begins when the
    function is actually applied to an argument.  We also make the
    second choice here. *)

Inductive value : tm -> Prop :=
  | v_abs : forall x T t,
      value (tabs x T t)
  | v_true : 
      value ttrue
  | v_false : 
      value tfalse.

Hint Constructors value.


(** Finally, we must consider what constitutes a _complete_ program.

  Intuitively, a "complete" program must not refer to any undefined
  variables.  We'll see shortly how to define the "free" variables 
  in a STLC term.  A program is "closed", that is, it contains no
  free variables.
   
*)

(** Having made the choice not to reduce under abstractions,
    we don't need to worry about whether variables are values, since
    we'll always be reducing programs "from the outside in," and that
    means the [step] relation will always be working with closed
    terms (ones with no free variables).  *)



(* ###################################################################### *)
(** *** Substitution *)

(** Now we come to the heart of the STLC: the operation of
    substituting one term for a variable in another term.

    This operation will be used below to define the operational
    semantics of function application, where we will need to
    substitute the argument term for the function parameter in the
    function's body.  For example, we reduce
       (\x:Bool. if x then true else x) false
    to 
       if false then true else false
]] 
    by substituting [false] for the parameter [x] in the body of the
    function.  

    In general, we need to be able to substitute some given
    term [s] for occurrences of some variable [x] in another term [t].
    In informal discussions, this is usually written [ [x:=s]t ] and
    pronounced "substitute [x] with [s] in [t]." *)

(** Here are some examples:

      - [[x:=true] (if x then x else false)] yields [if true then true else false]

      - [[x:=true] x] yields [true]

      - [[x:=true] (if x then x else y)] yields [if true then true else y]

      - [[x:=true] y] yields [y]

      - [[x:=true] false] yields [false] (vacuous substitution)

      - [[x:=true] (\y:Bool. if y then x else false)] yields [\y:Bool. if y then true else false]
      - [[x:=true] (\y:Bool. x)] yields [\y:Bool. true]

      - [[x:=true] (\y:Bool. y)] yields [\y:Bool. y]

      - [[x:=true] (\x:Bool. x)] yields [\x:Bool. x]

    The last example is very important: substituting [x] with [true] in
    [\x:Bool. x] does _not_ yield [\x:Bool. true]!  The reason for
    this is that the [x] in the body of [\x:Bool. x] is _bound_ by the
    abstraction: it is a new, local name that just happens to be
    spelled the same as some global name [x]. *)

(** Here is the definition, informally...
   [x:=s]x = s
   [x:=s]y = y                                   if x <> y
   [x:=s](\x:T11.t12)   = \x:T11. t12      
   [x:=s](\y:T11.t12)   = \y:T11. [x:=s]t12      if x <> y
   [x:=s](t1 t2)        = ([x:=s]t1) ([x:=s]t2)       
   [x:=s]true           = true
   [x:=s]false          = false
   [x:=s](if t1 then t2 else t3) = 
                   if [x:=s]t1 then [x:=s]t2 else [x:=s]t3
]]  
*)

(**    ... and formally: *)

Reserved Notation "'[' x ':=' s ']' t" (at level 20).

Fixpoint subst (x:id) (s:tm) (t:tm) : tm :=
  match t with
  | tvar x' => 
      if eq_id_dec x x' then s else t
  | tabs x' T t1 => 
      tabs x' T (if eq_id_dec x x' then t1 else ([x:=s] t1)) 
  | tapp t1 t2 => 
      tapp ([x:=s] t1) ([x:=s] t2)
  | ttrue => 
      ttrue
  | tfalse => 
      tfalse
  | tif t1 t2 t3 => 
      tif ([x:=s] t1) ([x:=s] t2) ([x:=s] t3)
  end

where "'[' x ':=' s ']' t" := (subst x s t).

(** _Technical note_: Substitution becomes trickier to define if we
    consider the case where [s], the term being substituted for a
    variable in some other term, may itself contain free variables.
    Since we are only interested here in defining the [step] relation
    on closed terms (i.e., terms like [\x:Bool. x], that do not mention
    variables are not bound by some enclosing lambda), we can skip
    this extra complexity here, but it must be dealt with when
    formalizing richer languages. *)

(** *** *)
(** **** Exercise: 3 stars (substi)  *)  

(** The definition that we gave above uses Coq's [Fixpoint] facility
    to define substitution as a _function_.  Suppose, instead, we
    wanted to define substitution as an inductive _relation_ [substi].
    We've begun the definition by providing the [Inductive] header and
    one of the constructors; your job is to fill in the rest of the
    constructors. *)

Inductive substi (s:tm) (x:id) : tm -> tm -> Prop := 
  | s_var1 : 
      substi s x (tvar x) s
  (* FILL IN HERE *)
.

Hint Constructors substi.

Theorem substi_correct : forall s x t t',
  [x:=s]t = t' <-> substi s x t t'.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ################################### *)
(** *** Reduction *)

(** The small-step reduction relation for STLC now follows the same
    pattern as the ones we have seen before.  Intuitively, to reduce a
    function application, we first reduce its left-hand side until it
    becomes a literal function; then we reduce its right-hand
    side (the argument) until it is also a value; and finally we
    substitute the argument for the bound variable in the body of the
    function.  This last rule, written informally as
      (\x:T.t12) v2 ==> [x:=v2]t12
    is traditionally called "beta-reduction". *)

(** 
                               value v2
                     ----------------------------                   (ST_AppAbs)
                     (\x:T.t12) v2 ==> [x:=v2]t12

                              t1 ==> t1'
                           ----------------                           (ST_App1)
                           t1 t2 ==> t1' t2

                              value v1
                              t2 ==> t2'
                           ----------------                           (ST_App2)
                           v1 t2 ==> v1 t2'
*)
(** ... plus the usual rules for booleans:
                    --------------------------------                (ST_IfTrue)
                    (if true then t1 else t2) ==> t1

                    ---------------------------------              (ST_IfFalse)
                    (if false then t1 else t2) ==> t2

                              t1 ==> t1'
         ----------------------------------------------------           (ST_If)
         (if t1 then t2 else t3) ==> (if t1' then t2 else t3)
*)

Reserved Notation "t1 '==>' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T t12 v2,
         value v2 ->
         (tapp (tabs x T t12) v2) ==> [x:=v2]t12
  | ST_App1 : forall t1 t1' t2,
         t1 ==> t1' ->
         tapp t1 t2 ==> tapp t1' t2
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 ==> t2' -> 
         tapp v1 t2 ==> tapp v1  t2'
  | ST_IfTrue : forall t1 t2,
      (tif ttrue t1 t2) ==> t1
  | ST_IfFalse : forall t1 t2,
      (tif tfalse t1 t2) ==> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 ==> t1' ->
      (tif t1 t2 t3) ==> (tif t1' t2 t3)

where "t1 '==>' t2" := (step t1 t2).

Tactic Notation "step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ST_AppAbs" | Case_aux c "ST_App1" 
  | Case_aux c "ST_App2" | Case_aux c "ST_IfTrue" 
  | Case_aux c "ST_IfFalse" | Case_aux c "ST_If" ].

Hint Constructors step.

Notation multistep := (multi step).
Notation "t1 '==>*' t2" := (multistep t1 t2) (at level 40).

(* ##################################### *)





(* ##################################### *)
(** *** Examples *)

(** Example:
    ((\x:Bool->Bool. x) (\x:Bool. x)) ==>* (\x:Bool. x)
i.e.
    (idBB idB) ==>* idB
*)

Lemma step_example1 :
  (tapp idBB idB) ==>* idB.
Proof.
  eapply multi_step.
    apply ST_AppAbs.
    apply v_abs.
  simpl.
  apply multi_refl.  Qed.  

(** Example:
((\x:Bool->Bool. x) ((\x:Bool->Bool. x) (\x:Bool. x))) 
      ==>* (\x:Bool. x)
i.e.
  (idBB (idBB idB)) ==>* idB.
*)

Lemma step_example2 :
  (tapp idBB (tapp idBB idB)) ==>* idB.
Proof.
  eapply multi_step.
    apply ST_App2. auto.
    apply ST_AppAbs. auto.
  eapply multi_step.
    apply ST_AppAbs. simpl. auto.
  simpl. apply multi_refl.  Qed. 

(** Example:
((\x:Bool->Bool. x) (\x:Bool. if x then false
                              else true)) true)
      ==>* false
i.e.
  ((idBB notB) ttrue) ==>* tfalse.
*)

Lemma step_example3 :
  tapp (tapp idBB notB) ttrue ==>* tfalse.
Proof. 
  eapply multi_step.
    apply ST_App1. apply ST_AppAbs. auto. simpl.
  eapply multi_step.
    apply ST_AppAbs. auto. simpl.
  eapply multi_step.
    apply ST_IfTrue. apply multi_refl.  Qed. 

(** Example:
((\x:Bool -> Bool. x) ((\x:Bool. if x then false
                               else true) true))
      ==>* false
i.e.
  (idBB (notB ttrue)) ==>* tfalse.
*)

Lemma step_example4 :
  tapp idBB (tapp notB ttrue) ==>* tfalse.
Proof. 
  eapply multi_step.
    apply ST_App2. auto. 
    apply ST_AppAbs. auto. simpl.
  eapply multi_step.
    apply ST_App2. auto. 
    apply ST_IfTrue. 
  eapply multi_step.
    apply ST_AppAbs. auto. simpl.
  apply multi_refl.  Qed. 


(** A more automatic proof *)

Lemma step_example1' :
  (tapp idBB idB) ==>* idB.
Proof. normalize.  Qed.  

(** Again, we can use the [normalize] tactic from above to simplify
    the proof. *)

Lemma step_example2' :
  (tapp idBB (tapp idBB idB)) ==>* idB.
Proof.
  normalize.
Qed. 

Lemma step_example3' :
  tapp (tapp idBB notB) ttrue ==>* tfalse.
Proof. normalize.  Qed.  

Lemma step_example4' :
  tapp idBB (tapp notB ttrue) ==>* tfalse.
Proof. normalize.  Qed.  

(** **** Exercise: 2 stars (step_example3)  *)  
(** Try to do this one both with and without [normalize]. *)

Lemma step_example5 :
       (tapp (tapp idBBBB idBB) idB)
  ==>* idB.
Proof.
  (* FILL IN HERE *) Admitted.

(* FILL IN HERE *)
(** [] *)

(* ###################################################################### *)
(** ** Typing *)

(* ################################### *)
(** *** Contexts *)

(** _Question_: What is the type of the term "[x y]"?

    _Answer_: It depends on the types of [x] and [y]!  

    I.e., in order to assign a type to a term, we need to know
    what assumptions we should make about the types of its free
    variables.

    This leads us to a three-place "typing judgment", informally
    written [Gamma |- t \in T], where [Gamma] is a
    "typing context" -- a mapping from variables to their types. *)

(** We hide the definition of partial maps in a module since it is
    actually defined in [SfLib]. *)

Module PartialMap.

Definition partial_map (A:Type) := id -> option A.

Definition empty {A:Type} : partial_map A := (fun _ => None). 

(** Informally, we'll write [Gamma, x:T] for "extend the partial
    function [Gamma] to also map [x] to [T]."  Formally, we use the
    function [extend] to add a binding to a partial map. *)

Definition extend {A:Type} (Gamma : partial_map A) (x:id) (T : A) :=
  fun x' => if eq_id_dec x x' then Some T else Gamma x'.

Lemma extend_eq : forall A (ctxt: partial_map A) x T,
  (extend ctxt x T) x = Some T.
Proof.
  intros. unfold extend. rewrite eq_id. auto.
Qed.

Lemma extend_neq : forall A (ctxt: partial_map A) x1 T x2,
  x2 <> x1 ->                       
  (extend ctxt x2 T) x1 = ctxt x1.
Proof.
  intros. unfold extend. rewrite neq_id; auto.
Qed.

End PartialMap.

Definition context := partial_map ty.

(* ################################### *)
(** *** Typing Relation *)

(** 
                             Gamma x = T
                            --------------                              (T_Var)
                            Gamma |- x \in T

                      Gamma , x:T11 |- t12 \in T12
                     ----------------------------                       (T_Abs)
                     Gamma |- \x:T11.t12 \in T11->T12

                        Gamma |- t1 \in T11->T12
                          Gamma |- t2 \in T11
                        ----------------------                          (T_App)
                         Gamma |- t1 t2 \in T12

                         --------------------                          (T_True)
                         Gamma |- true \in Bool

                        ---------------------                         (T_False)
                        Gamma |- false \in Bool

       Gamma |- t1 \in Bool    Gamma |- t2 \in T    Gamma |- t3 \in T
       --------------------------------------------------------          (T_If)
                  Gamma |- if t1 then t2 else t3 \in T


    We can read the three-place relation [Gamma |- t \in T] as: 
    "to the term [t] we can assign the type [T] using as types for
    the free variables of [t] the ones specified in the context 
    [Gamma]." *)

Reserved Notation "Gamma '|-' t '\in' T" (at level 40).
    
Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T,
      Gamma x = Some T ->
      Gamma |- tvar x \in T
  | T_Abs : forall Gamma x T11 T12 t12,
      extend Gamma x T11 |- t12 \in T12 -> 
      Gamma |- tabs x T11 t12 \in TArrow T11 T12
  | T_App : forall T11 T12 Gamma t1 t2,
      Gamma |- t1 \in TArrow T11 T12 -> 
      Gamma |- t2 \in T11 -> 
      Gamma |- tapp t1 t2 \in T12
  | T_True : forall Gamma,
       Gamma |- ttrue \in TBool
  | T_False : forall Gamma,
       Gamma |- tfalse \in TBool
  | T_If : forall t1 t2 t3 T Gamma,
       Gamma |- t1 \in TBool ->
       Gamma |- t2 \in T ->
       Gamma |- t3 \in T ->
       Gamma |- tif t1 t2 t3 \in T

where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Tactic Notation "has_type_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "T_Var" | Case_aux c "T_Abs" 
  | Case_aux c "T_App" | Case_aux c "T_True" 
  | Case_aux c "T_False" | Case_aux c "T_If" ].

Hint Constructors has_type.

(* ################################### *)
(** *** Examples *)

Example typing_example_1 :
  empty |- tabs x TBool (tvar x) \in TArrow TBool TBool.
Proof.
  apply T_Abs. apply T_Var. reflexivity.  Qed.

(** Note that since we added the [has_type] constructors to the hints
    database, auto can actually solve this one immediately. *)

Example typing_example_1' :
  empty |- tabs x TBool (tvar x) \in TArrow TBool TBool.
Proof. auto.  Qed.

(** Another example:
     empty |- \x:A. \y:A->A. y (y x)) 
           \in A -> (A->A) -> A.
*)

Example typing_example_2 :
  empty |-
    (tabs x TBool
       (tabs y (TArrow TBool TBool)
          (tapp (tvar y) (tapp (tvar y) (tvar x))))) \in
    (TArrow TBool (TArrow (TArrow TBool TBool) TBool)).
Proof with auto using extend_eq.
  apply T_Abs.
  apply T_Abs.
  eapply T_App. apply T_Var...
  eapply T_App. apply T_Var...
  apply T_Var...
Qed.

(** **** Exercise: 2 stars, optional (typing_example_2_full)  *)
(** Prove the same result without using [auto], [eauto], or
    [eapply]. *)

Example typing_example_2_full :
  empty |-
    (tabs x TBool
       (tabs y (TArrow TBool TBool)
          (tapp (tvar y) (tapp (tvar y) (tvar x))))) \in
    (TArrow TBool (TArrow (TArrow TBool TBool) TBool)).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars (typing_example_3)  *)
(** Formally prove the following typing derivation holds: *)
(** 
   empty |- \x:Bool->B. \y:Bool->Bool. \z:Bool.
               y (x z) 
         \in T.
*)

Example typing_example_3 :
  exists T, 
    empty |-
      (tabs x (TArrow TBool TBool)
         (tabs y (TArrow TBool TBool)
            (tabs z TBool
               (tapp (tvar y) (tapp (tvar x) (tvar z)))))) \in
      T.
Proof with auto.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** We can also show that terms are _not_ typable.  For example, let's
    formally check that there is no typing derivation assigning a type
    to the term [\x:Bool. \y:Bool, x y] -- i.e.,
    ~ exists T,
        empty |- \x:Bool. \y:Bool, x y : T.
*)

Example typing_nonexample_1 :
  ~ exists T,
      empty |- 
        (tabs x TBool
            (tabs y TBool
               (tapp (tvar x) (tvar y)))) \in
        T.
Proof.
  intros Hc. inversion Hc.
  (* The [clear] tactic is useful here for tidying away bits of
     the context that we're not going to need again. *)
  inversion H. subst. clear H.
  inversion H5. subst. clear H5.
  inversion H4. subst. clear H4.
  inversion H2. subst. clear H2.
  inversion H5. subst. clear H5.
  (* rewrite extend_neq in H1. rewrite extend_eq in H1. *)
  inversion H1.  Qed.

(** **** Exercise: 3 stars, optional (typing_nonexample_3)  *)
(** Another nonexample:
    ~ (exists S, exists T,
          empty |- \x:S. x x : T).
*)

Example typing_nonexample_3 :
  ~ (exists S, exists T,
        empty |- 
          (tabs x S
             (tapp (tvar x) (tvar x))) \in
          T).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)



End STLC.

(** $Date: 2014-12-31 11:17:56 -0500 (Wed, 31 Dec 2014) $ *)

