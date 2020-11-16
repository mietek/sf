(** * MoreStlc: More on the Simply Typed Lambda-Calculus *)

Set Warnings "-notation-overridden,-parsing".
From PLF Require Import Maps.
From PLF Require Import Types.
From PLF Require Import Smallstep.
From PLF Require Import Stlc.

(* ################################################################# *)
(** * Simple Extensions to STLC *)

(** The simply typed lambda-calculus has enough structure to make its
    theoretical properties interesting, but it is not much of a
    programming language!

    In this chapter, we begin to close the gap with real-world
    languages by introducing a number of familiar features that have
    straightforward treatments at the level of typing. *)

(* ================================================================= *)
(** ** Numbers *)

(** As we saw in exercise [stlc_arith] at the end of the [StlcProp]
    chapter, adding types, constants, and primitive operations for
    natural numbers is easy -- basically just a matter of combining
    the [Types] and [Stlc] chapters.  Adding more realistic
    numeric types like machine integers and floats is also
    straightforward, though of course the specifications of the
    numeric primitives become more fiddly. *)

(* ================================================================= *)
(** ** Let Bindings *)

(** When writing a complex expression, it is useful to be able
    to give names to some of its subexpressions to avoid repetition
    and increase readability.  Most languages provide one or more ways
    of doing this.  In OCaml (and Coq), for example, we can write [let
    x=t1 in t2] to mean "reduce the expression [t1] to a value and
    bind the name [x] to this value while reducing [t2]."

    Our [let]-binder follows OCaml in choosing a standard
    _call-by-value_ evaluation order, where the [let]-bound term must
    be fully reduced before reduction of the [let]-body can begin.
    The typing rule [T_Let] tells us that the type of a [let] can be
    calculated by calculating the type of the [let]-bound term,
    extending the context with a binding with this type, and in this
    enriched context calculating the type of the body (which is then
    the type of the whole [let] expression).

    At this point in the book, it's probably easier simply to look at
    the rules defining this new feature than to wade through a lot of
    English text conveying the same information.  Here they are: *)

(** Syntax:

       t ::=                Terms
           | ...               (other terms same as before)
           | let x=t in t      let-binding
*)

(**
    Reduction:

                                 t1 --> t1'
                     ----------------------------------               (ST_Let1)
                     let x=t1 in t2 --> let x=t1' in t2

                        ----------------------------              (ST_LetValue)
                        let x=v1 in t2 --> [x:=v1]t2

    Typing:

             Gamma |- t1 \in T1      x|->T1; Gamma |- t2 \in T2
             --------------------------------------------------        (T_Let)
                        Gamma |- let x=t1 in t2 \in T2
*)

(* ================================================================= *)
(** ** Pairs *)

(** Our functional programming examples in Coq have made
    frequent use of _pairs_ of values.  The type of such a pair is
    called a _product type_.

    The formalization of pairs is almost too simple to be worth
    discussing.  However, let's look briefly at the various parts of
    the definition to emphasize the common pattern. *)

(** In Coq, the primitive way of extracting the components of a pair
    is _pattern matching_.  An alternative is to take [fst] and
    [snd] -- the first- and second-projection operators -- as
    primitives.  Just for fun, let's do our pairs this way.  For
    example, here's how we'd write a function that takes a pair of
    numbers and returns the pair of their sum and difference:

       \x : Nat*Nat,
          let sum = x.fst + x.snd in
          let diff = x.fst - x.snd in
          (sum,diff)
*)

(** Adding pairs to the simply typed lambda-calculus, then, involves
    adding two new forms of term -- pairing, written [(t1,t2)], and
    projection, written [t.fst] for the first projection from [t] and
    [t.snd] for the second projection -- plus one new type constructor,
    [T1*T2], called the _product_ of [T1] and [T2].  *)

(** Syntax:

       t ::=                Terms
           | ...
           | (t,t)             pair
           | t.fst             first projection
           | t.snd             second projection

       v ::=                Values
           | ...
           | (v,v)             pair value

       T ::=                Types
           | ...
           | T * T             product type
*)

(** For reduction, we need several new rules specifying how pairs and
    projection behave.

                              t1 --> t1'
                         --------------------                        (ST_Pair1)
                         (t1,t2) --> (t1',t2)

                              t2 --> t2'
                         --------------------                        (ST_Pair2)
                         (v1,t2) --> (v1,t2')

                               t1 --> t1'
                           ------------------                        (ST_Fst1)
                           t1.fst --> t1'.fst

                          ------------------                       (ST_FstPair)
                          (v1,v2).fst --> v1

                               t1 --> t1'
                           ------------------                        (ST_Snd1)
                           t1.snd --> t1'.snd

                          ------------------                       (ST_SndPair)
                          (v1,v2).snd --> v2
*)

(** Rules [ST_FstPair] and [ST_SndPair] say that, when a fully
    reduced pair meets a first or second projection, the result is
    the appropriate component.  The congruence rules [ST_Fst1] and
    [ST_Snd1] allow reduction to proceed under projections, when the
    term being projected from has not yet been fully reduced.
    [ST_Pair1] and [ST_Pair2] reduce the parts of pairs: first the
    left part, and then -- when a value appears on the left -- the right
    part.  The ordering arising from the use of the metavariables [v]
    and [t] in these rules enforces a left-to-right evaluation
    strategy for pairs.  (Note the implicit convention that
    metavariables like [v] and [v1] can only denote values.)  We've
    also added a clause to the definition of values, above, specifying
    that [(v1,v2)] is a value.  The fact that the components of a pair
    value must themselves be values ensures that a pair passed as an
    argument to a function will be fully reduced before the function
    body starts executing. *)

(** The typing rules for pairs and projections are straightforward.

               Gamma |- t1 \in T1     Gamma |- t2 \in T2
               -----------------------------------------               (T_Pair)
                       Gamma |- (t1,t2) \in T1*T2

                        Gamma |- t0 \in T1*T2
                        ----------------------                         (T_Fst)
                        Gamma |- t0.fst \in T1

                        Gamma |- t0 \in T1*T2
                        ----------------------                         (T_Snd)
                        Gamma |- t0.snd \in T2
*)

(** [T_Pair] says that [(t1,t2)] has type [T1*T2] if [t1] has
    type [T1] and [t2] has type [T2].  Conversely, [T_Fst] and [T_Snd]
    tell us that, if [t0] has a product type [T1*T2] (i.e., if it
    will reduce to a pair), then the types of the projections from
    this pair are [T1] and [T2]. *)

(* ================================================================= *)
(** ** Unit *)

(** Another handy base type, found especially in functional languages,
    is the singleton type [Unit].

    It has a single element -- the term constant [unit] (with a small
    [u]) -- and a typing rule making [unit] an element of [Unit].  We
    also add [unit] to the set of possible values -- indeed, [unit] is
    the _only_ possible result of reducing an expression of type
    [Unit]. *)

(** Syntax:

       t ::=                Terms
           | ...               (other terms same as before)
           | unit              unit

       v ::=                Values
           | ...
           | unit              unit value

       T ::=                Types
           | ...
           | Unit              unit type

    Typing:

                         ----------------------                        (T_Unit)
                         Gamma |- unit \in Unit
*)

(** It may seem a little strange to bother defining a type that
    has just one element -- after all, wouldn't every computation
    living in such a type be trivial?

    This is a fair question, and indeed in the STLC the [Unit] type is
    not especially critical (though we'll see two uses for it below).
    Where [Unit] really comes in handy is in richer languages with
    _side effects_ -- e.g., assignment statements that mutate
    variables or pointers, exceptions and other sorts of nonlocal
    control structures, etc.  In such languages, it is convenient to
    have a type for the (trivial) result of an expression that is
    evaluated only for its effect. *)

(* ================================================================= *)
(** ** Sums *)

(** Many programs need to deal with values that can take two distinct
   forms.  For example, we might identify students in a university
   database using _either_ their name _or_ their id number. A search
   function might return _either_ a matching value _or_ an error code.

   These are specific examples of a binary _sum type_ (sometimes called
   a _disjoint union_), which describes a set of values drawn from
   one of two given types, e.g.:

       Nat + Bool
*)
(** We create elements of these types by _tagging_ elements of
    the component types.  For example, if [n] is a [Nat] then [inl n]
    is an element of [Nat+Bool]; similarly, if [b] is a [Bool] then
    [inr b] is a [Nat+Bool].  The names of the tags [inl] and [inr]
    arise from thinking of them as functions

       inl \in Nat  -> Nat + Bool
       inr \in Bool -> Nat + Bool

    that "inject" elements of [Nat] or [Bool] into the left and right
    components of the sum type [Nat+Bool].  (But note that we don't
    actually treat them as functions in the way we formalize them:
    [inl] and [inr] are keywords, and [inl t] and [inr t] are primitive
    syntactic forms, not function applications.) *)

(** In general, the elements of a type [T1 + T2] consist of the
    elements of [T1] tagged with the token [inl], plus the elements of
    [T2] tagged with [inr]. *)

(** As we've seen in Coq programming, one important use of sums is
    signaling errors:

      div \in Nat -> Nat -> (Nat + Unit)
      div =
        \x:Nat, \y:Nat,
          test iszero y then
            inr unit
          else
            inl ...
*)
(** The type [Nat + Unit] above is in fact isomorphic to [option
    nat] in Coq -- i.e., it's easy to write functions that translate
    back and forth. *)

(** To _use_ elements of sum types, we introduce a [case]
    construct (a very simplified form of Coq's [match]) to destruct
    them. For example, the following procedure converts a [Nat+Bool]
    into a [Nat]:

    getNat \in Nat+Bool -> Nat
    getNat =
      \x:Nat+Bool,
        case x of
          inl n => n
        | inr b => test b then 1 else 0
*)
(** More formally... *)

(** Syntax:

       t ::=                Terms
           | ...               (other terms same as before)
           | inl T t           tagging (left)
           | inr T t           tagging (right)
           | case t of         case
               inl x => t
             | inr x => t

       v ::=                Values
           | ...
           | inl T v           tagged value (left)
           | inr T v           tagged value (right)

       T ::=                Types
           | ...
           | T + T             sum type
*)

(** Reduction:

                               t1 --> t1'
                        ------------------------                       (ST_Inl)
                        inl T2 t1 --> inl T2 t1'

                               t2 --> t2'
                        ------------------------                       (ST_Inr)
                        inr T1 t2 --> inr T1 t2'

                               t0 --> t0'
               -------------------------------------------            (ST_Case)
                case t0 of inl x1 => t1 | inr x2 => t2 -->
               case t0' of inl x1 => t1 | inr x2 => t2

            -----------------------------------------------        (ST_CaseInl)
            case (inl T2 v1) of inl x1 => t1 | inr x2 => t2
                           -->  [x1:=v1]t1

            -----------------------------------------------        (ST_CaseInr)
            case (inr T1 v2) of inl x1 => t1 | inr x2 => t2
                           -->  [x2:=v2]t2
*)

(** Typing:

                          Gamma |- t1 \in T1
                   ------------------------------                       (T_Inl)
                   Gamma |- inl T2 t1 \in T1 + T2

                          Gamma |- t2 \in T2
                   -------------------------------                      (T_Inr)
                    Gamma |- inr T1 t2 \in T1 + T2

                        Gamma |- t0 \in T1+T2
                     x1|->T1; Gamma |- t1 \in T3
                     x2|->T2; Gamma |- t2 \in T3
         ------------------------------------------------------         (T_Case)
         Gamma |- case t0 of inl x1 => t1 | inr x2 => t2 \in T3

    We use the type annotations on [inl] and [inr] to make the typing
    relation deterministic (each term has at most one type), as we
    did for functions. *)

(** Without this extra information, the typing rule [T_Inl], for
    example, would have to say that, once we have shown that [t1] is
    an element of type [T1], we can derive that [inl t1] is an element
    of [T1 + T2] for _any_ type [T2].  For example, we could derive both
    [inl 5 : Nat + Nat] and [inl 5 : Nat + Bool] (and infinitely many
    other types).  This peculiarity (technically, a failure of
    uniqueness of types) would mean that we cannot build a
    typechecking algorithm simply by "reading the rules from bottom to
    top" as we could for all the other features seen so far.

    There are various ways to deal with this difficulty.  One simple
    one -- which we've adopted here -- forces the programmer to
    explicitly annotate the "other side" of a sum type when performing
    an injection.  This is a bit heavy for programmers (so real
    languages adopt other solutions), but it is easy to understand and
    formalize. *)

(* ================================================================= *)
(** ** Lists *)

(** The typing features we have seen can be classified into
    _base types_ like [Bool], and _type constructors_ like [->] and
    [*] that build new types from old ones.  Another useful type
    constructor is [List].  For every type [T], the type [List T]
    describes finite-length lists whose elements are drawn from [T].

    In principle, we could encode lists using pairs, sums and
    _recursive_ types. But giving semantics to recursive types is
    non-trivial. Instead, we'll just discuss the special case of lists
    directly.

    Below we give the syntax, semantics, and typing rules for lists.
    Except for the fact that explicit type annotations are mandatory
    on [nil] and cannot appear on [cons], these lists are essentially
    identical to those we built in Coq.  We use [case], rather than
    [head] and [tail] operators, to destruct lists, to avoid dealing
    with questions like "what is the [head] of the empty list?" *)

(** For example, here is a function that calculates the sum of
    the first two elements of a list of numbers:

      \x:List Nat,
      case x of nil   => 0
               | a::x' => case x' of nil    => a
                                    | b::x'' => a+b
*)
(**
    Syntax:

       t ::=                Terms
           | ...
           | nil T
           | cons t t
           | case t of nil   => t
                      | x::x => t

       v ::=                Values
           | ...
           | nil T             nil value
           | cons v v          cons value

       T ::=                Types
           | ...
           | List T            list of Ts
*)

(** Reduction:

                                t1 --> t1'
                       --------------------------                    (ST_Cons1)
                       cons t1 t2 --> cons t1' t2

                                t2 --> t2'
                       --------------------------                    (ST_Cons2)
                       cons v1 t2 --> cons v1 t2'

                              t1 --> t1'
                -------------------------------------------         (ST_Lcase1)
                 (case t1 of nil => t2 | xh::xt => t3) -->
                (case t1' of nil => t2 | xh::xt => t3)

               ------------------------------------------          (ST_LcaseNil)
               (case nil T1 of nil => t2 | xh::xt => t3)
                                --> t2

            ------------------------------------------------     (ST_LcaseCons)
            (case (cons vh vt) of nil => t2 | xh::xt => t3)
                          --> [xh:=vh,xt:=vt]t3
*)

(** Typing:

                        ---------------------------                     (T_Nil)
                        Gamma |- nil T1 \in List T1

             Gamma |- t1 \in T1      Gamma |- t2 \in List T1
             -----------------------------------------------           (T_Cons)
                    Gamma |- cons t1 t2 \in List T1

                        Gamma |- t1 \in List T1
                        Gamma |- t2 \in T2
                (h|->T1; t|->List T1; Gamma) |- t3 \in T2
          ---------------------------------------------------         (T_Lcase)
          Gamma |- (case t1 of nil => t2 | h::t => t3) \in T2
*)

(* ================================================================= *)
(** ** General Recursion *)

(** Another facility found in most programming languages (including
    Coq) is the ability to define recursive functions.  For example,
    we would like to be able to define the factorial function like
    this:

      fact = \x:Nat,
                test x=0 then 1 else x * (fact (pred x)))

   Note that the right-hand side of this binder mentions the variable
   being bound -- something that is not allowed by our formalization of
   [let] above.

   Directly formalizing this "recursive definition" mechanism is possible,
   but it requires some extra effort: in particular, we'd have to
   pass around an "environment" of recursive function definitions in
   the definition of the [step] relation. *)

(** Here is another way of presenting recursive functions that is
    a bit more verbose but equally powerful and much more straightforward
    to formalize: instead of writing recursive definitions, we will define
    a _fixed-point operator_ called [fix] that performs the "unfolding"
    of the recursive definition in the right-hand side as needed, during
    reduction.

    For example, instead of

      fact = \x:Nat,
                test x=0 then 1 else x * (fact (pred x)))

    we will write:

      fact =
          fix
            (\f:Nat->Nat,
               \x:Nat,
                  test x=0 then 1 else x * (f (pred x)))
*)
(** We can derive the latter from the former as follows:

      - In the right-hand side of the definition of [fact], replace
        recursive references to [fact] by a fresh variable [f].

      - Add an abstraction binding [f] at the front, with an
        appropriate type annotation.  (Since we are using [f] in place
        of [fact], which had type [Nat->Nat], we should require [f]
        to have the same type.)  The new abstraction has type
        [(Nat->Nat) -> (Nat->Nat)].

      - Apply [fix] to this abstraction.  This application has
        type [Nat->Nat].

      - Use all of this as the right-hand side of an ordinary
        [let]-binding for [fact].
*)

(** The intuition is that the higher-order function [f] passed
    to [fix] is a _generator_ for the [fact] function: if [f] is
    applied to a function that "approximates" the desired behavior of
    [fact] up to some number [n] (that is, a function that returns
    correct results on inputs less than or equal to [n] but we don't
    care what it does on inputs greater than [n]), then [f] returns a
    slightly better approximation to [fact] -- a function that returns
    correct results for inputs up to [n+1].  Applying [fix] to this
    generator returns its _fixed point_, which is a function that
    gives the desired behavior for all inputs [n].

    (The term "fixed point" is used here in exactly the same sense as
    in ordinary mathematics, where a fixed point of a function [f] is
    an input [x] such that [f(x) = x].  Here, a fixed point of a
    function [F] of type [(Nat->Nat)->(Nat->Nat)] is a function [f] of
    type [Nat->Nat] such that [F f] behaves the same as [f].) *)

(** Syntax:

       t ::=                Terms
           | ...
           | fix t             fixed-point operator

   Reduction:

                                t1 --> t1'
                            ------------------                     (ST_Fix1)
                            fix t1 --> fix t1'

               --------------------------------------------      (ST_FixAbs)
               fix (\xf:T1.t1) --> [xf:=fix (\xf:T1.t1)] t1

   Typing:

                           Gamma |- t1 \in T1->T1
                           ----------------------                    (T_Fix)
                           Gamma |- fix t1 \in T1
*)

(** Let's see how [ST_FixAbs] works by reducing [fact 3 = fix F 3],
    where

    F = (\f. \x. test x=0 then 1 else x * (f (pred x)))

    (type annotations are omitted for brevity).

    fix F 3

[-->] [ST_FixAbs] + [ST_App1]

    (\x. test x=0 then 1 else x * (fix F (pred x))) 3

[-->] [ST_AppAbs]

    test 3=0 then 1 else 3 * (fix F (pred 3))

[-->] [ST_Test0_Nonzero]

    3 * (fix F (pred 3))

[-->] [ST_FixAbs + ST_Mult2]

    3 * ((\x. test x=0 then 1 else x * (fix F (pred x))) (pred 3))

[-->] [ST_PredNat + ST_Mult2 + ST_App2]

    3 * ((\x. test x=0 then 1 else x * (fix F (pred x))) 2)

[-->] [ST_AppAbs + ST_Mult2]

    3 * (test 2=0 then 1 else 2 * (fix F (pred 2)))

[-->] [ST_Test0_Nonzero + ST_Mult2]

    3 * (2 * (fix F (pred 2)))

[-->] [ST_FixAbs + 2 x ST_Mult2]

    3 * (2 * ((\x. test x=0 then 1 else x * (fix F (pred x))) (pred 2)))

[-->] [ST_PredNat + 2 x ST_Mult2 + ST_App2]

    3 * (2 * ((\x. test x=0 then 1 else x * (fix F (pred x))) 1))

[-->] [ST_AppAbs + 2 x ST_Mult2]

    3 * (2 * (test 1=0 then 1 else 1 * (fix F (pred 1))))

[-->] [ST_Test0_Nonzero + 2 x ST_Mult2]

    3 * (2 * (1 * (fix F (pred 1))))

[-->] [ST_FixAbs + 3 x ST_Mult2]

    3 * (2 * (1 * ((\x. test x=0 then 1 else x * (fix F (pred x))) (pred 1))))

[-->] [ST_PredNat + 3 x ST_Mult2 + ST_App2]

    3 * (2 * (1 * ((\x. test x=0 then 1 else x * (fix F (pred x))) 0)))

[-->] [ST_AppAbs + 3 x ST_Mult2]

    3 * (2 * (1 * (test 0=0 then 1 else 0 * (fix F (pred 0)))))

[-->] [ST_Test0Zero + 3 x ST_Mult2]

    3 * (2 * (1 * 1))

[-->] [ST_MultNats + 2 x ST_Mult2]

    3 * (2 * 1)

[-->] [ST_MultNats + ST_Mult2]

    3 * 2

[-->] [ST_MultNats]

    6
*)

(** One important point to note is that, unlike [Fixpoint]
    definitions in Coq, there is nothing to prevent functions defined
    using [fix] from diverging. *)

(** **** Exercise: 1 star, standard, optional (halve_fix) 

    Translate this informal recursive definition into one using [fix]:

      halve =
        \x:Nat,
           test x=0 then 0
           else test (pred x)=0 then 0
           else 1 + (halve (pred (pred x)))

(* FILL IN HERE *)
*)
(** [] *)

(** **** Exercise: 1 star, standard, optional (fact_steps) 

    Write down the sequence of steps that the term [fact 1] goes
    through to reduce to a normal form (assuming the usual reduction
    rules for arithmetic operations).

    (* FILL IN HERE *)
*)
(** [] *)

(** The ability to form the fixed point of a function of type [T->T]
    for any [T] has some surprising consequences.  In particular, it
    implies that _every_ type is inhabited by some term.  To see this,
    observe that, for every type [T], we can define the term

    fix (\x:T,x)

    By [T_Fix]  and [T_Abs], this term has type [T].  By [ST_FixAbs]
    it reduces to itself, over and over again.  Thus it is a
    _diverging element_ of [T].

    More usefully, here's an example using [fix] to define a
    two-argument recursive function:

    equal =
      fix
        (\eq:Nat->Nat->Bool,
           \m:Nat, \n:Nat,
             test m=0 then iszero n
             else test n=0 then fls
             else eq (pred m) (pred n))
*)
(** And finally, here is an example where [fix] is used to define a
    _pair_ of recursive functions (illustrating the fact that the type
    [T1] in the rule [T_Fix] need not be a function type):

      evenodd =
        fix
          (\eo: (Nat->Bool * Nat->Bool),
             let e = \n:Nat, test n=0 then tru else eo,snd (pred n) in
             let o = \n:Nat, test n=0 then fls else eo,fst (pred n) in
             (e,o))

      even = evenodd.fst
      odd  = evenodd.snd
*)

(* ================================================================= *)
(** ** Records *)

(** As a final example of a basic extension of the STLC, let's look
    briefly at how to define _records_ and their types.  Intuitively,
    records can be obtained from pairs by two straightforward
    generalizations: they are n-ary (rather than just binary) and
    their fields are accessed by _label_ (rather than position). *)

(** Syntax:

       t ::=                          Terms
           | ...
           | {i1=t1, ..., in=tn}         record
           | t.i                         projection

       v ::=                          Values
           | ...
           | {i1=v1, ..., in=vn}         record value

       T ::=                          Types
           | ...
           | {i1:T1, ..., in:Tn}         record type
*)

(** The generalization from products should be pretty obvious.  But
   it's worth noticing the ways in which what we've actually written is
   even _more_ informal than the informal syntax we've used in previous
   sections and chapters: we've used "[...]" in several places to mean "any
   number of these," and we've omitted explicit mention of the usual
   side condition that the labels of a record should not contain any
   repetitions. *)

(**
   Reduction:

                              ti --> ti'
                 ------------------------------------                  (ST_Rcd)
                     {i1=v1, ..., im=vm, in=ti , ...}
                 --> {i1=v1, ..., im=vm, in=ti', ...}

                              t0 --> t0'
                            --------------                           (ST_Proj1)
                            t0.i --> t0'.i

                      -------------------------                    (ST_ProjRcd)
                      {..., i=vi, ...}.i --> vi
*)
(** Again, these rules are a bit informal.  For example, the first rule
   is intended to be read "if [ti] is the leftmost field that is not a
   value and if [ti] steps to [ti'], then the whole record steps..."
   In the last rule, the intention is that there should be only one
   field called [i], and that all the other fields must contain values. *)

(**
   The typing rules are also simple:

            Gamma |- t1 \in T1     ...     Gamma |- tn \in Tn
          ----------------------------------------------------          (T_Rcd)
          Gamma |- {i1=t1, ..., in=tn} \in {i1:T1, ..., in:Tn}

                    Gamma |- t0 \in {..., i:Ti, ...}
                    --------------------------------                   (T_Proj)
                          Gamma |- t0.i \in Ti
*)

(** There are several ways to approach formalizing the above
    definitions.

      - We can directly formalize the syntactic forms and inference
        rules, staying as close as possible to the form we've given
        them above.  This is conceptually straightforward, and it's
        probably what we'd want to do if we were building a real
        compiler (in particular, it will allow us to print error
        messages in the form that programmers will find easy to
        understand).  But the formal versions of the rules will not be
        very pretty or easy to work with, because all the [...]s above
        will have to be replaced with explicit quantifications or
        comprehensions.  For this reason, records are not included in
        the extended exercise at the end of this chapter.  (It is
        still useful to discuss them informally here because they will
        help motivate the addition of subtyping to the type system
        when we get to the [Sub] chapter.)

      - Alternatively, we could look for a smoother way of presenting
        records -- for example, a binary presentation with one
        constructor for the empty record and another constructor for
        adding a single field to an existing record, instead of a
        single monolithic constructor that builds a whole record at
        once.  This is the right way to go if we are primarily
        interested in studying the metatheory of the calculi with
        records, since it leads to clean and elegant definitions and
        proofs.  Chapter [Records] shows how this can be done.

      - Finally, if we like, we can avoid formalizing records
        altogether, by stipulating that record notations are just
        informal shorthands for more complex expressions involving
        pairs and product types.  We sketch this approach in the next
        section. *)

(* ----------------------------------------------------------------- *)
(** *** Encoding Records (Optional) *)

(** Let's see how records can be encoded using just pairs and
    [unit].  (This clever encoding, as well as the observation that it
    also extends to systems with subtyping, is due to Luca Cardelli.)

    First, observe that we can encode arbitrary-size _tuples_ using
    nested pairs and the [unit] value.  To avoid overloading the pair
    notation [(t1,t2)], we'll use curly braces without labels to write
    down tuples, so [{}] is the empty tuple, [{5}] is a singleton
    tuple, [{5,6}] is a 2-tuple (morally the same as a pair),
    [{5,6,7}] is a triple, etc.

      {} ----> unit {t1, t2, ..., tn} ----> (t1, trest) where {t2,
      ..., tn} ----> trest

    Similarly, we can encode tuple types using nested product types:

      {} ----> Unit {T1, T2, ..., Tn} ----> T1 * TRest where {T2, ...,
      Tn} ----> TRest

    The operation of projecting a field from a tuple can be encoded
    using a sequence of second projections followed by a first
    projection:

      t.0 ----> t.fst t.(n+1) ----> (t.snd).n

    Next, suppose that there is some total ordering on record labels,
    so that we can associate each label with a unique natural number.
    This number is called the _position_ of the label.  For example,
    we might assign positions like this:

      LABEL POSITION a 0 b 1 c 2 ...  ...  bar 1395 ...  ...  foo 4460
      ...  ...

    We use these positions to encode record values as tuples (i.e., as
    nested pairs) by sorting the fields according to their positions.
    For example:

      {a=5,b=6} ----> {5,6} {a=5,c=7} ----> {5,unit,7} {c=7,a=5} ---->
      {5,unit,7} {c=5,b=3} ----> {unit,3,5} {f=8,c=5,a=7} ---->
      {7,unit,5,unit,unit,8} {f=8,c=5} ----> {unit,unit,5,unit,unit,8}

    Note that each field appears in the position associated with its
    label, that the size of the tuple is determined by the label with
    the highest position, and that we fill in unused positions with
    [unit].

    We do exactly the same thing with record types:

      {a:Nat,b:Nat} ----> {Nat,Nat} {c:Nat,a:Nat} ----> {Nat,Unit,Nat}
      {f:Nat,c:Nat} ----> {Unit,Unit,Nat,Unit,Unit,Nat}

    Finally, record projection is encoded as a tuple projection from
    the appropriate position:

      t.l ----> t.(position of l)

    It is not hard to check that all the typing rules for the original
    "direct" presentation of records are validated by this
    encoding.  (The reduction rules are "almost validated" -- not
    quite, because the encoding reorders fields.) *)

(** Of course, this encoding will not be very efficient if we
    happen to use a record with label [foo]!  But things are not
    actually as bad as they might seem: for example, if we assume that
    our compiler can see the whole program at the same time, we can
    _choose_ the numbering of labels so that we assign small positions
    to the most frequently used labels.  Indeed, there are industrial
    compilers that essentially do this! *)

(* ----------------------------------------------------------------- *)
(** *** Variants (Optional) *)

(** Just as products can be generalized to records, sums can be
    generalized to n-ary labeled types called _variants_.  Instead of
    [T1+T2], we can write something like [<l1:T1,l2:T2,...ln:Tn>]
    where [l1],[l2],... are field labels which are used both to build
    instances and as case arm labels.

    These n-ary variants give us almost enough mechanism to build
    arbitrary inductive data types like lists and trees from
    scratch -- the only thing missing is a way to allow _recursion_ in
    type definitions.  We won't cover this here, but detailed
    treatments can be found in many textbooks -- e.g., Types and
    Programming Languages [Pierce 2002] (in Bib.v). *)

(* ################################################################# *)
(** * Exercise: Formalizing the Extensions *)

Module STLCExtended.

(** **** Exercise: 3 stars, standard (STLCE_definitions) 

    In this series of exercises, you will formalize some of the
    extensions described in this chapter.  We've provided the
    necessary additions to the syntax of terms and types, and we've
    included a few examples that you can test your definitions with
    to make sure they are working as expected.  You'll fill in the
    rest of the definitions and extend all the proofs accordingly.

    To get you started, we've provided implementations for:
     - numbers
     - sums
     - lists
     - unit

    You need to complete the implementations for:
     - pairs
     - let (which involves binding)
     - [fix]

    A good strategy is to work on the extensions one at a time, in two
    passes, rather than trying to work through the file from start to
    finish in a single pass.  For each definition or proof, begin by
    reading carefully through the parts that are provided for you,
    referring to the text in the [Stlc] chapter for high-level
    intuitions and the embedded comments for detailed mechanics. *)

(* ----------------------------------------------------------------- *)
(** *** Syntax *)

Inductive ty : Type :=
  | Ty_Arrow : ty -> ty -> ty
  | Ty_Nat  : ty
  | Ty_Sum  : ty -> ty -> ty
  | Ty_List : ty -> ty
  | Ty_Unit : ty
  | Ty_Prod : ty -> ty -> ty.

Inductive tm : Type :=
  (* pure STLC *)
  | tm_var : string -> tm
  | tm_app : tm -> tm -> tm
  | tm_abs : string -> ty -> tm -> tm
  (* numbers *)
  | tm_const: nat -> tm
  | tm_succ : tm -> tm
  | tm_pred : tm -> tm
  | tm_mult : tm -> tm -> tm
  | tm_if0  : tm -> tm -> tm -> tm
  (* sums *)
  | tm_inl : ty -> tm -> tm
  | tm_inr : ty -> tm -> tm
  | tm_case : tm -> string -> tm -> string -> tm -> tm
          (* i.e., [case t0 of inl x1 => t1 | inr x2 => t2] *)
  (* lists *)
  | tm_nil : ty -> tm
  | tm_cons : tm -> tm -> tm
  | tm_lcase : tm -> tm -> string -> string -> tm -> tm
           (* i.e., [case t1 of | nil => t2 | x::y => t3] *)
  (* unit *)
  | tm_unit : tm

  (* You are going to be working on the following extensions: *)

  (* pairs *)
  | tm_pair : tm -> tm -> tm
  | tm_fst : tm -> tm
  | tm_snd : tm -> tm
  (* let *)
  | tm_let : string -> tm -> tm -> tm
         (* i.e., [let x = t1 in t2] *)
  (* fix *)
  | tm_fix  : tm -> tm.

(** Note that, for brevity, we've omitted booleans and instead
    provided a single [if0] form combining a zero test and a
    conditional.  That is, instead of writing

       if x = 0 then ... else ...

    we'll write this:

       if0 x then ... else ...
*)

Definition x : string := "x".
Definition y : string := "y".
Definition z : string := "z".

Hint Unfold x : core.
Hint Unfold y : core.
Hint Unfold z : core.


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

Notation "'Nat'" := Ty_Nat (in custom stlc_ty at level 0).
Notation "'succ' x" := (tm_succ x) (in custom stlc at level 0,
                                     x custom stlc at level 0).
Notation "'pred' x" := (tm_pred x) (in custom stlc at level 0,
                                     x custom stlc at level 0).
Notation "x * y" := (tm_mult x y) (in custom stlc at level 1,
                                      left associativity).
Notation "'if0' x 'then' y 'else' z" :=
  (tm_if0 x y z) (in custom stlc at level 89,
                    x custom stlc at level 99,
                    y custom stlc at level 99,
                    z custom stlc at level 99,
                    left associativity).
Coercion tm_const : nat >-> tm.

Notation "S + T" :=
  (Ty_Sum S T) (in custom stlc_ty at level 3, left associativity).
Notation "'inl' T t" := (tm_inl T t) (in custom stlc at level 0,
                                         T custom stlc_ty at level 0,
                                         t custom stlc at level 0).
Notation "'inr' T t" := (tm_inr T t) (in custom stlc at level 0,
                                         T custom stlc_ty at level 0,
                                         t custom stlc at level 0).
Notation "'case' t0 'of' '|' 'inl' x1 '=>' t1 '|' 'inr' x2 '=>' t2" :=
  (tm_case t0 x1 t1 x2 t2) (in custom stlc at level 89,
                               t0 custom stlc at level 99,
                               x1 custom stlc at level 99,
                               t1 custom stlc at level 99,
                               x2 custom stlc at level 99,
                               t2 custom stlc at level 99,
                               left associativity).

Notation "X * Y" :=
  (Ty_Prod X Y) (in custom stlc_ty at level 2, X custom stlc_ty, Y custom stlc_ty at level 0).
Notation "( x ',' y )" := (tm_pair x y) (in custom stlc at level 0,
                                                x custom stlc at level 99,
                                                y custom stlc at level 99).
Notation "t '.fst'" := (tm_fst t) (in custom stlc at level 0).
Notation "t '.snd'" := (tm_snd t) (in custom stlc at level 0).

Notation "'List' T" :=
  (Ty_List T) (in custom stlc_ty at level 4).
Notation "'nil' T" := (tm_nil T) (in custom stlc at level 0, T custom stlc_ty at level 0).
Notation "h '::' t" := (tm_cons h t) (in custom stlc at level 2, right associativity).
Notation "'case' t1 'of' '|' 'nil' '=>' t2 '|' x '::' y '=>' t3" :=
  (tm_lcase t1 t2 x y t3) (in custom stlc at level 89,
                              t1 custom stlc at level 99,
                              t2 custom stlc at level 99,
                              x constr at level 1,
                              y constr at level 1,
                              t3 custom stlc at level 99,
                              left associativity).

Notation "'Unit'" :=
  (Ty_Unit) (in custom stlc_ty at level 0).
Notation "'unit'" := tm_unit (in custom stlc at level 0).

Notation "'let' x '=' t1 'in' t2" :=
  (tm_let x t1 t2) (in custom stlc at level 0).

Notation "'fix' t" := (tm_fix t) (in custom stlc at level 0).



(* ----------------------------------------------------------------- *)
(** *** Substitution *)

Reserved Notation "'[' x ':=' s ']' t" (in custom stlc at level 20, x constr).
Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  (* pure STLC *)
  | tm_var y =>
      if eqb_string x y then s else t
  | <{\y:T, t1}> =>
      if eqb_string x y then t else <{\y:T, [x:=s] t1}>
  | <{t1 t2}> =>
      <{([x:=s] t1) ([x:=s] t2)}>
  (* numbers *)
  | tm_const _ =>
      t
  | <{succ t1}> =>
      <{succ [x := s] t1}>
  | <{pred t1}> =>
      <{pred [x := s] t1}>
  | <{t1 * t2}> =>
      <{ ([x := s] t1) * ([x := s] t2)}>
  | <{if0 t1 then t2 else t3}> =>
      <{if0 [x := s] t1 then [x := s] t2 else [x := s] t3}>
  (* sums *)
  | <{inl T2 t1}> =>
      <{inl T2 ( [x:=s] t1) }>
  | <{inr T1 t2}> =>
      <{inr T1 ( [x:=s] t2) }>
  | <{case t0 of | inl y1 => t1 | inr y2 => t2}> =>
      <{case ([x:=s] t0) of
         | inl y1 => { if eqb_string x y1 then t1 else <{ [x:=s] t1 }> }
         | inr y2 => {if eqb_string x y2 then t2 else <{ [x:=s] t2 }> } }>
  (* lists *)
  | <{nil _}> =>
      t
  | <{t1 :: t2}> =>
      <{ ([x:=s] t1) :: [x:=s] t2 }>
  | <{case t1 of | nil => t2 | y1 :: y2 => t3}> =>
      <{case ( [x:=s] t1 ) of
        | nil => [x:=s] t2
        | y1 :: y2 =>
        {if eqb_string x y1 then
           t3
         else if eqb_string x y2 then t3
              else <{ [x:=s] t3 }> } }>
  (* unit *)
  | <{unit}> => <{unit}>

  (* Complete the following cases. *)

  (* pairs *)
  (* FILL IN HERE *)
  (* let *)
  (* FILL IN HERE *)
  (* fix *)
  (* FILL IN HERE *)
  | _ => t  (* ... and delete this line when you finish the exercise *)
  end

where "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc).

(* ----------------------------------------------------------------- *)
(** *** Reduction *)

(** Next we define the values of our language. *)

Inductive value : tm -> Prop :=
  (* In pure STLC, function abstractions are values: *)
  | v_abs : forall x T2 t1,
      value <{\x:T2, t1}>
  (* Numbers are values: *)
  | v_nat : forall n : nat,
      value <{n}>
  (* A tagged value is a value:  *)
  | v_inl : forall v T1,
      value v ->
      value <{inl T1 v}>
  | v_inr : forall v T1,
      value v ->
      value <{inr T1 v}>
  (* A list is a value iff its head and tail are values: *)
  | v_lnil : forall T1, value <{nil T1}>
  | v_lcons : forall v1 v2,
      value v1 ->
      value v2 ->
      value <{v1 :: v2}>
  (* A unit is always a value *)
  | v_unit : value <{unit}>
  (* A pair is a value if both components are: *)
  | v_pair : forall v1 v2,
      value v1 ->
      value v2 ->
      value <{(v1, v2)}>.

Hint Constructors value : core.

Reserved Notation "t '-->' t'" (at level 40).

Inductive step : tm -> tm -> Prop :=
  (* pure STLC *)
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
  (* numbers *)
  | ST_Succ : forall t1 t1',
         t1 --> t1' ->
         <{succ t1}> --> <{succ t1'}>
  | ST_SuccNat : forall n : nat,
         <{succ n}> --> <{ {S n} }>
  | ST_Pred : forall t1 t1',
         t1 --> t1' ->
         <{pred t1}> --> <{pred t1'}>
  | ST_PredNat : forall n:nat,
         <{pred n}> --> <{ {n - 1} }>
  | ST_Mulconsts : forall n1 n2 : nat,
         <{n1 * n2}> --> <{ {n1 * n2} }>
  | ST_Mult1 : forall t1 t1' t2,
         t1 --> t1' ->
         <{t1 * t2}> --> <{t1' * t2}>
  | ST_Mult2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         <{v1 * t2}> --> <{v1 * t2'}>
  | ST_If0 : forall t1 t1' t2 t3,
         t1 --> t1' ->
         <{if0 t1 then t2 else t3}> --> <{if0 t1' then t2 else t3}>
  | ST_If0_Zero : forall t2 t3,
         <{if0 0 then t2 else t3}> --> t2
  | ST_If0_Nonzero : forall n t2 t3,
         <{if0 {S n} then t2 else t3}> --> t3
  (* sums *)
  | ST_Inl : forall t1 t1' T2,
        t1 --> t1' ->
        <{inl T2 t1}> --> <{inl T2 t1'}>
  | ST_Inr : forall t2 t2' T1,
        t2 --> t2' ->
        <{inr T1 t2}> --> <{inr T1 t2'}>
  | ST_Case : forall t0 t0' x1 t1 x2 t2,
        t0 --> t0' ->
        <{case t0 of | inl x1 => t1 | inr x2 => t2}> -->
        <{case t0' of | inl x1 => t1 | inr x2 => t2}>
  | ST_CaseInl : forall v0 x1 t1 x2 t2 T2,
        value v0 ->
        <{case inl T2 v0 of | inl x1 => t1 | inr x2 => t2}> --> <{ [x1:=v0]t1 }>
  | ST_CaseInr : forall v0 x1 t1 x2 t2 T1,
        value v0 ->
        <{case inr T1 v0 of | inl x1 => t1 | inr x2 => t2}> --> <{ [x2:=v0]t2 }>
  (* lists *)
  | ST_Cons1 : forall t1 t1' t2,
       t1 --> t1' ->
       <{t1 :: t2}> --> <{t1' :: t2}>
  | ST_Cons2 : forall v1 t2 t2',
       value v1 ->
       t2 --> t2' ->
       <{v1 :: t2}> --> <{v1 :: t2'}>
  | ST_Lcase1 : forall t1 t1' t2 x1 x2 t3,
       t1 --> t1' ->
       <{case t1 of | nil => t2 | x1 :: x2 => t3}> -->
       <{case t1' of | nil => t2 | x1 :: x2 => t3}>
  | ST_LcaseNil : forall T1 t2 x1 x2 t3,
       <{case nil T1 of | nil => t2 | x1 :: x2 => t3}> --> t2
  | ST_LcaseCons : forall v1 vl t2 x1 x2 t3,
       value v1 ->
       value vl ->
       <{case v1 :: vl of | nil => t2 | x1 :: x2 => t3}>
         -->  <{ [x2 := vl] ([x1 := v1] t3) }>

  (* Add rules for the following extensions. *)

  (* pairs *)
  (* FILL IN HERE *)
  (* let *)
  (* FILL IN HERE *)
  (* fix *)
  (* FILL IN HERE *)

  where "t '-->' t'" := (step t t').

Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

Hint Constructors step : core.

(* ----------------------------------------------------------------- *)
(** *** Typing *)

Definition context := partial_map ty.

(** Next we define the typing rules.  These are nearly direct
    transcriptions of the inference rules shown above. *)

Reserved Notation "Gamma '|-' t '\in' T" (at level 40, t custom stlc, T custom stlc_ty at level 0).

Inductive has_type : context -> tm -> ty -> Prop :=
  (* pure STLC *)
  | T_Var : forall Gamma x T1,
      Gamma x = Some T1 ->
      Gamma |- x \in T1
  | T_Abs : forall Gamma x T1 T2 t1,
    (x |-> T2 ; Gamma) |- t1 \in T1 ->
      Gamma |- \x:T2, t1 \in (T2 -> T1)
  | T_App : forall T1 T2 Gamma t1 t2,
      Gamma |- t1 \in (T2 -> T1) ->
      Gamma |- t2 \in T2 ->
      Gamma |- t1 t2 \in T1
  (* numbers *)
  | T_Nat : forall Gamma (n : nat),
      Gamma |- n \in Nat
  | T_Succ : forall Gamma t,
      Gamma |- t \in Nat ->
      Gamma |- succ t \in Nat
  | T_Pred : forall Gamma t,
      Gamma |- t \in Nat ->
      Gamma |- pred t \in Nat
  | T_Mult : forall Gamma t1 t2,
      Gamma |- t1 \in Nat ->
      Gamma |- t2 \in Nat ->
      Gamma |- t1 * t2 \in Nat
  | T_If0 : forall Gamma t1 t2 t3 T0,
      Gamma |- t1 \in Nat ->
      Gamma |- t2 \in T0 ->
      Gamma |- t3 \in T0 ->
      Gamma |- if0 t1 then t2 else t3 \in T0
  (* sums *)
  | T_Inl : forall Gamma t1 T1 T2,
      Gamma |- t1 \in T1 ->
      Gamma |- (inl T2 t1) \in (T1 + T2)
  | T_Inr : forall Gamma t2 T1 T2,
      Gamma |- t2 \in T2 ->
      Gamma |- (inr T1 t2) \in (T1 + T2)
  | T_Case : forall Gamma t0 x1 T1 t1 x2 T2 t2 T3,
      Gamma |- t0 \in (T1 + T2) ->
      (x1 |-> T1 ; Gamma) |- t1 \in T3 ->
      (x2 |-> T2 ; Gamma) |- t2 \in T3 ->
      Gamma |- (case t0 of | inl x1 => t1 | inr x2 => t2) \in T3
  (* lists *)
  | T_Nil : forall Gamma T1,
      Gamma |- (nil T1) \in (List T1)
  | T_Cons : forall Gamma t1 t2 T1,
      Gamma |- t1 \in T1 ->
      Gamma |- t2 \in (List T1) ->
      Gamma |- (t1 :: t2) \in (List T1)
  | T_Lcase : forall Gamma t1 T1 t2 x1 x2 t3 T2,
      Gamma |- t1 \in (List T1) ->
      Gamma |- t2 \in T2 ->
      (x1 |-> T1 ; x2 |-> <{{List T1}}> ; Gamma) |- t3 \in T2 ->
      Gamma |- (case t1 of | nil => t2 | x1 :: x2 => t3) \in T2
  (* unit *)
  | T_Unit : forall Gamma,
      Gamma |- unit \in Unit

  (* Add rules for the following extensions. *)

  (* pairs *)
  (* FILL IN HERE *)
  (* let *)
  (* FILL IN HERE *)
  (* fix *)
  (* FILL IN HERE *)

where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Hint Constructors has_type : core.

(* Do not modify the following line: *)
Definition manual_grade_for_extensions_definition : option (nat*string) := None.
(** [] *)

(* ================================================================= *)
(** ** Examples *)

(** **** Exercise: 3 stars, standard (STLCE_examples) 

    This section presents formalized versions of the examples from
    above (plus several more).

    For each example, uncomment proofs and replace [Admitted] by
    [Qed] once you've implemented enough of the definitions for
    the tests to pass.

    The examples at the beginning focus on specific features; you can
    use these to make sure your definition of a given feature is
    reasonable before moving on to extending the proofs later in the
    file with the cases relating to this feature.
    The later examples require all the features together, so you'll
    need to come back to these when you've got all the definitions
    filled in. *)

Module Examples.

(* ----------------------------------------------------------------- *)
(** *** Preliminaries *)

(** First, let's define a few variable names: *)

Open Scope string_scope.
(*  NOTATION: LATER: These can all be Notations -- just make sure to add a
   [Hint Unfold] for each one. *)
Notation x := "x".
Notation y := "y".
Notation a := "a".
Notation f := "f".
Notation g := "g".
Notation l := "l".
Notation k := "k".
Notation i1 := "i1".
Notation i2 := "i2".
Notation processSum := "processSum".
Notation n := "n".
Notation eq := "eq".
Notation m := "m".
Notation evenodd := "evenodd".
Notation even := "even".
Notation odd := "odd".
Notation eo := "eo".

(** Next, a bit of Coq hackery to automate searching for typing
    derivations.  You don't need to understand this bit in detail --
    just have a look over it so that you'll know what to look for if
    you ever find yourself needing to make custom extensions to
    [auto].

    The following [Hint] declarations say that, whenever [auto]
    arrives at a goal of the form [(Gamma |- (tm_app e1 e1) \in T)], it
    should consider [eapply T_App], leaving an existential variable
    for the middle type T1, and similar for [lcase]. That variable
    will then be filled in during the search for type derivations for
    [e1] and [e2].  We also include a hint to "try harder" when
    solving equality goals; this is useful to automate uses of
    [T_Var] (which includes an equality as a precondition). *)

Hint Extern 2 (has_type _ (tm_app _ _) _) =>
  eapply T_App; auto : core.
Hint Extern 2 (has_type _ (tm_lcase _ _ _ _ _) _) =>
  eapply T_Lcase; auto : core.
Hint Extern 2 (_ = _) => compute; reflexivity : core.

(* ----------------------------------------------------------------- *)
(** *** Numbers *)

Module Numtest.

(* tm_test0 (pred (succ (pred (2 * 0))) then 5 else 6 *)
Definition test :=
  <{if0
    (pred
      (succ
        (pred
          (2 * 0))))
    then 5
    else 6}>.

Example typechecks :
  empty |- test \in Nat.
Proof.
  unfold test.
  (* This typing derivation is quite deep, so we need
     to increase the max search depth of [auto] from the
     default 5 to 10. *)
  auto 10.
(* FILL IN HERE *) Admitted.

Example numtest_reduces :
  test -->* 5.
Proof.
(* 
  unfold test. normalize.
*)
(* FILL IN HERE *) Admitted.

End Numtest.

(* ----------------------------------------------------------------- *)
(** *** Products *)

Module Prodtest.

(* ((5,6),7).fst.tm_snd *)
Definition test :=
  <{((5,6),7).fst.snd}>.

Example typechecks :
  empty |- test \in Nat.
Proof. unfold test. eauto 15. (* FILL IN HERE *) Admitted.
(* GRADE_THEOREM 0.25: typechecks *)

Example reduces :
  test -->* 6.
Proof.
(* 
  unfold test. normalize.
*)
(* FILL IN HERE *) Admitted.
(* GRADE_THEOREM 0.25: reduces *)

End Prodtest.

(* ----------------------------------------------------------------- *)
(** *** [let] *)

Module LetTest.

(* let x = pred 6 in succ x *)
Definition test :=
  <{let x = (pred 6) in
    (succ x)}>.

Example typechecks :
  empty |- test \in Nat.
Proof. unfold test. eauto 15. (* FILL IN HERE *) Admitted.
(* GRADE_THEOREM 0.25: typechecks *)

Example reduces :
  test -->* 6.
Proof.
(* 
  unfold test. normalize.
*)
(* FILL IN HERE *) Admitted.
(* GRADE_THEOREM 0.25: reduces *)

End LetTest.

(* ----------------------------------------------------------------- *)
(** *** Sums *)

Module Sumtest1.

(* case (inl Nat 5) of
     inl x => x
   | inr y => y *)

Definition test :=
  <{case (inl Nat 5) of
    | inl x => x
    | inr y => y}>.

Example typechecks :
  empty |- test \in Nat.
Proof. unfold test. eauto 15. (* FILL IN HERE *) Admitted.

Example reduces :
  test -->* 5.
Proof.
(* 
  unfold test. normalize.
*)
(* FILL IN HERE *) Admitted.

End Sumtest1.

Module Sumtest2.

(* let processSum =
     \x:Nat+Nat.
        case x of
          inl n => n
          inr n => tm_test0 n then 1 else 0 in
   (processSum (inl Nat 5), processSum (inr Nat 5))    *)

Definition test :=
  <{let processSum =
    (\x:Nat + Nat,
      case x of
       | inl n => n
       | inr n => (if0 n then 1 else 0)) in
    (processSum (inl Nat 5), processSum (inr Nat 5))}>.

Example typechecks :
  empty |- test \in (Nat * Nat).
Proof. unfold test. eauto 15. (* FILL IN HERE *) Admitted.

Example reduces :
  test -->* <{(5, 0)}>.
Proof.
(* 
  unfold test. normalize.
*)
(* FILL IN HERE *) Admitted.

End Sumtest2.

(* ----------------------------------------------------------------- *)
(** *** Lists *)

Module ListTest.

(* let l = cons 5 (cons 6 (nil Nat)) in
   case l of
     nil => 0
   | x::y => x*x *)

Definition test :=
  <{let l = (5 :: 6 :: (nil Nat)) in
    case l of
    | nil => 0
    | x :: y => (x * x)}>.

Example typechecks :
  empty |- test \in Nat.
Proof. unfold test. eauto 20. (* FILL IN HERE *) Admitted.

Example reduces :
  test -->* 25.
Proof.
(* 
  unfold test. normalize.
*)
(* FILL IN HERE *) Admitted.

End ListTest.

(* ----------------------------------------------------------------- *)
(** *** [fix] *)

Module FixTest1.

(* fact := fix
             (\f:nat->nat.
                \a:nat.
                   test a=0 then 1 else a * (f (pred a))) *)
Definition fact :=
  <{fix
      (\f:Nat->Nat,
        \a:Nat,
         if0 a then 1 else (a * (f (pred a))))}>.

(** (Warning: you may be able to typecheck [fact] but still have some
    rules wrong!) *)

Example typechecks :
  empty |- fact \in (Nat -> Nat).
Proof. unfold fact. auto 10. (* FILL IN HERE *) Admitted.
(* GRADE_THEOREM 0.25: typechecks *)

Example reduces :
  <{fact 4}> -->* 24.
Proof.
(* 
  unfold fact. normalize.
*)
(* FILL IN HERE *) Admitted.
(* GRADE_THEOREM 0.25: reduces *)

End FixTest1.

Module FixTest2.

(* map :=
     \g:nat->nat.
       fix
         (\f:[nat]->[nat].
            \l:[nat].
               case l of
               | [] -> []
               | x::l -> (g x)::(f l)) *)
Definition map :=
  <{ \g:Nat->Nat,
       fix
         (\f:(List Nat)->(List Nat),
            \l:List Nat,
               case l of
               | nil => nil Nat
               | x::l => ((g x)::(f l)))}>.

Example typechecks :
  empty |- map \in
    ((Nat -> Nat) -> ((List Nat) -> (List Nat))).
Proof. unfold map. auto 10. (* FILL IN HERE *) Admitted.
(* GRADE_THEOREM 0.25: typechecks *)

Example reduces :
  <{map (\a:Nat, succ a) (1 :: 2 :: (nil Nat))}>
  -->* <{2 :: 3 :: (nil Nat)}>.
Proof.
(* 
  unfold map. normalize.
*)
(* FILL IN HERE *) Admitted.
(* GRADE_THEOREM 0.25: reduces *)

End FixTest2.

Module FixTest3.

(* equal =
      fix
        (\eq:Nat->Nat->Bool.
           \m:Nat. \n:Nat.
             tm_test0 m then (tm_test0 n then 1 else 0)
             else tm_test0 n then 0
             else eq (pred m) (pred n))   *)

Definition equal :=
  <{fix
        (\eq:Nat->Nat->Nat,
           \m:Nat, \n:Nat,
             if0 m then (if0 n then 1 else 0)
             else (if0 n
                   then 0
                   else (eq (pred m) (pred n))))}>.

Example typechecks :
  empty |- equal \in (Nat -> Nat -> Nat).
Proof. unfold equal. auto 10. (* FILL IN HERE *) Admitted.
(* GRADE_THEOREM 0.25: typechecks *)

Example reduces :
  <{equal 4 4}> -->* 1.
Proof.
(* 
  unfold equal. normalize.
*)
(* FILL IN HERE *) Admitted.
(* GRADE_THEOREM 0.25: reduces *)

Example reduces2 :
  <{equal 4 5}> -->* 0.
Proof.
(* 
  unfold equal. normalize.
*)
(* FILL IN HERE *) Admitted.

End FixTest3.

Module FixTest4.

(* let evenodd =
         fix
           (\eo: (Nat->Nat * Nat->Nat).
              let e = \n:Nat. tm_test0 n then 1 else eo.tm_snd (pred n) in
              let o = \n:Nat. tm_test0 n then 0 else eo.tm_fst (pred n) in
              (e,o)) in
    let even = evenodd.tm_fst in
    let odd  = evenodd.tm_snd in
    (even 3, even 4)
*)

Definition eotest :=
<{let evenodd =
         fix
           (\eo: ((Nat -> Nat) * (Nat -> Nat)),
              (\n:Nat, if0 n then 1 else (eo.snd (pred n)),
               \n:Nat, if0 n then 0 else (eo.fst (pred n)))) in
    let even = evenodd.fst in
    let odd  = evenodd.snd in
    (even 3, even 4)}>.

Example typechecks :
  empty |- eotest \in (Nat * Nat).
Proof. unfold eotest. eauto 30. (* FILL IN HERE *) Admitted.
(* GRADE_THEOREM 0.25: typechecks *)

Example reduces :
  eotest -->* <{(0, 1)}>.
Proof.
(* 
  unfold eotest. normalize.
*)
(* FILL IN HERE *) Admitted.
(* GRADE_THEOREM 0.25: reduces *)

End FixTest4.

End Examples.
(** [] *)

(* ================================================================= *)
(** ** Properties of Typing *)

(** The proofs of progress and preservation for this enriched system
    are essentially the same (though of course longer) as for the pure
    STLC. *)

(* ----------------------------------------------------------------- *)
(** *** Progress *)

(** **** Exercise: 3 stars, standard (STLCE_progress) 

    Complete the proof of [progress].

    Theorem: Suppose empty |- t \in T.  Then either
      1. t is a value, or
      2. t --> t' for some t'.

    Proof: By induction on the given typing derivation. *)

Theorem progress : forall t T,
     empty |- t \in T ->
     value t \/ exists t', t --> t'.
Proof with eauto.
  intros t T Ht.
  remember empty as Gamma.
  generalize dependent HeqGamma.
  induction Ht; intros HeqGamma; subst.
  - (* T_Var *)
    (* The final rule in the given typing derivation cannot be
       [T_Var], since it can never be the case that
       [empty |- x \in T] (since the context is empty). *)
    discriminate H.
  - (* T_Abs *)
    (* If the [T_Abs] rule was the last used, then
       [t = \ x0 : T2, t1], which is a value. *)
    left...
  - (* T_App *)
    (* If the last rule applied was T_App, then [t = t1 t2],
       and we know from the form of the rule that
         [empty |- t1 \in T1 -> T2]
         [empty |- t2 \in T1]
       By the induction hypothesis, each of t1 and t2 either is
       a value or can take a step. *)
    right.
    destruct IHHt1; subst...
    + (* t1 is a value *)
      destruct IHHt2; subst...
      * (* t2 is a value *)
        (* If both [t1] and [t2] are values, then we know that
           [t1 = \x0 : T0, t11], since abstractions are the
           only values that can have an arrow type.  But
           [(\x0 : T0, t11) t2 --> [x:=t2]t11] by [ST_AppAbs]. *)
        destruct H; try solve_by_invert.
        exists <{ [x0 := t2]t1 }>...
      * (* t2 steps *)
        (* If [t1] is a value and [t2 --> t2'],
           then [t1 t2 --> t1 t2'] by [ST_App2]. *)
        destruct H0 as [t2' Hstp]. exists <{t1 t2'}>...
    + (* t1 steps *)
      (* Finally, If [t1 --> t1'], then [t1 t2 --> t1' t2]
         by [ST_App1]. *)
      destruct H as [t1' Hstp]. exists <{t1' t2}>...
  - (* T_Nat *)
    left...
  - (* T_Succ *)
    right.
    destruct IHHt...
    + (* t1 is a value *)
      destruct H; try solve_by_invert.
      exists <{ {S n} }>...
    + (* t1 steps *)
      destruct H as [t' Hstp].
      exists <{succ t'}>...
  - (* T_Pred *)
    right.
    destruct IHHt...
    + (* t1 is a value *)
      destruct H; try solve_by_invert.
      exists <{ {n - 1} }>...
    + (* t1 steps *)
      destruct H as [t' Hstp].
      exists <{pred t'}>...
  - (* T_Mult *)
    right.
    destruct IHHt1...
    + (* t1 is a value *)
      destruct IHHt2...
      * (* t2 is a value *)
        destruct H; try solve_by_invert.
        destruct H0; try solve_by_invert.
        exists <{ {n * n0} }>...
      * (* t2 steps *)
        destruct H0 as [t2' Hstp].
        exists <{t1 * t2'}>...
    + (* t1 steps *)
      destruct H as [t1' Hstp].
      exists <{t1' * t2}>...
  - (* T_Test0 *)
    right.
    destruct IHHt1...
    + (* t1 is a value *)
      destruct H; try solve_by_invert.
      destruct n as [|n'].
      * (* n1=0 *)
        exists t2...
      * (* n1<>0 *)
        exists t3...
    + (* t1 steps *)
      destruct H as [t1' H0].
      exists <{if0 t1' then t2 else t3}>...
  - (* T_Inl *)
    destruct IHHt...
    + (* t1 steps *)
      right. destruct H as [t1' Hstp]...
      (* exists (tm_inl _ t1')... *)
  - (* T_Inr *)
    destruct IHHt...
    + (* t1 steps *)
      right. destruct H as [t1' Hstp]...
      (* exists (tm_inr _ t1')... *)
  - (* T_Case *)
    right.
    destruct IHHt1...
    + (* t0 is a value *)
      destruct H; try solve_by_invert.
      * (* t0 is inl *)
        exists <{ [x1:=v]t1 }>...
      * (* t0 is inr *)
        exists <{ [x2:=v]t2 }>...
    + (* t0 steps *)
      destruct H as [t0' Hstp].
      exists <{case t0' of | inl x1 => t1 | inr x2 => t2}>...
  - (* T_Nil *)
    left...
  - (* T_Cons *)
    destruct IHHt1...
    + (* head is a value *)
      destruct IHHt2...
      * (* tail steps *)
        right. destruct H0 as [t2' Hstp].
        exists <{t1 :: t2'}>...
    + (* head steps *)
      right. destruct H as [t1' Hstp].
      exists <{t1' :: t2}>...
  - (* T_Lcase *)
    right.
    destruct IHHt1...
    + (* t1 is a value *)
      destruct H; try solve_by_invert.
      * (* t1=tm_nil *)
        exists t2...
      * (* t1=tm_cons v1 v2 *)
        exists <{ [x2:=v2]([x1:=v1]t3) }>...
    + (* t1 steps *)
      destruct H as [t1' Hstp].
      exists <{case t1' of | nil => t2 | x1 :: x2 => t3}>...
  - (* T_Unit *)
    left...

  (* Complete the proof. *)

  (* pairs *)
  (* FILL IN HERE *)
  (* let *)
  (* FILL IN HERE *)
  (* fix *)
  (* FILL IN HERE *)
(* FILL IN HERE *) Admitted.

(* Do not modify the following line: *)
Definition manual_grade_for_progress : option (nat*string) := None.
(** [] *)

(* ================================================================= *)
(** ** Weakening *)

(** The weakening claim and (automated) proof are exactly the
    same as for the original STLC. (We only need to increase the
    search depth of eauto to 7.) *)

Lemma weakening : forall Gamma Gamma' t T,
     inclusion Gamma Gamma' ->
     Gamma  |- t \in T  ->
     Gamma' |- t \in T.
Proof.
  intros Gamma Gamma' t T H Ht.
  generalize dependent Gamma'.
  induction Ht; eauto 7 using inclusion_update.
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
(** *** Substitution *)

(** **** Exercise: 2 stars, standard (STLCE_subst_preserves_typing) 

    Complete the proof of [substitution_preserves_typing]. *)

Lemma substitution_preserves_typing : forall Gamma x U t v T,
  (x |-> U ; Gamma) |- t \in T ->
  empty |- v \in U   ->
  Gamma |- [x:=v]t \in T.
Proof with eauto.
  intros Gamma x U t v T Ht Hv.
  generalize dependent Gamma. generalize dependent T.
  (* Proof: By induction on the term [t].  Most cases follow
     directly from the IH, with the exception of [var]
     and [abs]. These aren't automatic because we must
     reason about how the variables interact. The proofs
     of these cases are similar to the ones in STLC.
     We refer the reader to StlcProp.v for explanations. *)
  induction t; intros T Gamma H;
  (* in each case, we'll want to get at the derivation of H *)
    inversion H; clear H; subst; simpl; eauto.
  - (* var *)
    rename s into y. destruct (eqb_stringP x y); subst.
    + (* x=y *)
      rewrite update_eq in H2.
      injection H2 as H2; subst.
      apply weakening_empty. assumption.
    + (* x<>y *)
      apply T_Var. rewrite update_neq in H2; auto.
  - (* abs *)
    rename s into y, t into S.
    destruct (eqb_stringP x y); subst; apply T_Abs.
    + (* x=y *)
      rewrite update_shadow in H5. assumption.
    + (* x<>y *)
      apply IHt.
      rewrite update_permute; auto.

  - (* tm_case *)
    rename s into x1, s0 into x2.
    eapply T_Case...
    + (* left arm *)
      destruct (eqb_stringP x x1); subst.
      * (* x = x1 *)
        rewrite update_shadow in H8. assumption.
      * (* x <> x1 *)
        apply IHt2.
        rewrite update_permute; auto.
    + (* right arm *)
      destruct (eqb_stringP x x2); subst.
      * (* x = x2 *)
        rewrite update_shadow in H9. assumption.
      * (* x <> x2 *)
        apply IHt3.
        rewrite update_permute; auto.
  - (* tm_lcase *)
    rename s into y1, s0 into y2.
    eapply T_Lcase...
    destruct (eqb_stringP x y1); subst.
    + (* x=y1 *)
      destruct (eqb_stringP y2 y1); subst.
      * (* y2=y1 *)
        repeat rewrite update_shadow in H9.
        rewrite update_shadow.
        assumption.
      * rewrite update_permute in H9; [|assumption].
        rewrite update_shadow in H9.
        rewrite update_permute;  assumption.
    + (* x<>y1 *)
      destruct (eqb_stringP x y2); subst.
      * (* x=y2 *)
        rewrite update_shadow in H9.
        assumption.
      * (* x<>y2 *)
        apply IHt3.
        rewrite (update_permute _ _ _ _ _ _ n0) in H9.
        rewrite (update_permute _ _ _ _ _ _ n) in H9.
        assumption.

  (* Complete the proof. *)

  (* FILL IN HERE *) Admitted.

(* Do not modify the following line: *)
Definition manual_grade_for_substitution_preserves_typing : option (nat*string) := None.
(** [] *)

(* ----------------------------------------------------------------- *)
(** *** Preservation *)

(** **** Exercise: 3 stars, standard (STLCE_preservation) 

    Complete the proof of [preservation]. *)

Theorem preservation : forall t t' T,
     empty |- t \in T  ->
     t --> t'  ->
     empty |- t' \in T.
Proof with eauto.
  intros t t' T HT. generalize dependent t'.
  remember empty as Gamma.
  (* Proof: By induction on the given typing derivation.  Many
     cases are contradictory ([T_Var], [T_Abs]).  We show just
     the interesting ones. Again, we refer the reader to
     StlcProp.v for explanations. *)
  induction HT;
    intros t' HE; subst; inversion HE; subst...
  - (* T_App *)
    inversion HE; subst...
    + (* ST_AppAbs *)
      apply substitution_preserves_typing with T2...
      inversion HT1...
  (* T_Case *)
  - (* ST_CaseInl *)
    inversion HT1; subst.
    eapply substitution_preserves_typing...
  - (* ST_CaseInr *)
    inversion HT1; subst.
    eapply substitution_preserves_typing...
  - (* T_Lcase *)
    + (* ST_LcaseCons *)
      inversion HT1; subst.
      apply substitution_preserves_typing with <{{List T1}}>...
      apply substitution_preserves_typing with T1...

  (* Complete the proof. *)

  (* fst and snd *)
  (* FILL IN HERE *)
  (* let *)
  (* FILL IN HERE *)
  (* fix *)
  (* FILL IN HERE *)
(* FILL IN HERE *) Admitted.

(* Do not modify the following line: *)
Definition manual_grade_for_preservation : option (nat*string) := None.
(** [] *)

End STLCExtended.

(* 2020-09-09 21:08 *)
