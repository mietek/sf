(** * Verif_sumarray: Introduction to Verifiable C *)

(* ================================================================= *)
(** ** Verified Software Toolchain *)

(** The Verified Software Toolchain is a toolset for proving the functional 
  correctness of C programs, with
  - a _program logic_ called Verifiable C, based on separation logic.
  - a _proof automation system_ called VST-Floyd that assists you in applying
    the program logic to your program.
  - a soundness proof in Coq, guaranteeing that whatever properties you
    prove about your program will actually hold in any execution of the
    C source-language operational semantics. And this proof _composes_
    with the correctness proof of the CompCert verified optimizing C compiler,
    so you can also get a guarantee about the behavior of the assembly 
    language program.

  This volume of _Software Foundations_ teaches you how to use Verifiable C
  and VST-Floyd to prove C programs correct.  In the process you'll learn
  some key concepts of Hoare Logic and Separation Logic.  This book does
  _not_ cover VST's soundness proof (which is described in the book
  _Program Logics for Certified Compilers_  [Appel 2014] (in Bib.v)). *)

(* ================================================================= *)
(** ** How to use this textbook *)

(** The first two chapters (this one and [Verif_reverse]) are a 
 feature-by-feature introduction to Verifiable C, demonstrated on two
 example C programs:  adding up an array and reversing a linked list.
 These chapters are best understood if you step through them in Coq, where
 you can see the proof goals at each stage; they are less useful to read in
 HTML.  These two chapters closely follow the first 48 mini-chapters of the
 _Verifiable C Reference Manual_, [VC.pdf], that is distributed with VST --
 -- and you can find a copy distributed with this volume of _Software 
 Foundations_.   The first two chapters have no exercises.

 This _Verifiable C_ volume of _Software Foundations_ is self-contained,
 so you should not need to look things up in the reference manual [VC.pdf].
 But to use features of Verifiable C beyond what's needed for this textbook,
 [VC.pdf] can be very useful.  The words SEE ALSO suggest which chapters
 of the reference manual cover the features discussed in this text.

 The remaining 7 chapters are _mainly_ exercises.  The best way to learn 
 is by doing it yourself -- so each chapter presents a little C program,
 and guides you through verifying it yourself.  The "capstone exercise"
 is the verification of a hash table with external chaining.
*)

(* ================================================================= *)
(** ** A C program to add up an array *)

(** Here is a little C program, [sumarray.c]:

    #include <stddef.h>

    unsigned sumarray(unsigned a[], int n) {
      int i; unsigned s;
      i=0;
      s=0;
      while (i<n) {
        s+=a[i];
        i++;
      }
      return s;
    }

    unsigned four[4] = {1,2,3,4};

    int main(void) {
      unsigned int s;
      s = sumarray(four,4);
      return (int)s;
    }
*)

(* ================================================================= *)
(** ** Workflow *)

(** SEE ALSO: VC.pdf Chapter 3 (Workflow),
     Chapter 4 (_Verifiable C and clightgen_), Chapter 5 (_ASTs_) *)

(** To verify a C program, such as [sumarray.c], use the CompCert
  front end to parse it into an Abstract Syntax Tree (AST).
  For all the chapters in this volume of _Software Foundations_ we've done
  that for you, so you don't have to install clightgen; but generally
  what you would do is,

   clightgen -normalize sumarray.c

  You would have installed [clightgen] as part of the CompCert tools, by
  mentioning the -clightgen option when you run ./configure when building CompCert.

  The output of [clightgen] would be a file [sumarray.v] that contains the Coq
  inductive data structure describing the syntax trees of the source
  program.  You can open [sumarray.v] in the current directory
  and inspect it. *)

(* ================================================================= *)
(** ** Let's verify! *)

(** SEE ALSO: VC.pdf Chapter 7 (_Functional model, API spec_) *)

(** This file, [Verif_sumarray.v], contains a _specification_
    of the functional correctness of the program [sumarray.c],
    followed by a proof that the program satisfies its specification.

    For larger programs, one would typically break this down into three
    or more files:
    - Functional model (often in the form of a Coq function)
    - API specification
    - Function-body correctness proofs, one per file. *)

(* ----------------------------------------------------------------- *)
(** *** Make sure you have the right version of VST installed *)

Require VC.Preface.  (* Check for the right version of VST *)

(* ----------------------------------------------------------------- *)
(** *** Standard boilerplate *)

(** Every API specification begins with the same standard boilerplate;
    the only thing that changes is the name of the program -- in this
    case, [sumarray]. *)

Require Import VST.floyd.proofauto.
Require Import VC.sumarray.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

(** The first line imports Verifiable C and its _Floyd_ proof-automation
    library.  The second line imports the AST of the program to be verified.
    The third line processes all the struct and union definitions
    in the AST, and the fourth line processes global variable declarations. *)

(* ----------------------------------------------------------------- *)
(** *** Functional model *)

(** To prove correctness of [sumarray.c], we start by writing a
   _functional model_ of adding up a sequence.  We can use a list-fold
   to express the sum of all the elements in a list of integers: *)

Definition sum_Z : list Z -> Z := fold_right Z.add 0.

(** Then we prove properties of the functional model: in this case,
    how [sum_Z] interacts with list append. *)

Lemma sum_Z_app:
  forall a b, sum_Z (a++b) =  sum_Z a + sum_Z b.
Proof.
  intros. induction a; simpl; lia.
Qed.

(** The data types used in a functional model can be any kind of mathematics
    at all, as long as we have a way to relate them to the integers, tuples,
    and sequences used in a C program.  But the mathematical integers [Z]
    and the 32-bit modular integers [Int.int] are often relevant.
    Notice that this functional spec does not depend on [sumarray.v] or on
    anything in the Verifiable C libraries. This is typical, and desirable:
    the functional model is about mathematics, not about C programming. *)

(* ================================================================= *)
(** ** API spec for the sumarray.c program *)

(** The Application Programmer Interface (API) of a C program is expressed
   in its header file: function prototypes and data-structure definitions that
   explain how to call upon the modules' functionality. In Verifiable C, an
   _API specification_ is written as a series of _function specifications_
   ([funspec]s) corresponding to the function prototypes. *)

Definition sumarray_spec : ident * funspec :=
DECLARE _sumarray
 WITH a: val, sh : share, contents : list Z, size: Z
 PRE [ tptr tuint, tint ]
  PROP  (readable_share sh; 0 <= size <= Int.max_signed;
         Forall (fun x => 0 <= x <= Int.max_unsigned) contents)
  PARAMS (a; Vint (Int.repr size))
  SEP   (data_at sh (tarray tuint size) (map Vint (map Int.repr contents)) a)
 POST [ tuint ]
  PROP () RETURN (Vint (Int.repr (sum_Z contents)))
  SEP (data_at sh (tarray tuint size) (map Vint (map Int.repr contents)) a).

(** This [DECLARE] statement has type [ident*funspec].  That is,
 it associates the name of a function (the identifier [_sumarray]) with
 a function-specification.  The identifier [_sumarray] comes directly
 from the C program, as parsed by [clightgen].  If you are curious,
 you can look in [sumarray.v]  (the output of [clightgen]) for
 [Definition _sumarray := ...].  Later in [sumarray.v], you can see 
 [Definition f_sumarray] that is the C-language function body (represented
 as a syntax tree).

  A function is specified by its _precondition_ and its
  _postcondition_.  The [WITH] clause quantifies over Coq values that
  may appear in both the precondition and the postcondition. The
  precondition has access to the function parameters
  (in this case [a] and [size]) and the postcondition has access
  to the return value [(sum_Z contents)].

  Function preconditions, postconditions, and loop invariants are
  _assertions_ about the state of variables and memory at a particular
  program point.  In an assertion [PROP(P) LOCAL(Q) SEP(R)], the
  propositions in the sequence [P] are all of Coq type [Prop].  They
  describe things that are true independent of program state.  In the
  precondition above, the statement [0 <= size <= Int.max_signed] is
  true _just within the scope of the quantification of the variable_
  [size]; that variable is bound by [WITH], and spans the [PRE] and
  [POST] assertions.

  The [LOCAL] clause, describing what's in C local variables,
  takes different forms depending on context:
  - In a function-precondition, we write PROP/PARAMS/SEP, that is,
    the [PARAMS] lists the values of C function parameters (in order).
  - In a function-postcondition, we write [RETURN(v)] to indicate
    the return value of the function.
  - Within a function body (in assertions and invariants) we write
    [LOCAL] to describe the values of local variables (including parameters).

  Whether it is PARAMS or RETURN or LOCAL, we are talking about the
  _values_ contained in parameters or local variables.
  In general, a C scalar variable holds something of type [val]; this
  type is defined by CompCert as, *)
Print val.
(*
 Inductive val: Type :=
 | Vundef: val
 | Vint: int -> val
 | Vlong: int64 -> val
 | Vfloat: float -> val
 | Vsingle: float32 -> val
 | Vptr: block -> ptrofs -> val. *)

(** In an assertion [PROP(P) LOCAL(Q) SEP(R)], the [SEP] conjuncts [R] are
  _spatial assertions_ in separation logic.  In our example precondition,
  there's just one SEP conjunct, a [data_at] assertion saying
  that at address [a] in memory, there is a data structure of type

  array[size] of unsigned int;

  with access-permission [sh], and the contents of that array is the
  sequence [map Vint (map Int.repr contents)].

  The postcondition is introduced by [POST [ tuint ]], indicating that
  this function returns a value of type [unsigned int]. There are no
  [PROP] statements in this postcondition--no forever-true facts hold
  now, that weren't already true on entry to the function.

  [RETURN(v)] gives the return value [v]; [RETURN()] for void functions.

  The postcondition's [SEP] clause mentions all the spatial resources
  from the precondition, minus ones that have been freed
  (deallocated), plus ones that have been malloc'd (allocated).

  So, overall, the specification for [sumarray] is this: "At any call
  to sumarray, there exist values [a, sh, contents, size] such that
  [sh] gives at least read-permission; [size] is representable as a
  nonnegative 32-bit signed integer; function-parameter [_a] contains
  value [a] and [_n] contains the 32-bit representation of [size]; and
  there's an array in memory at address [a] with permission [sh]
  containing [contents].  The function returns a value equal to
  [sum_int(contents)], and leaves the array in memory unaltered."  *)

(* ----------------------------------------------------------------- *)
(** *** Function specification for main() *)

(** The function-spec for [main] has a special form, which we discuss
   below in the section called _Global variables and main_.  In
   particular, its precondition is defined using [main_pre]. *)
Definition main_spec :=
 DECLARE _main
  WITH gv : globals
  PRE  [] main_pre prog tt gv
  POST [ tint ]  
     PROP() 
     RETURN (Vint (Int.repr (1+2+3+4)))
     SEP(TT).
(** This postcondition says we have indeed added up the global array
   [four]. *)

(* ----------------------------------------------------------------- *)
(** *** Integer overflow

    In Verifiable C's signed integer arithmetic, you must prove (if the
 system cannot prove automatically) that no overflow occurs.  For unsigned
 integers, arithmetic is treated as modulo-2^n (where n is typically 32
 or 64), and overflow is not an issue.  The function [Int.repr: Z -> int]
 truncates mathematical integers into 32-bit integers by taking the
 (sign-extended) low-order 32 bits.  [Int.signed: int -> Z] injects back
 into the signed integers.

 The [sumarray] program uses unsigned arithmetic for [s] and the
 array contents; it uses signed arithmetic for [i].

 The postcondition guarantees that the value returned is
 [Int.repr (sum_Z contents)].  But what if the sum of all the [s]
 is larger than 2^32, so the sum doesn't fit in a 32-bit signed integer?
 Then [Int.unsigned(Int.repr (sum_Z contents)) <> sum_Z contents].
 In general, for a claim about [Int.repr(x)] to be _useful_ one also
 needs to know that [0 <= x <= Int.max_unsigned] or
 [Int.min_signed <= x <= Int.max_signed].
 The caller of [sumarray] will probably need to prove
 [0 <= sum_Z contents <= Int.max_unsigned]
 in order to make much use of the postcondition. *)

(* ================================================================= *)
(** ** Packaging the Gprog and Vprog *)

(** SEE ALSO: VC.pdf Chapter 8 (_Proof of the sumarray program_) *)

(** To prove the correctness of a whole program,
  - 1. Collect the function-API specs together into [Gprog].
  - 2. Prove that each function satisfies its own API spec
    (with a [semax_body] proof).
  - 3. Tie everything together with a [semax_func] proof.

The first step is easy: *)

(* Packaging the API specs all together. *)
Definition Gprog := [sumarray_spec; main_spec].

(** What's in [Gprog] are the funspecs that we built using [DECLARE].
  (In multi-module programs we would also include imported funspecs.)

 In addition to [Gprog], the API spec contains [Vprog], the list of
 global-variable type-specs.  This was computed automatically by the
 [mk_varspecs] tactic, in the "boilerplate" code above. *)

Print Vprog.
(*   = [(_four, tarray tuint 4)]  : varspecs *)
Print varspecs.
(*   = list (ident * type) *)

(** That is, for each C language global variable, [Vprog] gives its
  name and its C-language type. *)

(* ================================================================= *)
(** ** Proof of the sumarray program *)

(** Now comes the proof that [f_sumarray], the body of the [sumarray()]
   function, satisfies [sumarray_spec], in global context [(Vprog,Gprog)]. *)
Lemma body_sumarray: semax_body Vprog Gprog f_sumarray sumarray_spec.

(** Here, [f_sumarray] is the actual function body (AST of the C code)
  as parsed by [clightgen]; you can read it in [sumarray.v].
  You can read [body_sumarray] as claiming: In the context of [Vprog] and
  [Gprog], the function body [f_sumarray] satisfies its specification
  [sumarray_spec].  We need the context in case the sumarray function
  refers to a global variable ([Vprog] provides the variable's type)
  or calls a global function  ([Gprog] provides the function's API spec). *)

(** Now, the proof of [body_sumarray]. *)

Proof.

(** If you are reading this as a static document, you should consider
 switching to your favorite Coq development environment, in which you 
 can step through the rest of this chapter, tactic by tactic, and examine
 the proof state at each point. *)

(* ----------------------------------------------------------------- *)
(** *** start_function *)

(** SEE ALSO: VC.pdf Chapter 9 (_start_function_)

 The predicate [semax_body] states the Hoare triple of the function body,
 [Delta |- {Pre} c {Post}], where [Pre] and [Post] are taken from the
 [funspec], [c] is the body of the function, and the type-context [Delta]
 is calculated from the global type-context overlaid with the parameter-
 and local-types of the function.

 To prove this, we begin with the tactic [start_function],  which takes care
 of some simple bookkeeping and expresses the Hoare triple to be proved. *)

start_function. (* Always do this at the beginning of a semax_body proof *)

(** Some of the assumptions you now see above the line are,
  - [a, sh, contents, size], taken directly from the WITH clause
       of [sumarray_spec];
  - [Delta_specs], the context in which Floyd's proof tactics will look up
       the specifications of global functions;
  - [Delta], the context in which Floyd will look up the types of
       local and global variables;
  - [SH,H,H0], taken exactly from the [PROP] clauses of [sumarray_spec]'s
       precondition.
  There are also two _abbreviations_ above the line,
  [POSTCONDITION] and [MORE_COMMANDS], discussed below. *)

(* ----------------------------------------------------------------- *)
(** *** Forward symbolic execution *)

(** SEE ALSO: VC.pdf Chapter 10 (_forward_).

  We do Hoare logic proof by forward symbolic execution.  At the beginning 
  of this function body, our proof goal is a Hoare triple about the statement
  [(i=0; ...more commands...)]. In a forward Hoare logic proof of 
  [{P}(i=0;...more...){R}] we might first apply the sequence rule,

    {P}(i=0;){Q}  {Q}(...more...){R}
    ---------------------------------
    {P}(i=0;...more...){R}

assuming we could derive some appropriate assertion [Q].
For many kinds of statements (assignments, return, break,
continue) [Q] is derived automatically by the [forward] tactic,
which applies a strongest-postcondition style of proof rule.
Let us now apply the [forward] tactic: *)

forward.  (* i = 0; *)

(** Look at the precondition of the current proof goal, that is, the
  second argument of [semax]; it has the form [PROP(...) LOCAL(...)
  SEP(...)].  That precondition is also the _postcondition_ of [i=0;].
  It's much like the _precondition_ of [i=0;] except for one change:
  we now know that [i] is equal to [0], which is expressed in the
  [LOCAL] part as [temp _i (Vint (Int.repr 0))]. *)

Check 0.  (* : Z,   the mathematical integer zero. *)
Check (Int.repr 0).  (* : int,   the 32-bit integer representing 0. *)
Check (Vint (Int.repr 0)).  (* : val,   the type of CompCert values *)
Check (temp _i (Vint (Int.repr 0))).  (* : localdef,  the type of LOCAL assertions *)

(* ----------------------------------------------------------------- *)
(** *** abbreviate, MORE_COMMANDS, POSTCONDITION

     When doing forward symbolic execution (forward Floyd/Hoare proof)
  through a large function, you don't usually want to see the entire
  function-body in your proof subgoal.  Therefore the system abbreviates
  some things for you, using the magic of Coq's implicit arguments. *)

Check @abbreviate.
(*   : forall A : Type, A -> A *)
About abbreviate.
(*   Arguments A, x are implicit and maximally inserted  . . . *)

(** We see here that [abbreviate] is just the identity function,
   with _both_ of its arguments implicit! *)

(** To examine the actual contents of MORE_COMMANDS, just do this: *)

unfold abbreviate in MORE_COMMANDS.

(** or alternately, *)
subst MORE_COMMANDS; unfold abbreviate.

(** Similarly, to see the POSTCONDITION, just do, *)

unfold abbreviate in POSTCONDITION.

(* ----------------------------------------------------------------- *)
(** *** Hint

    In any VST proof state, the [hint] tactic will print a suggestion
  (if it can) that will help you make progress in the proof.
  In stepping through the case study in this chapter,
  insert [hint] at any point to see what it says. *)

hint.
(** Then delete the hints!  (They slow down replay of your proof.) *)

(** The hint here suggests using [abbreviate_semax], which will undo
  the [unfold abbreviate] that we did above.  Really this is optional;
  if we don't do [abbreviate_semax], the next [forward] tactic will
  do it for us. *)

abbreviate_semax.
hint.
(** This time, the hint suggests that we try 'forward'. *)

(* ----------------------------------------------------------------- *)
(** *** Forward through another assignment statement. *)
forward.  (* s = 0; *)

(** The [forward] tactic works on assignment statements, break,
   continue, and return. *)

(* ----------------------------------------------------------------- *)
(** *** While loops, forward_while *)

(** SEE ALSO: VC.pdf Chapter 12 (_if, while, for_) and Chapter 13 (_while loops_).

   To do symbolic execution through a [while] loop, use the
   [forward_while] tactic; you must supply a loop invariant. *)
forward_while
 (EX i: Z,
   PROP  (0 <= i <= size)
   LOCAL (temp _a a;
          temp _i (Vint (Int.repr i));
          temp _n (Vint (Int.repr size));
          temp _s (Vint (Int.repr (sum_Z (sublist 0 i contents)))))
   SEP   (data_at sh (tarray tuint size) (map Vint (map Int.repr contents)) a)).

(** A loop invariant is an assertion, almost always in the form
  of an existential quantifier,  [EX...PROP(...)LOCAL(...)SEP(...)].
  Each iteration of the loop has a state characterized by
  a different value of some iteration variable(s),
  the [EX] binds that value.

  [forward_while] leaves four subgoals; here we label them
   with the - bullet. *)
- hint.
(** The first subgoal is to prove
  that the current assertion (precondition) entails the loop invariant. *)

(* ----------------------------------------------------------------- *)
(** *** Proving separation-logic entailments *)

(** SEE ALSO: VC.pdf Chapter 14 (_PROP LOCAL SEP_) and Chapter
     15 (_Entailments_)

  This proof goal is an _entailment_,  [ENTAIL Delta, P |-- Q],  meaning 
  "in context [Delta], any state that satisfies [P] will also satisfy [Q]."

  In this case, the right-hand-side of this entailment is existentially
  quantified; it says: there exists a value [i] such that (among other things)
  [temp _i (Vint (Int.repr i))], that is, the C variable [_i] contains the
  value [i].  But the left-hand-side of the entailment says 
  [temp _i (Vint (Int.repr 0))], that is, the C variable [_i] contains 0.

  This is analogous to the following situation: *)

Set Nested Proofs Allowed.
Goal forall (f: Z->Z) (x: Z), f(x)=0 -> exists i:Z, f(x)=i.
  intros.

(** To prove such a goal, one uses Coq's "exists" tactic to
 demonstrate a value for [i]: *)
  exists 0.
  auto.
Qed.

(** In a separation logic entailment, one can prove an [EX] on the
  right-hand side by using the [Exists] tactic to demonstrate a value
  for the quantified variable: *)
  Exists 0.   (* Instantiate the existential on the right-side of |--   *)

(** Notice that [i] has now been replace with [0] on the right side.

   To prove entailments, we usually use the [entailer!] tactic to
   simplify the entailment as much as possible--or in many cases,
   to prove it entirely. *)

  entailer!.

(** In this case, it solves entirely; in other cases, entailer!
    leaves subgoals for you to prove. *)

(* ----------------------------------------------------------------- *)
(** *** Type-checking the loop test *)
- hint.
(** The second subgoal of [forward_while] is always to prove that the
  loop-test expression can evaluate without crashing--that is,
  all the variables it references exist and are initialized,
  it doesn't divide by zero, et cetera.

  We call this a "type-checking condition", the predicate [tc_expr].
  In this case, it's the while-loop test [i<n] that must execute,
  so we see [tc_expr Delta (! (_i < _n))] on the right-hand side
  of the entailment.

  Very often, these [tc_expr] goals solve automatically by [entailer!]. *)
  entailer!.

  (** and indeed, this subgoal is solved. *)

(* ----------------------------------------------------------------- *)
(** *** Proving that the loop body preserves the loop invariant *)
- hint.
(** The third subgoal of [forward_while] is to prove
    that the loop body preserves the loop invariant.
   We must forward-symbolic-execute through the loop body. *)

(** SEE ALSO: VC.pdf Chapter 16 (_Array subscripts_) *)

(** Examine the proof goal at the beginning of the loop body.  Above the
    line is the variable [i], introduced automatically by [forward_while]
    from the existential [EX i:Z] in the loop invariant.

    The first C command in the loop body is the array subscript,
    [ _x = a[_i]; ].   In order to prove this statement, the [forward]
    tactic needs to be able to prove that [i] is within bounds of the
    array.  When we try [forward], it fails: *)

Fail forward. (* x = a[i]

    [forward] fails and tells us to first make [0 <= i < Zlength contents]
   provable.  This auxiliary fact will help it prove that the array
   subscript [i] is within the bounds of the array [a].  It asks us to
   assert and prove some fact strong enough to imply this.

   Above the line we have [0<=i] and [i<size], so if we could prove
   [Zlength contents = size] that would be enough.  Unfortunately,
   it won't work to do  [assert (Zlength contents = size)]  because
   there is not enough information above the line to prove that. *)

(** SEE ALSO: VST.pdf, Chapter "assert_PROP"

   The required information to prove [Zlength contents = size] comes from
   the _precondition_ of the current [semax] goal. In the precondition, we have

   data_at sh (tarray tuint size) (map Vint (map Int.repr contents)) a

   The [data_at] predicate always enforces that the  "contents" list for
   an array is exactly the same length as the size of the array.

   To make use of precondition facts in an assertion, use [assert_PROP]. *)

assert_PROP (Zlength contents = size). {

(** The proof goal is an entailment, with the current precondition on
    the left, and the proposition to be proved on the right.
    As usual, to prove an entailment, we use the [entailer!] tactic
    to simplify the proof goal: *)

  entailer!.
(** Indeed, [entailer!] has done almost all the work.  If you want
   to see how [entailer!] did it, undo the last step and use these
   two tactics:  [go_lower.  saturate_local.]
   The job of [go_lower] is to process the PROP and LOCAL parts of
   the entailment; and [saturate_local] derives all the propositional
   facts derivable from the [mpred]s on the left-hand-side, and puts
   those facts above the line.  In this case, above the line is,
   [Zlength (unfold_reptype (map Vint (map Int.repr contents))) = size]
   which is the fact we need. *)
  hint.
(** The [hint] suggests that [list_solve] solves this goal,
   [Zlength contents = Zlength (map Vint (map Int.repr contents))].
   Indeed, [list_solve] knows a lot of things about the interaction
   of list operators: [Zlength, map, sublist,] etc.

   Or, we can solve the goal "by hand": *)
  do 2 rewrite Zlength_map. reflexivity.
}
hint.

 (** Now that we have [Zlength contents = size] above the, we can go
   [forward] through the array-subscript statement. *)
forward. (* [x = a[i];] *)

(** Now [forward] through the rest of the loop body. *)
forward. (* s += x; *)
forward. (* i++; *)

(** SEE ALSO: VC.pdf Chapter 17 (_At the end of the loop body_) *)

(** We have reached the end of the loop body, and it's
   time to prove that the _current precondition_  (which is the
   postcondition of the loop body) entails the loop invariant. *)
 Exists (i+1).
 entailer!.
 f_equal. f_equal.

(** Here the proof goal is,

   sum_Z (sublist 0 (i + 1) contents) =
   sum_Z (sublist 0 i contents) + Znth i contents

   We will prove this in stages:

   sum_Z (sublist 0 (i + 1) contents) =
   sum_Z (sublist 0 i contents ++ sublist i (i+1) contents) =
   sum_Z (sublist 0 i contents) + sum_Z (sublist i (i+1) contents) =
   sum_Z (sublist 0 i contents) + sum_Z (Znth i contents :: nil) =
   sum_Z (sublist 0 i contents) + Znth i contents
*)
 rewrite (sublist_split 0 i (i+1)) by lia.
 rewrite sum_Z_app. rewrite (sublist_one i) by lia.
 simpl. lia. 
(** After the loop, our precondition is the conjunction of the loop 
    invariant and the negation of the loop test.  *)

(** SEE ALSO: VC.pdf Chapter 18 (_Returning from a function_) *)

- hint.

(** You can always go [forward] through a [return] statement.
  The resulting proof goal is an entailment, that the current
  precondition implies the function's postcondition. *)

forward.  (* return s; *)

(** Here we prove that the postcondition of the function body
    entails the postcondition demanded by the function specification. *)
entailer!.
hint.
autorewrite with sublist in *|-.
hint.
autorewrite with sublist.
hint.
reflexivity.
Qed.

(* ================================================================= *)
(** ** Global variables and main() *)

(** SEE ALSO: VC.pdf Chapter 19 (_Global variables and main_) *)
(* Contents of the extern global initialized array "_four" *)
Definition four_contents := [1; 2; 3; 4].

Lemma body_main:  semax_body Vprog Gprog f_main main_spec.
Proof.
  start_function.

(** C programs may have extern global variables, either with
  explicit initializers or implicitly initialized to zero.
  Because they live in memory, they need to be described by a
  separation logic predicate, a "resource" that gets passed from
  one function to another via the SEP part of funspec preconditions
  and postconditions.  Initially, all the global-variable resources
  are passed into the [main] function, as its precondition.  The
  built-in operator [main_pre] calculates this precondition of [main]
  by examining all the global declarations of the program.

  In this program, there is one global variable,

    unsigned four[4] = {1,2,3,4};

  and we can see its SEP assertion in the precondition of the
  current proof goal:

   data_at Ews (tarray tuint 4)
           (map Vint [Int.repr 1; Int.repr 2; Int.repr 3; Int.repr 4])
           (gv _four)
*)

(** SEE ALSO: VC.pdf Chapter 20 (_Function calls_)

  We are ready to prove the function-call, [s = sumarray(four,4);]
  We use the [forward_call] tactic, and for the argument we must supply
  a tuple of values that instantiates the WITH clause of the called
  function's funspec.  In [DECLARE _sumarray], the [WITH] clause reads,
  [WITH a: val, sh : share, contents : list Z, size: Z].
  Therefore the argument to [forward_call] must be a four-tuple of type,
  [(val * share * list Z * Z)].  *)
forward_call (*  s = sumarray(four,4); *)
  (gv _four, Ews, four_contents, 4).

(** The subgoal of [forward_call] is that we have to prove the PROP
  part of the [sumarray] function's precondition. *)

 split3. auto. computable. repeat constructor; computable.

(** Now we are after the function-call, and we can go forward through
  the return statement. *)
forward. (* return s; *)
Qed.

(* ================================================================= *)
(** ** Tying all the functions together *)

(** SEE ALSO: VC.pdf Chapter 21 (_Tying all the functions together_)

  The C program may do input/output, affecting the state of the
  outside world.  This state is described (abstractly) by the [Espec],
  the "external specification."  The sumarray program does not do
  any input/output, so we can use a trivial [Espec].  We provide this to
  the [semax_prog] proofs (below, in the [prog_correct] lemma) as follows: *)

Existing Instance NullExtension.Espec.
(** This is a _typeclass instance_.  If you're not familiar with typeclasses,
  don't worry, just treat this as "boilerplate" that you can ignore. *)

(** An entire C program is proved correct if all the functions
  satisfy their funspecs.  We listed all those functions (upon whose
  specifications we depend) in the [Gprog] definition.  The judgment
  [semax_prog prog Vprog Gprog] says, "In the program [prog], whose
  [varspecs] are [Vprog] and whose funspecs are [Gprog], every
  function mentioned in [Gprog] does satisfy its specification." *)

Lemma prog_correct: semax_prog prog tt Vprog Gprog.
Proof.
prove_semax_prog.

semax_func_cons body_sumarray.
semax_func_cons body_main.
Qed.

(* ================================================================= *)
(** ** Additional recommended reading *)

(** Recommended: read VC.pdf Chapters 22-47 (up to _Pointer comparisons_) *)

(* 2020-09-18 15:39 *)
