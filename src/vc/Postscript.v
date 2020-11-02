(** * Postscript: Postcript and bibliography *)

(* ################################################################# *)
(** * Looking back *)

(** You've now seen how to verify programs that use many of C's data
  structures (arrays, pointers, structs, integers) and control
  structures (functions, if-then-else, loops), and abstraction 
  structures (data abstraction, module interfaces).  The final exercise
  (hash tables) demonstrated all of these at once, in addition to a
  key concept: layering the proof using a functional model,
  so that proofs about the properties of the functional model ([Hashfun])
  cleanly separate from the implementation proof ([Verif_hash]) showing
  that the C program refines the functional model. *)

(* ################################################################# *)
(** * Looking forward *)

(** If you want to verify some C programs on your own, you may take
 inspiration from some of these Verifiable C proofs:
 - SHA-2 cryptographic hashing [Appel 2015] (in Bib.v)
 - HMAC cryptographic authentication [Beringer 2015] (in Bib.v)
 - HMAC-DRBG cryptographic random number generation [Ye 2017] (in Bib.v)
 - Concurrent messaging system [Mansky 2017] (in Bib.v)
 - Generational copying garbage collector [Wang 2019] (in Bib.v)
 - Bins-based malloc/free system [Appel and Naumann 2020] (in Bib.v)
 - AES encryption, B+Trees, Tries of B+ trees (unpublished 
        master's or undergraduate theses). *)

(* ================================================================= *)
(** ** Small examples

    VST is distributed with a [progs] directory of many small C programs
  that demonstrate different features and methods of Verifiable C.
  If your VST installation is in the standard place, you can find this
  as a subdirectory of [`coqc -where`/user-contrib/VST]. *)

(* ================================================================= *)
(** ** Modules

    All the verifications in this volume are single-file C programs.  Real 
  software engineering in C is done with modules in .c files and interfaces
  in .h files.  Since 2019, VST has a module system; the early version
  is described in [Beringer 2019] (in Bib.v) and the newer version is demonstrated 
  in progs/VSUpile.  The description in [Beringer 2019] (in Bib.v) mostly matches
  the proofs in progs/VSUpile, but the proofs handle data abstraction in a more
  advanced way than is described in the paper. *)

(* ================================================================= *)
(** ** Input/output

     To prove I/O using our Verifiable C logic, we treat the state of the
  outside world as a resource in the SEP clause, alongside (but separating from) 
  in-memory conjuncts.  Proved examples are in [progs/io.c, progs/io_mem.c],
  and their proof files [progs/verif_io.v, progs/verif_io_mem.v].  Research
  papers describing these concepts include [Koh 2020] (in Bib.v) and
  [Mansky 2020] (in Bib.v). *)

(* ################################################################# *)
(** * Looking around *)

(** VST is not the only program verification system.  How should you decide
  which system to use? *)

(* ================================================================= *)
(** ** Static analyzers

    There are many _static analyzers_ -- too numerous to list here -- that
  attempt to check _safety_ of your program:  will it crash?  Will it access
  an array out of bounds, or dereference an uninitialized pointer?  Static
  analyzers can be useful in software engineering, but they have two major 
  limitations:
  - They don't verify _functional correctness_ -- that is, does your program
    produce the right answer, or interact with the right behavior?
  - They are incomplete.  For example, proving that [a[i]] is an in-bounds array
    access requires proving that [0 <= i < N].  Sometimes a static analyzer
    can deduce that from the program flow, but in general it is a functional
    correctness property that may require sophisticated invariants to prove. *)

(* ================================================================= *)
(** ** Functional correctness verifiers -- functional languages

    A good way to write proved-correct software is to program in a pure
  functional program logic, and use higher-order logic to prove correctness.
  For example:
  - Write pure functional programs in Coq, prove them correct in Coq, then
    extract them from Coq to OCaml or Haskell.  See Volume 3 of Software
    Foundations:  Verified Functional Algorithms.
  - In HOL systems (Higher-order Logic) such as Isabelle/HOL, you can do the
    same thing: write functional programs, prove them correct, extract, compile.
  - You can write Haskell programs, compile with [ghc], and import into Coq
    for verification using hs-to-coq [Spector-Zabusky 2018] (in Bib.v).
  - ACL2 is an older system, that uses a first-order logic.  That's less 
    expressive, you don't get polymorphism or quantification, but there
    have been many successful applications of ACL2 in industry. *)

(* ================================================================= *)
(** ** Functional correctness verifiers -- imperative languages *)

(** Functional programming has its limitations: it requires a garbage
  collector,  usually written in an imperative language, and how did you
  prove that correct?  In functional languages it is often harder
  to build (and reason about) low-latency code, or to access low-level
  primitives.  For these and other reasons, some software is still
  written in low-level imperative languages such as C.

  There are verifiers for high-level imperative languages (that
  require a garbage collector).  For example, Dafny [Leino 2010] (in Bib.v)
  is a language and tool for Hoare-logic style verification.
  It's relatively simple to learn and elegant to use.

  ML with mutable references and arrays is also a high-level imperative
  language.  CFML is a system for reasoning about imperative ML
  programs using separation logic in Coq [Chargueraud 2010] (in Bib.v),
  soon to be described in another volume of _Software Foundations_.
  CakeML is a system for proving (and correctly compiling) ML
  programs in HOL [Kumar 2014] (in Bib.v). *)

(* ================================================================= *)
(** ** Functional correctness verifiers -- C *)

(** For the canonical _low-level imperative language_ -- C -- there
  are several systems:
  - Frama-C (https://frama-c.com/)
  - VeriFast [Jacobs 2011] (in Bib.v)
  - VST (the subject of this volume).

  Unlike VST, where (as you have seen) the proof script is separate from
  the program, in both Frama-C and VeriFast you prove the program by inserting
  assertions and invariants into the program. the tools complete the
  verification automatically -- or else, point out which assertions 
  have failed, so you can adjust your assertions and invariants, and try again.

  Each of these three systems has an assertion language, in which you
  express your function specifications, assertions, and invariants.
  - In VST, as you have seen, that language is a separation language
    (PROP/LOCAL/SEP) embedded in Coq, so that the PROP, LOCAL, and SEP
    clauses can all make use of the full expressive power of the Calculus
    of Inductive Constructions (CiC).  You have seen a simple example of
    the expressive power of this approach, where we can use ordinary Coq 
    proofs in [Hashfun], and directly connect them to separation-logic
    proofs in [Verif_hash].
  - Frama-C uses a weaker assertion language, expressed in C syntax.  That's
    a much weaker logic to reason in, and it doesn't directly connect to
    a general-purpose logic (and proof assistant) like Coq.  Also, since
    Frama-C is not a separation logic, it can be difficult to reason about
    data structures.
  - VeriFast uses a capable Dafny-like logic -- even more capable, since
    it is separation logic, not just Hoare logic.  That means you can reason
    about data structures.  There's no artificial limitation to a C-like syntax
    in the assertion language.  Unfortunately, VeriFast's assertion language
    is not connected to a general-purpose logic (and proof assistant); that 
    means you can do refinement proofs (this C program implements that
    functional model),  but it's not so easy to reason about properties of
    your functional models. *)

(* ================================================================= *)
(** ** Foundational soundness *)

(** Formal reasoning about source programs is a good thing -- but once you've
  proved your source program correct, how do you know that is compiled
  correctly?  That is, 
  - the compiler must not have bugs, and
  - the compiler must agree with your verifier on every detail of the
    semantics of the source language.
  Of all the systems described above, only VST and CakeML can make this
  connection end-to-end, with machine-checked proofs. *)

(* ################################################################# *)
(** * Conclusion *)

(** This volume has given you a taste of formal verification for a low-level
  imperative language.  Since C was not designed with verification in mind,
  it has many sharp corners and idiosyncrasies, which the verification tool
  cannot always hide from you.  But C is a _lingua franca_ in which you can
  express a wide variety of programming paradigms, and Verifiable C is
  expressive enough to allow to verify them.  We wish you success in your
  future software verification efforts. *)
  
  
(* 2020-09-18 15:39 *)
