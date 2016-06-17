(** * Postscript *)


(** Congratulations: You've made it to the end! *)

(** * Looking Back... *)

(** We've covered a lot of ground.  The topics might be summarized like this:

   - _Functional programming_:
          - "declarative" programming style (recursion over persistent
            data structures, rather than looping over mutable arrays
            or pointer structures)
          - higher-order functions
          - polymorphism *)

(**
     - _Logic_, the mathematical basis for software engineering:

               logic                        calculus
        --------------------   =   ----------------------------
        software engineering       mechanical/civil engineering


          - inductively defined sets and relations
          - inductive proofs
          - proof objects *)

(**
     - _Coq_, an industrial-strength proof assistant
          - functional core language
          - core tactics
          - automation
*)

(**
     - _Foundations of programming languages_

           - notations and definitional techniques for precisely specifying
                - abstract syntax
                - operational semantics
                    - big-step style
                    - small-step style
                - type systems

           - program equivalence

           - Hoare logic

           - fundamental metatheory of type systems

              - progress and preservation

           - theory of subtyping
*)

(* ###################################################################### *)
(** * Looking Forward... *)

(** Some good places to go for more...

       - This book includes several optional chapters covering topics
         that you may find useful.  If you've been using it in the
         context of a course, take a look at the table of contents
         and the chapter dependency diagram.

       - Cutting-edge conferences on programming languages and formal
         verification:
            - POPL
            - PLDI
            - OOPSLA
            - ICFP
            - CAV
            - (and many others)

       - More on functional programming
            - Learn You a Haskell for Great Good, by Miran
              Lipovaca [Lipovaca 2011].
            - and many other texts on Haskell, OCaml, Scheme, Scala,
              ...

       - More on Hoare logic and program verification
            - The Formal Semantics of Programming Languages: An
              Introduction, by Glynn Winskel [Winskel 1993].
            - Many practical verification tools, e.g. Microsoft's
              Boogie system, Java Extended Static Checking, etc.

       - More on the foundations of programming languages:
            - Types and Programming Languages, by Benjamin
              C. Pierce [Pierce 2002].
            - Practical Foundations for Programming Languages, by
              Robert Harper [Harper 2016].
            - Foundations for Programming Languages, by John
              C. Mitchell [Mitchell 1996].

       - More on Coq:
           - Certified Programming with Dependent Types, by Adam
             Chlipala [Chlipala 2013].
           - Interactive Theorem Proving and Program Development:
             Coq'Art: The Calculus of Inductive Constructions, by Yves
             Bertot and Pierre Casteran [Bertot 2004].
           - Iron Lambda (http://iron.ouroborus.net/) is a collection
             of ​Coq formalisations for functional languages of
             increasing complexity. It fills part of the gap between
             the end of the​ Software Foundations course and what
             appears in current research papers.  The collection has
             at least Progress and Preservation theorems for a number
             of variants of STLC and the polymorphic
             lambda-calculus (System F). *)

(* $Date: 2016-05-26 17:51:14 -0400 (Thu, 26 May 2016) $ *)
