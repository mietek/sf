(** * Verif_stack: Stack ADT implemented by linked lists *)

(** Here is a little C program, [stack.c]

    #include <stddef.h>

    extern void * malloc (size_t n);
    extern void free (void *p);
    extern void exit(int n);

    struct cons {
      int value;
      struct cons *next;
    };

    struct stack {
      struct cons *top;
    };

    struct stack *newstack(void) {
      struct stack *p;
      p = (struct stack * ) malloc (sizeof (struct stack));
      if (!p) exit(1);
      p->top = NULL;
      return p;
    }

    void push (struct stack *p, int i) {
      struct cons *q;
      q = (struct cons * ) malloc (sizeof (struct cons));
      if (!q) exit(1);
      q->value = i;
      q->next = p->top;
      p->top = q;
    }

    int pop (struct stack *p) {
      struct cons *q;
      int i;
      q = p->top;
      p->top = q->next;
      i = q->value;
      free(q);
      return i;
    }

 This program implements a stack ADT (abstract data type).
 - To create a new stack, [st = newstack();]
 - To push integer [i] onto the stack, [push(st,i);]
 - To pop from the stack, [i=pop(st);]

 This stack is implemented as a header node ([struct stack])
 pointing to a linked list of cons cells ([struct cons]). *)

(* ================================================================= *)
(** ** Let's verify! *)

Require VC.Preface. (* Check for the right version of VST *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VC.stack.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.
Require Import VC.hints.  (* Import special hints for this tutorial. *)

(* ================================================================= *)
(** ** Malloc and free *)

(** When you use C's malloc/free library, you write [p=malloc(n);]
  to get a pointer [p] to a block of [n] bytes; when you're done
  with that block, you call [free(p)] to dispose of it.
  How does the [free] function know how many bytes to dispose?

  The answer is, the malloc/free library puts an extra "header"
  field just before address [p], so really you get this:

      +-----------+
      | header    |
      +-----------+
  p-->|  zero     |
      +-----------+
      |  one      |
      +-----------+
      |  two      |
      +-----------+

  where in this case, [header=3].

  In separation logic, we can describe this as 
  - [malloc_token Ews p * data_at Ews (Tstruct _mystruct noattr) (zero,one,two) p]
  where [malloc_token Ews p] describes this picture:

      +-----------+
      | header    |
      +-----------+
  p-->

  Of course, the malloc/free library might have a different way
  of "remembering" the size that [p] points to, so its representation
  of [malloc_token] is _not necessarily_ a word at offset -1.
  Therefore, clients of the malloc/free library treat [malloc_token]
  as an abstract predicate.  Now, the function-specifications of malloc 
  and free are something like this: *)

Definition malloc_spec_example  :=
 DECLARE _malloc
 WITH t:type
 PRE [ tuint ]
    PROP (0 <= sizeof t <= Int.max_unsigned;
          complete_legal_cosu_type t = true;
          natural_aligned natural_alignment t = true)
    PARAMS (Vint (Int.repr (sizeof t)))
    SEP ()
 POST [ tptr tvoid ] EX p:_,
    PROP ()
    RETURN (p)
    SEP (if eq_dec p nullval then emp
         else (malloc_token Ews t p * data_at_ Ews t p)).

Definition free_spec_example :=
 DECLARE _free
 WITH t: type, p:val
 PRE [ tptr tvoid ]
     PROP ()
     PARAMS (p)
     SEP (malloc_token Ews t p; data_at_ Ews t p)
 POST [ Tvoid ]
     PROP () RETURN () SEP ().

(** If your source program says [malloc(sizeof(t))], your [forward_call] 
    should supply (as a WITH-witness) the C type [t].
    Malloc may choose to return NULL, in which case the SEP part
    of the postcondition is [emp], or it may return a pointer,
    in which case you get [data_at_ Ews t p], and as a free bonus
    you get a [malloc_token Ews t p].  But don't lose that [malloc_token]!
    You will need to supply it later to the [free] function when
    you dispose of the object.

    The SEP predicate [data_at_ Ews t p] is an _uninitialized_
    structure of type [t].  It is equivalent to,
    [data_at Ews t (default_val t) p].  The [default_val] is basically
    a struct or array full of [Vundef] values. *)

(* ================================================================= *)
(** ** Specification of linked lists

    This is much like the linked lists in [Verif_reverse]. *)

Fixpoint listrep (il: list Z) (p: val) : mpred :=
 match il with
 | i::il' => EX y: val, 
        malloc_token Ews (Tstruct _cons noattr) p *
        data_at Ews (Tstruct _cons noattr) (Vint (Int.repr i),y) p *
	listrep il' y
 | nil => !! (p = nullval) && emp
 end.

(** Proof automation for user-defined separation predicates works better
  if you disable automatic simplification, as follows: *)
Arguments listrep il p : simpl never.

(** As usual, we should populate the Hint databases
    [saturate_local] and [valid_pointer] *)

(** **** Exercise: 1 star, standard (stack_listrep_properties) *)
Lemma listrep_local_prop: forall il p, listrep il p |--
        !! (is_pointer_or_null p  /\ (p=nullval <-> il=nil)).
(** See if you can remember how to prove this; or look again
  at [Verif_reverse] to see how it's done. *)
(* FILL IN HERE *) Admitted.
Hint Resolve listrep_local_prop : saturate_local.

Lemma listrep_valid_pointer:
  forall il p,
   listrep il p |-- valid_pointer p.
(** See if you can remember how to prove this; or look again
  at [Verif_reverse] to see how it's done. *)
(* FILL IN HERE *) Admitted.
Hint Resolve listrep_valid_pointer : valid_pointer.
(** [] *)

(* ================================================================= *)
(** ** Specification of stack data structure *)

(** Our stack data structure looks like this:

      +-----------+
      | token     |
      +-----------+       +---------
  p-->|  top------+---q-->| linked list...
      +-----------+       +---------

 The stack object [p] points to a header node with one field [top]
 (plus a malloc token); the _contents_ of the [top] field
 is some pointer [q] that points to a linked list. *)

Definition stack (il: list Z) (p: val) :=
 EX q: val,
  malloc_token Ews (Tstruct _stack noattr) p * 
  data_at Ews (Tstruct _stack noattr) q p *
  listrep il q.

Arguments stack il p : simpl never.
(** **** Exercise: 1 star, standard (stack_properties) *)

Lemma stack_local_prop: forall il p, stack il p |--  !! (isptr p).
(* FILL IN HERE *) Admitted.
Hint Resolve stack_local_prop : saturate_local.

Lemma stack_valid_pointer:
  forall il p,
   stack il p |-- valid_pointer p.
(* FILL IN HERE *) Admitted.
Hint Resolve stack_valid_pointer : valid_pointer.
(** [] *)

(* ================================================================= *)
(** ** Function specifications for the stack operations *)

Definition newstack_spec : ident * funspec :=
 DECLARE _newstack
 WITH gv: globals
 PRE [ ] 
    PROP () PARAMS() GLOBALS(gv) SEP (mem_mgr gv)
 POST [ tptr (Tstruct _stack noattr) ] 
    EX p: val, PROP ( ) RETURN (p) SEP (stack nil p; mem_mgr gv).

Definition push_spec : ident * funspec :=
 DECLARE _push
 WITH p: val, i: Z, il: list Z, gv: globals
 PRE [ tptr (Tstruct _stack noattr), tint ] 
    PROP (Int.min_signed <= i <= Int.max_signed) 
    PARAMS (p; Vint (Int.repr i)) GLOBALS(gv) 
    SEP (stack il p; mem_mgr gv)
 POST [ tvoid ] 
    PROP ( ) RETURN () SEP (stack (i::il) p; mem_mgr gv).

Definition pop_spec : ident * funspec :=
 DECLARE _pop
 WITH p: val, i: Z, il: list Z, gv: globals
 PRE [ tptr (Tstruct _stack noattr) ] 
    PROP () 
    PARAMS (p) GLOBALS(gv) 
    SEP (stack (i::il) p; mem_mgr gv)
 POST [ tint ] 
    PROP ( ) RETURN (Vint (Int.repr i)) SEP (stack il p; mem_mgr gv).

(** Putting all the funspecs together: *)

Definition Gprog : funspecs :=
        ltac:(with_library prog [
                   newstack_spec; push_spec; pop_spec
 ]).

(* ================================================================= *)
(** ** Proofs of the function bodies *)

(** An _Abstract Data Type_ (ADT) is a type provided with a 
  _representation_ and a set of _operations_.  Clients of the ADT
  never see the representation, they only call upon the operations.
  Implementations of the operations do need to manipulate the 
  representation directly.

  In this case, [stack] is our ADT.  The operations are [newstack],
  [push], and [pop].  Clients of these operations see only
  [stack il p], where [il] is the list of values that the client
  has pushed onto the stack, and [p] is the client's "handle",
  the address of the representation of the stack.  The client does
  not know whether the abstract list [il] is represented in C 
  data structures by a singly linked list, a doubly linked list,
  an array, or some other data structure.  The client _never unfolds_
  the Definition [stack].

  The operations [newstack, push, pop] are implemented in C,
  and they directly manipulate (in this case) a singly linked list.
  In proving the correctness of [newstack, push, pop], we need to
  know the representation.  Therefore,

  Hint:  At the beginning of [body_pop], of [body_push], and of
  [body_newstack], the first thing you should do is
  [unfold stack in *]. *)

(** **** Exercise: 2 stars, standard (body_pop) *)
Lemma body_pop: semax_body Vprog Gprog f_pop pop_spec.
Proof.
start_function.
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard (body_push) *)
Lemma body_push: semax_body Vprog Gprog f_push push_spec.
Proof.
start_function.
forward_call (Tstruct _cons noattr, gv).
simpl; split3; auto.
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard (body_newstack) *)
Lemma body_newstack: semax_body Vprog Gprog f_newstack newstack_spec.
Proof.
start_function.
(* FILL IN HERE *) Admitted.
(** [] *)

(* 2020-09-18 15:39 *)
