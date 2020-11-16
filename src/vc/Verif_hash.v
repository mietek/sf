(** * Verif_hash: Correctness proof of hash.c *)

(** In this chapter we will prove that the C program, hash.c,
  correctly implements the functional model in hashfun.v.
  That proof, composed with the proof in hashfun.v that the 
  functional model behaves correctly as a key-value map with 
  string keys, demonstrates the correct behavior of hash.c. *)

(** **** The usual boilerplate *)
Require VC.Preface. (* Check for the right version of VST *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import  VC.hash.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.
Require Import VC.hints.  (* Import special hints for this tutorial. *)

(** Now we import some VST libraries that don't come standard with
  VST.floyd.proofauto. *)

Require Import VST.msl.wand_frame.
Require Import VST.msl.iter_sepcon.
Require Import VST.floyd.reassoc_seq.
Require Import VST.floyd.field_at_wand.

(** Now we import the functional model. *)
Require Import VC.Hashfun.

(* ################################################################# *)
(** * Function specifications *)
(* ----------------------------------------------------------------- *)
(** *** Imports from the C string library (see [Verif_strlib]) *)

Definition strcmp_spec :=
 DECLARE _strcmp
  WITH str1 : val, s1 : list byte, str2 : val, s2 : list byte
  PRE [ tptr tschar, tptr tschar ]
    PROP ()
    PARAMS (str1; str2)
    SEP (cstring Ews s1 str1; cstring Ews s2 str2)
  POST [ tint ]
   EX i : int,
    PROP (if Int.eq_dec i Int.zero then s1 = s2 else s1 <> s2)
    RETURN (Vint i)
    SEP (cstring Ews s1 str1; cstring Ews s2 str2).

Definition strcpy_spec :=
 DECLARE _strcpy
  WITH dest : val, n : Z, src : val, s : list byte
  PRE [ tptr tschar, tptr tschar ]
    PROP (Zlength s < n)
    PARAMS (dest; src)
    SEP (data_at_ Ews (tarray tschar n) dest; cstring Ews s src)
  POST [ tptr tschar ]
    PROP ()
    RETURN (dest)
    SEP (cstringn Ews s n dest; cstring Ews s src).

Definition strlen_spec :=
 DECLARE _strlen
  WITH s : list byte, str: val
  PRE [ tptr tschar ]
    PROP ( )
    PARAMS (str)
    SEP (cstring Ews s str)
  POST [ size_t ]
    PROP ()
    RETURN (Vptrofs (Ptrofs.repr (Zlength s)))
    SEP (cstring Ews s str).

(* ----------------------------------------------------------------- *)
(** ***  String functions:  copy, hash *)

Definition copy_string_spec : ident * funspec :=
 DECLARE _copy_string
 WITH s: val, sigma : list byte, gv: globals
 PRE [ tptr tschar ] 
    PROP ()
    PARAMS (s) GLOBALS(gv)
    SEP (cstring Ews sigma s; mem_mgr gv)
 POST [ tptr tschar ] 
    EX p: val,
      PROP ( ) RETURN (p) 
      SEP (cstring Ews sigma s;
           cstring Ews sigma p;
           malloc_token Ews (tarray tschar (Zlength sigma + 1)) p;
           mem_mgr gv).

Definition hash_spec : ident * funspec :=
  DECLARE _hash
  WITH s: val, contents : list byte
  PRE [ tptr tschar ]
          PROP  ()
          PARAMS (s)
          SEP   (cstring Ews contents s)
  POST [ tuint ]
        PROP ()
	RETURN (Vint (Int.repr (hashfun contents)))
        SEP (cstring Ews contents s).

(* ----------------------------------------------------------------- *)
(** *** Data structures for hash table *)

(** Some abbreviations for C struct types that we use frequently *)
Definition tcell := Tstruct _cell noattr.
Definition thashtable := Tstruct _hashtable noattr.

(** A [list_cell] has four parts:
 - a linked list _cons_ cell with a key-pointer [kp], integer [count], and
   pointer to the [next] element of the linked list;
 - the key-pointer points to a string (null-terminated array of char)
   containing the key;
 - the cons cell was obtained by [malloc], and must be freeable by [free], 
   and so there's a [malloc_token] giving that capability;
 - the key-string also has a [malloc-token] so that it can be freed *)

Definition list_cell (key: list byte) (count: Z) (next: val) (p: val): mpred :=
 EX kp: val, cstring Ews key kp 
             * malloc_token Ews (tarray tschar (Zlength key + 1)) kp
             * data_at Ews tcell (kp,(Vint (Int.repr count), next)) p 
             * malloc_token Ews tcell p.

Definition list_cell_local_facts: 
  forall key count next p, list_cell key count next p |-- !! isptr p.
Proof. intros. unfold list_cell. Intros kp. entailer!. Qed.
Hint Resolve list_cell_local_facts: saturate_local.

Definition list_cell_valid_pointer:
  forall key count next p, list_cell key count next p |-- valid_pointer p.
Proof. intros. unfold list_cell. Intros kp. entailer!. Qed.
Hint Resolve list_cell_valid_pointer: valid_pointer.

(** **** Exercise: 1 star, standard (listcell_fold) *)
Lemma listcell_fold: forall key kp count p' p,
    cstring Ews key kp
    * malloc_token Ews (tarray tschar (Zlength key + 1)) kp
    * data_at Ews tcell (kp, (Vint (Int.repr count), p')) p
    * malloc_token Ews tcell p 
         |-- list_cell key count p' p.
Proof. 
(* FILL IN HERE *) Admitted.
(** [] *)

Fixpoint listrep (sigma: list (list byte * Z)) (x: val) : mpred :=
 match sigma with
 | (s,c)::hs => EX y: val, list_cell s c y x * listrep hs y
 | nil => 
    !! (x = nullval) && emp
 end.

(** **** Exercise: 2 stars, standard (listrep_hints) *)
Lemma listrep_local_prop: forall sigma p, listrep sigma p |--
        !! (is_pointer_or_null p  /\ (p=nullval <-> sigma=nil)).
Proof.
(* FILL IN HERE *) Admitted.
Hint Resolve listrep_local_prop : saturate_local.

Lemma listrep_valid_pointer:
  forall sigma p,
   listrep sigma p |-- valid_pointer p.
Proof.
(* FILL IN HERE *) Admitted.
Hint Resolve listrep_valid_pointer : valid_pointer.
(** [] *)

Lemma listrep_fold: forall key count p' p al, 
  list_cell key count p' p * listrep al p' |-- listrep ((key,count)::al) p.
Proof. intros. simpl. Exists p'. cancel. Qed.

(** A [listbox] is a pointer to a pointer to a cons cell. *)
Definition listboxrep al r :=
 EX p:val, data_at Ews (tptr tcell) p r * listrep al p.

Definition uncurry {A B C} (f: A -> B -> C) (xy: A*B) : C :=
  f (fst xy) (snd xy).

Definition hashtable_rep (contents: hashtable_contents) (p: val) : mpred :=
  EX bl: list (list (list byte * Z) * val),
    !! (contents = map fst bl) &&
    malloc_token Ews thashtable p * 
    field_at Ews thashtable [StructField _buckets] (map snd bl) p 
    * iter_sepcon (uncurry listrep) bl.

(** **** Exercise: 2 stars, standard (hashtable_rep_hints) *)
Lemma hashtable_rep_local_facts: forall contents p,
 hashtable_rep contents p |-- !! (isptr p /\ Zlength contents = N).
(* FILL IN HERE *) Admitted.
Hint Resolve hashtable_rep_local_facts : saturate_local.

Lemma hashtable_rep_valid_pointer: forall contents p,
 hashtable_rep contents p |-- valid_pointer p.
(* FILL IN HERE *) Admitted.
Hint Resolve hashtable_rep_valid_pointer : valid_pointer.
(** [] *)

(* ----------------------------------------------------------------- *)
(** *** Function specifications for hash table *)

Definition new_table_spec : ident * funspec :=
 DECLARE _new_table
 WITH gv: globals
 PRE [ ] 
   PROP()
   PARAMS() GLOBALS(gv)
   SEP(mem_mgr gv)
 POST [ tptr thashtable ] 
   EX p:val, PROP() 
      RETURN (p) 
      SEP(hashtable_rep empty_table p; mem_mgr gv).

Definition new_cell_spec : ident * funspec :=
 DECLARE _new_cell
 WITH s: val, key: list byte, count: Z, next: val, gv: globals
 PRE [ tptr tschar, tint, tptr tcell ] 
   PROP()
   PARAMS(s; Vint (Int.repr count); next) GLOBALS(gv)
   SEP(cstring Ews key s; mem_mgr gv)
 POST [ tptr tcell ] 
   EX p:val, PROP() 
      RETURN(p) 
      SEP(list_cell key count next p; cstring Ews key s;
          mem_mgr gv).

Definition get_spec : ident * funspec :=
 DECLARE _get
 WITH p: val, contents: hashtable_contents, s: val, sigma : list byte
 PRE [ tptr (Tstruct _hashtable noattr), tptr tschar ] 
    PROP () 
    PARAMS (p; s)
    SEP (hashtable_rep contents p; cstring Ews sigma s)
 POST [ tuint ]
    PROP ( )
    RETURN (Vint (Int.repr (hashtable_get sigma contents)))
    SEP (hashtable_rep contents p; cstring Ews sigma s).

Definition incr_list_spec : ident * funspec :=
 DECLARE _incr_list
 WITH r0: val, al: list (list byte * Z), s: val,
      sigma : list byte, gv: globals
 PRE [ tptr (tptr tcell), tptr tschar ] 
    PROP (list_get sigma al < Int.max_unsigned) 
    PARAMS (r0; s) GLOBALS(gv)
    SEP (listboxrep al r0; cstring Ews sigma s; mem_mgr gv)
 POST [ tvoid ]
      PROP ( ) RETURN ()
      SEP (listboxrep (list_incr sigma al) r0; 
           cstring Ews sigma s; mem_mgr gv).

Definition incr_spec : ident * funspec :=
 DECLARE _incr
 WITH p: val, contents: hashtable_contents, s: val,
      sigma : list byte, gv: globals
 PRE [ tptr (Tstruct _hashtable noattr), tptr tschar ] 
    PROP (hashtable_get sigma contents < Int.max_unsigned) 
    PARAMS (p; s) GLOBALS(gv)
    SEP (hashtable_rep contents p; cstring Ews sigma s; mem_mgr gv)
 POST [ tvoid ]
      PROP ( ) RETURN ()
      SEP (hashtable_rep (hashtable_incr sigma  contents) p;
           cstring Ews sigma s; mem_mgr gv).

(**  Putting all the funspecs together *)

Definition Gprog : funspecs :=
        ltac:(with_library prog [
                   strcmp_spec; strcpy_spec; strlen_spec; hash_spec;
                   new_cell_spec; copy_string_spec; get_spec; incr_spec; 
                   incr_list_spec
 ]).

(* ################################################################# *)
(** * Proofs of the functions [hash], [copy_string], [new_cell] *)

(** Before attempting to prove [body_hash], do [Verif_strlib] at
    least through [body_strlen]. *) 

(** **** Exercise: 3 stars, standard (body_hash) *)
Lemma body_hash: semax_body Vprog Gprog f_hash hash_spec.
Proof.
start_function.
unfold cstring in *.
(** 
  In the PROP part of your loop invariant, you'll want to maintain
    [0 <= i <= Zlength contents].
  In the LOCAL part of your loop invariant, try to use something like

    temp _c (Vbyte (Znth i (contents ++ [Byte.zero]))

  instead of 

    temp _c (Znth i (map Vbyte (...)))

  The reason is that [temp _c (Vint x)] or [temp _c (Vbyte y)] is much 
  easier for Floyd to handle than [temp _c X]
  where X is a general formula of type [val].
 
  Late in the proof of the loop body, the lemma [hashfun_snoc] will 
  be useful. *)
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, standard (body_copy_string) *)
Lemma body_copy_string: semax_body Vprog Gprog f_copy_string copy_string_spec.
Proof.
start_function.
assert_PROP (Zlength sigma + 1 <= Ptrofs.max_unsigned) by entailer!.
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, standard (body_new_cell) *)
Lemma body_new_cell: semax_body Vprog Gprog f_new_cell new_cell_spec.
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################################# *)
(** * Proof of the [new_table] function *)

(* ================================================================= *)
(** ** Auxiliary lemmas about data-structure predicates *)

(** **** Exercise: 2 stars, standard (iter_sepcon_hints) *)
Lemma iter_sepcon_listrep_local_facts:
 forall bl, iter_sepcon (uncurry listrep) bl
                    |-- !! Forall is_pointer_or_null (map snd bl).
Proof.
(* Hint: use [induction] and [sep_apply]. *)
(* FILL IN HERE *) Admitted.

Hint Resolve iter_sepcon_listrep_local_facts : saturate_local.
(** [] *)

(** **** Exercise: 2 stars, standard (iter_sepcon_split3) *)
Lemma iter_sepcon_split3: 
  forall {A}{d: Inhabitant A} (i: Z) (al: list A) (f: A -> mpred),
   0 <= i < Zlength al   -> 
  (iter_sepcon f al = 
   iter_sepcon f (sublist 0 i al) * f (Znth i al)
    * iter_sepcon f (sublist (i+1) (Zlength al) al))%logic.
Proof.
intros.
rewrite <- (sublist_same 0 (Zlength al) al) at 1 by auto.
(* Hint: [rewrite (sublist_split LO MID HI) by lia], where you choose
    values for LO MID HI. 
  Also useful:  [rewrite sublist_len_1]    and    [iter_sepcon_app].
  Finally, you'll have to use the associativity-commutativity of the "*" 
  operator: lemmas [sepcon_emp, sepcon_assoc, sepcon_comm], etc. *)
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, standard (body_new_table) *)
Lemma body_new_table_helper: 
 (* This lemma is useful as the very last thing to do in body_new_table *)
 forall p, 
  data_at Ews thashtable (list_repeat (Z.to_nat N) nullval) p
  |-- field_at Ews thashtable [StructField _buckets]
       (list_repeat (Z.to_nat N) nullval) p *
         iter_sepcon (uncurry listrep) (list_repeat (Z.to_nat N) ([], nullval)).
Proof.
intros.
unfold_data_at (data_at _ _ _ p).
(* FILL IN HERE *) Admitted.

Lemma body_new_table: semax_body Vprog Gprog f_new_table new_table_spec.
Proof.
(** The loop invariant in this function describes a partially 
  initialized array. The best way to do that is with something like,

  data_at Ews thashtable 
      (list_repeat (Z.to_nat i) nullval ++ 
       list_repeat (Z.to_nat (N-i)) Vundef)   p.

  Then at some point you'll have to prove something about,

   data_at Ews thashtable
      (list_repeat (Z.to_nat (i + 1)) nullval ++ 
       list_repeat (Z.to_nat (N - (i + 1))) Vundef)   p

  In particular, you'll have to split up 

   list_repeat (Z.to_nat (i + 1)) nullval

   into 

   list_repeat (Z.to_nat i) nullval ++ list_repeat (Z.to_nat 1) nullval.

  The best way to do that is [rewrite <- list_repeat_app']. *)
(* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################################# *)
(** * Proof of the [get] function *)

(** **** Exercise: 2 stars, standard (listrep_traverse) *)

(** Consider this loop in the [get] function:

  while (p) {
    if (strcmp(p->key, s)==0)
      return p->count;
    p=p->next;
  }

   We will reason about linked-list traversal in separation logic
   using "Magic Wand as Frame" 
   https://www.cs.princeton.edu/~appel/papers/wand-frame.pdf

  When the loop is partway down the linked list, we can view the
  original list up to the current position as a "linked-list data
  structure with a hole"; and the current position points to a
  linked-list data structure that fills the hole.  The
  "data-structure-with-a-hole" we reason about with separating
  implication, called "magic wand": (hole -* data-structure) which says,
  if you can conjoin this data-structure-with-a-hole with
  something-to-fill-the-hole, then you get the original data structure:

     hole * (hole -* data-structure) |-- data-structure

 Before the loop, we have a precondition such as,

   (listrep b0 p0; other_stuff)

 After a few loop iterations, we have a situation like,

   (listrep b p; (listrep b p -* listrep b0 p0); other_stuff)

 If the loop reaches [p==NULL], then we have,

   (listrep nil nullval; (listrep nil nullval -* listrep b0 p0); other_stuff)

 The [listrep_traverse_*] lemmas in this exercise illustrate how
 to start a traversal, how to perform one iteration of the traversal,
 and how to finish a traversal. *)

Lemma listrep_traverse_start:
  forall p al, 
    emp |-- listrep al p -* listrep al p.
(* FILL IN HERE *) Admitted.

Lemma listrep_traverse_step:
  forall al key count p' p, 
  list_cell key count p' p |-- 
     listrep al p' -* listrep ((key, count) :: al) p.
(* FILL IN HERE *) Admitted.

Lemma listrep_traverse_step_example:
 forall kp key count al q p b0 p0,
    cstring Ews key kp *
    (listrep ((key, count) :: al) p -* listrep b0 p0) *
    malloc_token Ews (tarray tschar (Zlength key + 1)) kp *
    data_at Ews tcell (kp, (Vint (Int.repr count), q)) p *
    malloc_token Ews tcell p * 
    listrep al q 
  |-- listrep b0 p0.
Proof.
intros.
(** Hint: use [sep_apply] with the lemmas [listcell_fold], 
  [listrep_traverse_step], [wand_frame_ver], [modus_ponens_wand]. *)
(* FILL IN HERE *) Admitted.

Lemma listrep_traverse_finish:
 forall al p,
   listrep nil nullval  *  (listrep nil nullval -* listrep al p)
  |-- listrep al p.
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, standard (body_get) *)

(** Use the [listrep_traverse_*] lemmas as appropriate. *)
Lemma body_get: semax_body Vprog Gprog f_get get_spec.
Proof.
start_function.
rename p into table.
pose proof (hashfun_inrange sigma).

unfold abbreviate in MORE_COMMANDS; subst MORE_COMMANDS.

(** This next command would not be part of an ordinary Verifiable C
   proof, it is here only to guide you through the bigger proof. *)
apply seq_assoc1; assert_after 1
 (EX cts:list (list (list byte * Z) * val), 
  PROP (contents = map fst cts ) 
  LOCAL (temp _h (Vint (Int.repr (hashfun sigma)));
         temp _table table;  temp _s s) 
  SEP (cstring Ews sigma s; malloc_token Ews thashtable table; 
       field_at Ews thashtable [StructField _buckets] (map snd cts) table; 
       iter_sepcon (uncurry listrep) cts))%assert.
{
 (* FILL IN HERE *) admit.
}
Intros cts; subst contents.
forward.
deadvars!.

autorewrite with norm. 
(** The previous line's [autorewrite] works only because 
  of hypothesis H. If you  [clear H; autorewrite with norm] you'll see
  that the [Int.modu] is not eliminated. *)

rewrite <- N_eq. 
(** The purpose of this rewrite is to preserve a little 
  bit of abstraction in the proofs.   Because N_eq is in the rep_lia
  Hint database, the [rep_lia] tactic "knows" that N=109. *)

assert (0 <= hashfun sigma mod N < N).
  (** It is useful to put facts like this above the line, to support 
      [rep_lia] in reasoning about conversions between Z and Int. *)
  (* FILL IN HERE *) admit.
assert_PROP (Zlength cts = N) as H1.
  (** Put equations like this above the line, to support [list_solve],
      [rep_lia],  and other tactics such as [entailer!] that call them. *)
{
 (* FILL IN HERE *) admit.
}
forward.
   (** Where did this proof goal come from?  [denote_tc_assert] is a
     "type-checking assertion", that is, "prove that a C expression
     evaluates without crashing."  In this case, the expression was
     [table->buckets[b]], and we have to prove here that [b] is in
     bounds of the array, and that the b'th element of the array is,
     in fact, initialized.

      The hypothesis H1 that you proved above is generally useful, and
      particularly in this proof right here. *)
 {  (* FILL IN HERE *) admit.
 }
set (h := hashfun sigma mod N) in *. 

(** This next line would not be part of an ordinary Verifiable C
   proof, it is here only to guide you through the bigger proof. *)
eapply semax_pre; [ instantiate (1:=
  PROP ( )   LOCAL (temp _p (snd (Znth h cts)); temp _s s)  
  SEP (cstring Ews sigma s; malloc_token Ews thashtable table; 
       field_at Ews thashtable [StructField _buckets] (map snd cts) table; 
       iter_sepcon (uncurry listrep) (sublist 0 h cts);
        listrep (fst (Znth h cts)) (snd (Znth h cts)); 
       iter_sepcon (uncurry listrep) (sublist (h + 1) (Zlength cts) cts))) | ].
{ (* FILL IN HERE *) admit.
}

destruct (Znth h cts) as [b0 p0] eqn:Hbp0.
simpl.
(** We have reached the while-loop that will walk down the linked list.
    The pointer [p0] is the pointer to the beginning of a list that
    represents the sequence [b0].  As the loop progresses, the loop 
    variable [p] will move down the links, pointing to smaller sequences [b].

    We represent the list segment from [p0] to [p] by a magic-wand
    formula:  [listrep b p -* listrep b0 p0].  This means a heaplet 
    (portion of memory) that, if you join it with a heaplet representing
    [listrep b p], would represent the entire [listrep b0 p0]. *)

(** Several of our SEP conjuncts will not be needed until after the
    loop is done.  We can hide them away in a single SEP-conjunct
    [FRZL FR1] by doing this command: *)
freeze FR1 := (malloc_token _ _ table) (field_at _ _ _ _ table)
       (iter_sepcon _ _) (iter_sepcon _ _).
(** The [freeze] tactic "frames out" several conjuncts for a while, 
  until later we [thaw FR1]. *)

forward_while 
 (EX b: list (list byte * Z), EX p: val,
    PROP( (* FILL IN HERE the explanation of how [b] relates to [b0].
          In particular, as you walk down the list past keys that
          don't match sigma, the result you would obtain by
          [list_get sigma] doesn't change. *)
          
        ) 
    LOCAL (temp _p p; temp _s s)
    SEP (FRZL FR1; cstring Ews sigma s
           (* FILL IN THE REST OF THE LOOP INVARIANT HERE!
             One of the conjuncts should be a magic-wand expression 
             describing a data structure with a hole;  the other conjuct
             describes what goes in the hole. *)
           
        )).
* (* Precondition implies loop invariant *)
(* FILL IN HERE *) admit.
* (* Loop test expression does not crash *)
(* FILL IN HERE *) admit.
* (* Loop body preserves loop invariant *)
 (** As usual in a linked-list traversal, we want to dereference
  [p->key] but we don't have a [data_at] conjunct for [p], we have
  only [listrep b p].  So we have to unfold the listrep; but this
  is useful only if we know that [p<>nil].  Therefore, case analysis: *)
destruct b as [ | [key count] al].
 (** This case, where b=nil, is impossible, because (if you have the
       right loop invariant) certain information in the SEP clause of
       the precondition is inconsistent with [HRE: isptr p] above the
       line.  To make use of propositional information in the SEP
       clause, use assert_PROP: *)
 {
   assert_PROP False. {
   (* FILL IN HERE *) admit.
   }
   contradiction.
 }
idtac.
(** The structure of the rest of this * bullet goes like this:

 - Massage the precondition and get through the forward_call to 
    function [strcmp].
 - Do  [forward_if (vret<>Int.zero)].  The argument you pass to forward_if
    can be a Prop, it does not need to be a full PROP/LOCAL/SEP, because:
   - One branch of the if never reaches the join point, it returns; and
   - The other branch of the if does not modify any local variables or
        memory, so the LOCAL and SEP parts of the assertion will be 
        unchanged.
 -
   - Sub-bullet: then-clause.  
       At some point in this proof, you'll need to [thaw FR1].
       You'll need to use [iter_sepcon_split3].
       Near the end of the then-clause, you'll have a goal similar
       (perhaps not identical) to [listrep_traverse_step_example].
   - Sub-bullet: else-clause.  Fairly short and straightforward proof.
   - Sub-bullet: after the if; another proof goal similar
     to [listrep_traverse_step_example]. *)
(* FILL IN HERE *) admit.
* (* After the loop *)
  (** Here, you still have a data structure with a hole, represented by
      (A -* B), and the thing-in-the-hole, represented by A.  This
      is similar to [listrep_traverse_finish]. *)   
  (* FILL IN HERE *) admit.
(* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################################# *)
(** * Proof of the [incr_list] function *)

(** Above, in the proof of the [get] function, we traverse a linked
   list without modifying it.  The loop invariant looked like,
    [listrep b p * (listrep b p -* listrep b0 p0)].

  But the [incr_list] function modifies a linked list, perhaps 
  inserting a new element at the end.  Furthermore, the C program's
  loop variable [struct cell **r] is a pointer to a pointer to a list
  cell.  Our separation-logic description of this is [listboxrep].  *)
Print listboxrep. (* = fun (al : list (list byte * Z)) (r : val) =>
     EX p : val, data_at Ews (tptr tcell) p r * listrep al p   *)

(** That is, [r] is a single-word box containing pointer [p],
   and [p] is a listrep.  Let's examine the loop that we want
   to verify:

void incr_list (struct cell **r0, char *s) {
  struct cell *p, **r;
  for(r=r0; ; r=&p->next) {
    p = *r;
    if (!p) { *r = new_cell(s,1,NULL); return; }
    if (strcmp(p->key, s)==0) {p->count++; return;}
} }

  We will describe variable [r] something like this:

  PROP() LOCAL(temp _r r) SEP(data_at Ews (tptr tcell) q r).

  That is, pointer to a single word containing [q].  But when
  we do [r = &(p->next)] we will have [r] pointing into the middle
  of a [struct cell] record, at the [next] field.  To  describe that
  single field all alone, we use [unfold_data_at] to split

  data_at Ews tcell (x,y,q) p

  into three separate conjuncts:

  field_at Ews tcell [StructField _key] x p *
  field_at Ews tcell [StructField _count] y p *
  field_at Ews tcell [StructField _next] q p

  and then we must rewrite the third conjunct into

  data_at Ews (tptr tcell) q (field_address tcell [StructField _next] p)

  where the [(field_address _ _ _)] is an "address arithmetic" expression
  that describes the offset, in bytes, from [p] to [&(p->next)].

  The [listboxrep_traverse] lemma illustrates the situation at
  the end of the loop body.  Look at the left-hand side of the [|--]
  entailment.  Variable [r] points to a single word containing [p]
  (it is perhaps the [_next] field of the previous list cell).
  Variable [p] points to a split-up list cell, with fields 
  [_key] and [_count].  Where is the [_next] field of [p]?  We choose
  not to describe it in this heaplet!
 
  The right-hand-side of this heaplet says, if you provide a heaplet
  satisfying [listboxrep] at address [&p->next] representing the 
  sequence [dl], then the combined heaplet satisfies [listboxrep]
  at address [r] representing the sequence [(key,count)::dl].
  Furthermore, this is true for _any_ sequence [dl].  That provides
  the freedom for the program to modify the contents of [p->next],
  or of any [_next] field later in the sequence. *)

(** **** Exercise: 3 stars, standard (listboxrep_traverse) *)
Lemma listboxrep_traverse:
  forall p kp key count r, 
     cstring Ews key kp * 
     malloc_token Ews (tarray tschar (Zlength key + 1)) kp *
     field_at Ews tcell [StructField _key] kp p *
     field_at Ews tcell [StructField _count] (Vint (Int.repr count)) p *
     malloc_token Ews tcell p *
     data_at Ews (tptr tcell) p r 
   |-- 
     ALL dl: list (list byte * Z), 
       listboxrep dl (field_address tcell [StructField _next] p)
       -* listboxrep ((key, count) :: dl) r.
Proof.
  intros.
 apply allp_right; intro dl.
 apply -> wand_sepcon_adjoint.
   (** Sometime during the proof below, you will have
       [data_at Ews tcell ... p]
     that you want to expand into 

       field_at Ews tcell [StructField _key] ... p 
     * field_at Ews tcell [StructField _count] ... p 
     * field_at Ews tcell [StructField _next] ... p]. 

   You can do this with [unfold_data_at (pattern)] where [pattern] is 
   something like [(data_at _ _ _ p)] indicating which SEP conjunct
   you want to expand.

   After that, you will want to rewrite by [field_at_data_at] ... *)

Check (field_at_data_at Ews tcell [StructField _next]). (* =
  forall v p, 
       field_at Ews tcell [StructField _next] v p =
       data_at Ews (nested_field_type tcell [StructField _next]) v
         (field_address tcell [StructField _next] p). *)
Eval simpl in (nested_field_type tcell [StructField _next]).
  (* = tptr (Tstruct _cell noattr) *)

(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 4 stars, standard (body_incr_list) *)
Lemma body_incr_list: semax_body Vprog Gprog f_incr_list incr_list_spec.
Proof.
(** This proof uses "magic wand as frame" to traverse _and update_ a
   (linked list) data structure.  This pattern is a bit more complex
   than the wand-as-frame pattern used in body_get, which did not
   update the data structure.  You will still use
   "data-structure-with-a-hole" and "what-is-in-the-hole"; but now the
   "data-structure-with-a-hole" must be able to accept the _future_
   hole-filler, not the one that is in the hole right now.

  The key lemmas to use are, [wand_refl_cancel_right],
   [wand_frame_elim'], and [wand_frame_ver].  When using
   [wand_frame_ver], you will find [listboxrep_traverse] to be useful. *)
(* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################################# *)
(** * field_compatible *)

(** Let's discuss how to address individual fields of structs, or
   individual slots of arrays. 

  First, [data_at sh (Tstruct _ _)] is equivalent to the
  conjunction of individual [field_at] predicates for each
  of the fields.  (Something similar holds for arrays.) *)
Lemma example_split_struct:
 forall p (x y z: val), 
      data_at Ews tcell (x,(y,z)) p
   =   (field_at Ews tcell [StructField _key] x p
     * field_at Ews tcell [StructField _count] y p
     * field_at Ews tcell [StructField _next] z p)%logic.
Proof.
intros.
unfold_data_at (data_at _ _ _ p).
rewrite sepcon_assoc.
reflexivity.
Qed.

(** Second, [field_at sh t gfs z p] is equivalent to
   [data_at sh (tptr t) z (field_address t gfs p)],
  that is, [field_address] is a way to describe the offset (in bytes)
  from the base of a struct to the address of a field of that struct
  (or similarly to an element of an array). *)

Lemma example_field_at_data_at:
 forall p (z: val),
   field_at Ews tcell [StructField _next] z p =
   data_at Ews (tptr tcell) z 
    (field_address tcell [StructField _next] p).
Proof.
intros.
 rewrite field_at_data_at.
 reflexivity.
Qed.

(** The [_next] field of [struct cell] is the  third field, after two integer
  fields.  If there is no padding between those fields (which is the case here),
  then the distance from the base of the struct to the base of the [_next] 
  field should be [2*sizeof(tint)]. *)

Lemma example_field_at_data_at':
 forall p (z: val),
   field_at Ews tcell [StructField _next] z p |--
   data_at Ews (tptr tcell) z 
    (offset_val (2 * sizeof tint) p).
Proof.
intros.
 rewrite field_at_data_at.
 unfold field_address.
 if_tac; simpl; auto.
 cancel.
 entailer!.
 destruct H0 as [H0 _].
 contradiction H0.
Qed.

(** But the converse does not hold: *)
Lemma example_field_at_data_at'':
 forall p (z: val),
   data_at Ews (tptr tcell) z 
    (offset_val (2 * sizeof tint) p)
 |-- field_at Ews tcell [StructField _next] z p.
Proof.
 intros.
 rewrite field_at_data_at.
 simpl.
 unfold field_address.
 rewrite if_true.
 simpl.
 cancel.
 (* Not provable! *)
Abort.

(** If we assume an extra premise, we can prove this, however: *)
Lemma example_field_at_data_at''':
 forall p (z: val),
  field_compatible tcell [StructField _next] p ->
   data_at Ews (tptr tcell) z 
    (offset_val (2 * sizeof tint) p)
 |-- field_at Ews tcell [StructField _next] z p.
Proof.
 intros.
 rewrite field_at_data_at.
 simpl.
 unfold field_address.
 rewrite if_true by assumption.
 simpl.
 cancel.
Qed.

(** Why is that?  The answer is in the definition of [field_address]: *)
Print field_address. (* = 
   fun {cs : compspecs} (t : type) (gfs : list gfield) (p : val) =>
    if field_compatible_dec t gfs p 
    then offset_val (nested_field_offset t gfs) p 
    else Vundef

    This says, if [field_compatible t gfs p] then the address
   of the field is (for example) [offset_val (2 * sizeof tint) p],
   but if [~ field_compatible t gfs p] then the address is [Vundef].
   That is, [field_address t gfs p] is defined only if the address [p]
   is compatible with [t] and [gfs].  What is [field_compatible] ? 

   Let [p] be a address, and let [t] be a C-language type.
   We might ask, is it legal to put an object of type [t]
   at address [p]?  Not always!  We require all these conditions:
   - [isptr p]:  [p] must be a pointer value (Vptr), not an 
        integer or undefined.
   - [complete_legal_cosu_type t = true]:
       [t] must be complete, e.g., if [typedef struct foo *t]
        then there must be a definition for [struct foo].
   - [size_compatible t p]: there must be at least [sizeof t]
       bytes before the maximum-possible address. 
   - [align_compatible t p]:  p must be an appropriate multiple
       of 2, of 4, or of 8 as necessary, so that each subfield of
       type [t] is appropriately aligned as required by the
       data type of that subfield.
   - [legal_nested_field t gfs]:  If we ask, "is it legal to put
       an object of type [t] with field-path [gfs] at address [p]?"
       then we must also know that [gfs] is a possible field-path
       in type [t].  For example, [StructField _count] is a possible field-path
       for type [tcell], but [StructField _s] is not-- there's
       no such field.

    We encapsulate all these properties of [t, p, gfs] in 
    the predicate [field_compatible]: *)
       
Print field_compatible. (* = 
  fun {cs : compspecs} (t : type) (gfs : list gfield) (p : val) =>
  isptr p /\
  complete_legal_cosu_type t = true /\
  size_compatible t p /\
  align_compatible t p /\
  legal_nested_field t gfs  *)

(** [_count] is a field of [struct cell] *)
Goal (legal_nested_field tcell [StructField _count]).
compute; auto 10.
Qed.

(** [_s] is not a field of [struct cell] *)
Goal (~ legal_nested_field tcell [StructField _s]).
compute. intuition congruence.
Qed.

(** 0 is a legal subscript of [struct cell *a[109]] *)
Goal (legal_nested_field (tarray (tptr tcell) 109) [ArraySubsc 0]).
compute. intuition congruence.
Qed.

(** 108 is a legal subscript of [struct cell *a[109]] *)
Goal (legal_nested_field (tarray (tptr tcell) 109) [ArraySubsc 108]).
compute. intuition congruence.
Qed.

(** 109 is not a legal subscript of [struct cell *a[109]] *)
Goal (~ legal_nested_field (tarray (tptr tcell) 109) [ArraySubsc 109]).
compute.  intuition congruence.
Qed.

(** Sometimes in the C language we want a pointer _just at
    the end_ of an array.  That is, given [struct cell *a[109]]
    we want the pointer value [ &a[109] ].  This is legal,
    even though this slot of the array does not exist.

    For this we want a variant of [legal_nested_field] that
    permits "just at the end": *)
Check legal_nested_field0. (* : type -> list gfield -> Prop *)

(** 108 is an an addressible subscript of [struct cell *a[109]] *)
Goal (legal_nested_field0 (tarray (tptr tcell) 109) [ArraySubsc 108]).
compute. intuition congruence.
Qed.

(** 109 is an an addressible subscript of [struct cell *a[109]] *)
Goal (legal_nested_field0 (tarray (tptr tcell) 109) [ArraySubsc 109]).
compute. intuition congruence.
Qed.

(** 110 is not an addressible subscript of [struct cell *a[109]] *)
Goal (~ legal_nested_field (tarray (tptr tcell) 109) [ArraySubsc 110]).
compute.  intuition congruence.
Qed.
       
(** Based on these two notions, 
  - [legal_nested_field] (loadable/storable field) and
  - [legal_nested_field0] (addressible field),
  we have, respectively [field_compatible] and [field_compatible0]. *)

Print field_compatible0. (* = 
  fun {cs : compspecs} (t : type) (gfs : list gfield) (p : val) =>
  isptr p /\
  complete_legal_cosu_type t = true /\
  size_compatible t p /\
  align_compatible t p /\
  legal_nested_field0 t gfs  *)

(* ================================================================= *)
(** ** Where does field_compatible come from? *)

(** Let's look again at this lemma: *)
Check example_field_at_data_at'''. (* : forall p (z: val),
  field_compatible tcell [StructField _next] p ->
   data_at Ews (tptr tcell) z 
    (offset_val (2 * sizeof tint) p)
 |-- field_at Ews tcell [StructField _next] z p. *)

(** We can apply this lemma if [field_compatible...] is above the line.
  How can we get that hypothesis above the line?
  Often the [entailer] or [entailer!] does this automatically,
  deriving it from [data_at] or [field_at] facts in the SEP clause
  of your left-hand side. *)

(* ################################################################# *)
(** * Proof of the [incr] function *)

(**

  void incr_list (struct cell **r0, char *s);

  void incr (struct hashtable *table, char *s) {
    unsigned int h = hash(s);
    unsigned int b = h % N;
    incr_list (& table->buckets[b], s);
  }

  The difficult part here is the function-argument, [ & table->buckets[b] ].
  The precondition of the [incr_list] function requires just a single
  pointer-to-pointer-to-cell, but we have an entire array of 109
  pointers-to-cell.  

  We start with [table], a pointer to a struct containing one
  field that's an array of 109 elements.  For calling [incr_list],
  we need to split that into two separate data structures:
  - the single-element array at [table->buckets+b]
  - all the rest of the data structure, including the other fields
    of [struct hashtable] (if there were any) and the
    elements [0..b-1] and [b+1..108] of the array.

  The [wand_slice_array] lemma can do this:  *)

Check wand_slice_array.
(*  : forall (lo hi n : Z) (t : type) (sh : Share.t)
             (al : list (reptype t)) (p : val),
       0 <= lo <= hi ->
       hi <= n ->
       Zlength al = n ->
       data_at sh (tarray t n) al p =
       !! field_compatible (tarray t n) [] p &&
       data_at sh (tarray t (hi - lo)) (sublist lo hi al)
         (field_address0 (tarray t n) [ArraySubsc lo] p) *
       array_with_hole sh t lo hi n al p.
*)
(** Here (array_with_hole sh t lo hi n al p) means *)
Print array_with_hole.
(*  : !! field_compatible (tarray t n) [] p &&
      (ALL cl : list (reptype t) ,
         data_at sh (tarray t (hi - lo)) cl
           (field_address0 (tarray t n) [ArraySubsc lo] p) -*
         data_at sh (tarray t n)
           (sublist 0 lo al' ++ cl ++ sublist hi n al') p)
*)

(** This says that [data_at sh (tarray t n) al p] can be split
   up into two pieces: 
   - 1. the slice from index [lo] to index [hi-1],
   - 2. everything else.   *)
   
(** Later in the proof of [body_incr], you need to handle 
    the function-argument, [ & (table->buckets[b]) ],
    where variable [_b] has the value [h].
    CompCert will calculate this as [table + (sizeof int)*h],
    which is to say,

    offset_val (sizeof (tptr tcell) * h) table

   But we want to express that as 
[[  
   field_address0 (tarray (tptr tcell) N) [ArraySubsc h]
      (field_address thashtable [StructField _buckets] table).

   As discussed above in the [field_compatible] section,
   to prove a field_address one must know that the address [table]
   is field-compatible with [thashtable], and that the address
   [table->buckets] is field-compatible with the [ArraySubsc h]
   field.  That's all proved in the following lemma: *)

Lemma body_incr_field_address_lemma:
  forall (table: val) (h : Z),
  0 <= h < N ->
  field_compatible (tarray (tptr tcell) N) []
    (field_address thashtable [StructField _buckets] table) ->
  field_compatible (tptr tcell) []
    (field_address0 (tarray (tptr tcell) N) 
       [ArraySubsc h]
       (field_address thashtable [StructField _buckets] table)) ->
  offset_val (sizeof (tptr tcell) * h) table =
  field_address0 (tarray (tptr tcell) N) [ArraySubsc h]
    (field_address thashtable [StructField _buckets] table).
Proof.
  intros.
 (** The Hint database allows [auto with field_compatible]
   to make use of the [field_compatible] facts above the line. *)
  rewrite field_address0_offset by auto with field_compatible.
  rewrite field_address_offset by auto with field_compatible.
  autorewrite with norm. auto.
Qed.

(** **** Exercise: 4 stars, standard (body_incr) *)
Lemma body_incr: semax_body Vprog Gprog f_incr incr_spec.
Proof.
start_function.
rename p into table.
rename H into Hmax.
assert_PROP (isptr table) as Htable by entailer!.

(** The next two lines would not be part of an ordinary Verifiable C
   proof; they are here only to guide you through the bigger proof. *)
subst MORE_COMMANDS; unfold abbreviate; match goal with |- semax _ _ (Ssequence ?c1 (Ssequence ?c2 ?c3)) _ => apply (semax_unfold_seq (Ssequence (Ssequence c1 c2) c3)); [ reflexivity | ] end.
pose (j := EX cts: list (list (list byte * Z) * val), PROP (contents = map fst cts; 0 <= hashfun sigma mod N < N; Zlength cts = N) LOCAL (temp _b (Vint (Int.repr (hashfun sigma mod N))); temp _h (Vint (Int.repr (hashfun sigma))); temp _table table; temp _s s; gvars gv) SEP (cstring Ews sigma s; malloc_token Ews thashtable table; data_at Ews (tarray (tptr tcell) N) (map snd cts) (field_address thashtable [StructField _buckets] table); iter_sepcon (uncurry listrep) cts; mem_mgr gv)); apply semax_seq' with j; subst j; abbreviate_semax.
{
 (* FILL IN HERE *) admit.
 }

Intros cts.
subst contents.
unfold hashtable_get in Hmax.
rewrite Zlength_map, H1 in Hmax.
set (h := hashfun sigma mod N) in *. 
erewrite (wand_slice_array h (h+1) N _ (tptr tcell))
  by first [rep_lia | list_solve ].

(** For the remainder of the proof, here are some useful lemmas:
    [sublist_len_1], [sublist_same], [sublist_map],
    [data_at_singleton_array_eq],
    [iter_sepcon_split3],  [iter_sepcon_app], [sublist_split],
    [field_at_data_at], [wand_slice_array_tptr_tcell] *)

(* FILL IN HERE *) Admitted.
(** [] *)

(* 2020-09-18 15:39 *)
