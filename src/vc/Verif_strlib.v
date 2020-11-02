(** * Verif_strlib: String functions *)

(**  In this chapter we show how to prove the correctness of C programs
 that use null-terminated character strings.

 Here are some functions from the C standard library, [strlib.c]

    #include <stddef.h>

    size_t strlen(const char *str) {
      size_t i;
      for (i=0; ; i++)
        if (str[i]==0) return i;
    }

    char *strcpy(char *dest, const char *src) {
      size_t i;
      for(i = 0;; i++){
        char d = src[i];
        dest[i] = d;
        if(d == 0) return dest;
      }
    }

    int strcmp(const char *str1, const char *str2) {
      size_t i;
      for(i = 0;; i++){
        char d1 = str1[i];
        char d2 = str2[i];
        if(d1 == 0 && d2 == 0) return 0;
        else if(d1 < d2) return -1;
        else if(d1 > d2) return 1;
      }
    }    
*)

(* ################################################################# *)
(** * Standard boilerplate *)

Require VC.Preface. (* Check for the right version of VST *)
Require Import VST.floyd.proofauto.
Require Import VC.strlib.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.
Require Import VC.hints.  (* Import special hints for this tutorial. *)
Require Import Coq.Strings.Ascii.

(* ################################################################# *)
(** * Representation of null-terminated strings. *)

(** Coq represents a string as a list-like Inductive of Ascii
    characters: *)
Locate string.  (* Coq.Strings.String.string *)
Print string.
(* Inductive string : Set :=
    EmptyString : string | String : Ascii.ascii -> string -> string *)

(** The C programming language represents a _character_ as
   a byte, that is, an 8-bit signed or unsigned integer.
   In Coq represent the 8-bit integers using the [byte] type. *)
Print byte.  (* Notation byte := Byte.int

    CompCert's [Byte] module is an 8-bit instantiation of
   the n-bit integers, just as the [Int] module is a 32-bit
   instantiation. 

   Here, we can ask what [Byte] knows about the theory of 8-bit
   modular integers: *)

Search byte. (* Too long a list of theorems to reproduce here! *)

(** We can convert a Coq string to a list of bytes: *)

Fixpoint string_to_list_byte (s: string) : list byte :=
  match s with
  | EmptyString => nil
  | String a s' => Byte.repr (Z.of_N (Ascii.N_of_ascii a))
                                      :: string_to_list_byte s'
  end.

Definition Hello := "Hello"%string.
Definition Hello' := string_to_list_byte Hello.

Eval simpl in string_to_list_byte Hello.
 (* = [Byte.repr 72; Byte.repr 101; Byte.repr 108; 
      Byte.repr 108; Byte.repr 111]   :   list byte *)

Section StringDemo.

  Variable p : val.  (* Suppose we have an address in memory *)
  
(** To describe a single byte in memory, we can use [data_at]
   with the signed-character type: *)
Print tschar.  (* = Tint I8 Signed noattr : type *)
Check (data_at Tsh tschar (Vint (Int.repr 72)) p).  (* : mpred *)

(** This [data_at Tsh tschar (Vint (Int.repr 72)) p] is an [mpred], that is,
 a memory predicate in separation logic.  It says, at address [p] in memory
 there is a sequence of bytes whose length is appropriate for type [tschar];
 that is, one byte.  The contents of this sequence of bytes (one byte) is a
 representation of the integer 72. The ownership share (access permission)
 of memory at address [p] is the "top share" [Tsh] *)

Check (data_at Tsh tschar (Vbyte (Byte.repr 72))).
(** We can express the same thing using [Vbyte (Byte.repr 72)]. In fact,
 [Vbyte] is not a primitive CompCert value, it is a definition: *)
Print Vbyte. (* = fun c : byte => Vint (Int.repr (Byte.signed c))
     : byte -> val *)

Goal Vbyte (Byte.repr 72) = Vint (Int.repr 72).
Proof. reflexivity. Qed.

Goal Vbyte (Byte.repr 72) = Vint (Int.repr 72).
Proof.
  unfold Vbyte.
  rewrite Byte.signed_repr.
  auto.
  rep_lia.
Qed.

(** The C programming language represents a string of length [k] as an array
   of nonnull characters (bytes), terminated by a null character.  We represent
   this in separation logic using the [cstring] memory-predicate: *)

Locate cstring. (* VST.floyd.entailer.cstring *)
Print cstring. (* =
  fun {CS : compspecs} (sh : Share.t) (s : list byte) (p : val) =>
  !! (~ In Byte.zero s) &&
  data_at sh (tarray tschar (Zlength s + 1)) (map Vbyte (s++[Byte.zero])) p *)

(** Here is an example of a [cstring] predicate that says, At address
   [p] there is a null-terminated string representing "Hello".  *)

Check (cstring Tsh Hello' p). (* : mpred *)

(** By unfolding the definition of [cstring] this is equivalent to, *)

Check (
  !! (~ In Byte.zero Hello') &&
  data_at Tsh (tarray tschar (5 + 1)) (map Vbyte (Hello'++[Byte.zero])) p ).

(** This says, no element of the list [Hello'] is equal to [Byte.zero].
 In memory at address [p] there is an array of 6 bytes, whose contents are
 the contents of [Hello'] with a [Byte.zero] appended at the end.

 Sometimes we know that there is a null-terminated string inside an  array of
 length [n].  That is, there are [k] nonnull characters (where [k<n]), 
 followed by a null character, followed by [n-(k+1)] uninitialized (or
 don't-care) characters.  We represent this with the [cstringn] predicate. *)
Print cstringn. (* =
 fun {CS : compspecs} (sh : Share.t) (s : list byte) (n : Z) (p : val) =>
 !! (~ In Byte.zero s) &&
 data_at sh (tarray tschar n)
  (map Vbyte (s ++ [Byte.zero]) ++
   list_repeat (Z.to_nat (n - (Zlength s + 1))) Vundef) p *)

Check (cstringn Tsh Hello' 10 p). (* : mpred *)

End StringDemo.

(* ################################################################# *)
(** * Reasoning about the contents of C strings *)

(** In separation logic proofs about C strings, we often find
  proof goals similar to the one exemplified by this lemma: *)
Lemma demonstrate_cstring1: 
 forall i contents
   (H:  ~ In Byte.zero contents)
   (H0: Znth i (contents ++ [Byte.zero]) <> Byte.zero)
   (H1: 0 <= i <= Zlength contents),
   0 <= i + 1 < Zlength (contents ++ [Byte.zero]).
Proof.
intros.
(** 
   A null-terminated string is an array of characters with three parts:
   - The contents of the string, none of which is the '\0' character;
   - The null termination character, equal to Byte.zero;
   - the remaining garbage in the array, after the null.
   When processing a string, you should maintain three kinds of 
   assumptions above the line:
  - Hypothesis [H] above the line says that none of the
  contents is the null character;
  - Hypothesis [H0] typically comes from a loop test, [s[i]!=0]
  - [H1] typically comes from a loop invariant:  suppose a 
  a loop iteration variable [_i] (with value [i])
  is traversing the array.  We expect that loop to go up to but 
  no farther than the null character, that is, one past the contents.

  The [cstring] tactic processes all three of these hypotheses to conclude
  that [i < Zlength contents]. *)
assert (H7: i < Zlength contents) by cstring.

(** But actually, [cstring] tactic will prove any rep_lia consequence
   of that fact.  For example: *)
clear H7.
autorewrite with sublist.
cstring.
Qed.

(** Here is another demonstration.  When your loop on the string
   contents reaches the end, the loop test [s[i]!=0] is false, so
   therefore [s[i]=0]. *)
Lemma demonstrate_cstring2: 
 forall i contents
   (H: ~ In Byte.zero contents)
   (H0: Znth i (contents ++ [Byte.zero]) = Byte.zero)
   (H1: 0 <= i <= Zlength contents),
   i = Zlength contents.
Proof.
intros.
(** Hypothesis [H0] expresses that the loop test determined [s[i]=0].
   The [cstring] can then prove that [i = Zlength contents].  *)
cstring.
Qed.

(* ################################################################# *)
(** * Function specs *)

(** [strlen(s)] returns the length of the string [s]. *)
Definition strlen_spec :=
 DECLARE _strlen
  WITH sh: share, s : list byte, str: val
  PRE [ tptr tschar ]
    PROP (readable_share sh)
    PARAMS (str)
    SEP (cstring sh s str)
  POST [ tuint ]
    PROP ()
    RETURN (Vptrofs (Ptrofs.repr (Zlength s)))
    SEP (cstring sh s str).

(** [strcpy(dest,src)] copies the string [src] to the array [dest]. *)
Definition strcpy_spec :=
 DECLARE _strcpy
  WITH wsh: share, rsh: share, dest : val, n : Z, src : val, s : list byte
  PRE [ tptr tschar, tptr tschar ]
    PROP (writable_share wsh; readable_share rsh; Zlength s < n)
    PARAMS (dest; src)
    SEP (data_at_ wsh (tarray tschar n) dest; cstring rsh s src)
  POST [ tptr tschar ]
    PROP ()
    RETURN (dest)
    SEP (cstringn wsh s n dest; cstring rsh s src).

(** [strcmp(s1,s2)] compares strings s1 and s2 for lexicographic
  order.  This funspec is an underspecification of the actual
  behavior, in that it specifies equality testing only. *)
Definition strcmp_spec :=
 DECLARE _strcmp
  WITH sh1: share, sh2: share, str1 : val, s1 : list byte, str2 : val,
       s2 : list byte
  PRE [ tptr tschar, tptr tschar ]
    PROP (readable_share sh1; readable_share sh2)
    PARAMS (str1; str2)
    SEP (cstring sh1 s1 str1; cstring sh2 s2 str2)
  POST [ tint ]
   EX i : int,
    PROP (if Int.eq_dec i Int.zero then s1 = s2 else s1 <> s2)
    RETURN (Vint i)
    SEP (cstring sh1 s1 str1; cstring sh2 s2 str2).

Definition Gprog : funspecs := [ strlen_spec; strcpy_spec; strcmp_spec ].

(* ################################################################# *)
(** * Proof of the [strlen] function *)

(** **** Exercise: 2 stars, standard (body_strlen) *)
Lemma body_strlen: semax_body Vprog Gprog f_strlen strlen_spec.
Proof.
start_function.
(** Look at the proof goal below the line.  We have the assertion,

  PROP ( )  LOCAL (temp _str str)  SEP (cstring sh s str))

 When proving things about a string-manipulating function, the
  first decision is:  Does this function treat the string _abstractly_
  or does it subscript the array and look at the individual characters?
  - If abstract, then we should _not_ unfold the definition [cstring].
  - If we subscript the array directly, we _must_ unfold [cstring].
  Since this [strlen] function does access the array contents, we
  start by unfolding [cstring].*)
unfold cstring in *.
(** Now, we have a [Prop]osition  [~ In Byte.zero s] in the [SEP]
    clause of our assertion; we can move it above the line by [Intros]. *)
Intros.
forward. (* i=0; *)

(** Now we are at a for-loop.  Unlike a simple while-loop, a for-loop may:
 - [break;] (prematurely terminate the loop)
 - [continue;] (prematurely terminate the body, skipping to the increment)
 So therefore the simple Hoare-logic _while_ rule is not always applicable.
 The general form of Verifiable C's loop tactic is:

  forward_loop Inv1  continue: Inv2 break: Inv3

 where [Inv1] is the invariant that holds right before the loop test,
 [Inv2] is the invariant that holds right before the increment, and
 [Inv3] is the postcondition of the loop.

 Providing  [continue: Inv2] is optional, as is [break: Inv3].
 In many cases the [forward_loop] tactic can figure out that the [continue:]
 invariant is not needed (if the loop doesn't contain a [continue] statement),
 or the [break:] postcondition is not needed (if there's no [break] 
 statement, or if there are no commands after the loop).

  So let's try this loop with only a single loop invariant: *)
forward_loop  (EX i : Z,
  PROP (0 <= i < Zlength s + 1)
  LOCAL (temp _str str; temp _i (Vptrofs (Ptrofs.repr i)))
  SEP (data_at sh (tarray tschar (Zlength s + 1))
          (map Vbyte (s ++ [Byte.zero])) str)).
(** Look at the [LOCAL] clause that binds [temp _i] to the value
   [Vptrofs (Ptrofs.repr i)].  What is that?  The answer is,
   in reasoning about C programs, we need:
  - 8-bit integers, [Byte.int] or simply [byte]
  - 32-bit integers, [Int.int] or simply [int]
  - 64-bit integers, [Int64.int]
  But there is also the concept expressed in C as [size_t], that is,
  _The integer type with the same number of bits as a pointer_.
  In this might be the same as 32-bit int, or it might be the same
  as 64-bit int.

  So, just as CompCert has the [Int] module for reasoning about 32-bit
  integers and the Int64 module for 64-bit integers, it has also
  the [Ptrofs] module for reasoning about _pointer offsets_.  [Ptrofs]
  is isomorphic to (but not identical to) either [Int64] or [Int],
  depending on the boolean value [Archi.ptr64]. *)

Compute Archi.ptr64. (* = false : bool *)

(** If this computes [false], then this installation of Verifiable C is
 configured for 32-bit pointers; if [true], then this Verifiable C is
 configured for 64-bit.  But either way, to turn a [Ptrofs.int] value into a
 CompCert [val], we have [Vptrofs]. And -- just as we can write C programs
 that are portable to 32-bit or 64-bit pointers using [size_t], we can write
 proofs scripts portable by using [Ptrofs].  *)
Print Vptrofs. (* = 
 fun n : ptrofs =>
   if Archi.ptr64 then Vlong (Ptrofs.to_int64 n) 
                  else Vint (Ptrofs.to_int n)
     : ptrofs -> val 

    And therefore, [_i] is a C variable of type [size_t], 
  [i] is a Coq variable of type [Z], and and [Vptrofs (Ptrofs.repr i)]
  is a CompCert [val] that _represents_ [i] as a [val]. *)

assert (Example: Archi.ptr64=false -> 
          forall n, Vptrofs (Ptrofs.repr n) = Vint (Int.repr n)). {
 intro Hx; try discriminate Hx. (* in case Archi.ptr64 = true *)
  (* In a 32-bit C system: *)
all:  intros.
all:  hint.
all:  autorewrite with norm.
all:  auto.
} clear Example.

(** Now it's time to prove all the subgoals of [forward_loop]. *)
* (* Prove the precondition entails the loop invariant *)
(* FILL IN HERE *) admit.
* (* Prove the loop body preserves the invariant *)
(* FILL IN HERE *) admit.
(* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################################# *)
(** * Proof of the [strcpy] function *)

(** **** Exercise: 2 stars, standard (strcpy_then_clause)

    The next lemma, or some variation of it, will be useful in the proof of
 the [strcpy] function (in the _then_ clause of the _if_ statement). *)
Lemma strcpy_then_clause:
  forall (wsh: share) (dest: val) (n: Z) (s: list byte),
  Zlength s < n ->
  ~ In Byte.zero s ->
    data_at wsh (tarray tschar n)
      (map Vbyte (sublist 0 (Zlength s) s) ++
       upd_Znth 0 (list_repeat (Z.to_nat (n - Zlength s)) Vundef)
         (Vint (Int.repr (Byte.signed (Znth (Zlength s) (s ++ [Byte.zero]))))))
      dest
  |-- data_at wsh (tarray tschar n)
        (map Vbyte (s ++ [Byte.zero]) ++
             list_repeat (Z.to_nat (n - (Zlength s + 1))) Vundef)
        dest.
Proof.
intros.
apply derives_refl'.
f_equal.
Check list_repeat_app'.  (* Hint: this lemma will be useful. *)
Check upd_Znth_app1.     (* Hint: this lemma will be useful. *)
Check app_Znth2.         (* Hint: this lemma will be useful. *)
Check Znth_0_cons.       (* Hint: this lemma will be useful. *)
(* Other useful lemmas will be map_app, app_ass *)
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard (strcpy_else_clause) *)
Lemma strcpy_else_clause: forall wsh dest n s i,
  Zlength s < n ->
  ~ In Byte.zero s ->
  0 <= i < Zlength s + 1 ->
  Znth i (s ++ [Byte.zero]) <> Byte.zero ->
     data_at wsh (tarray tschar n)
      (upd_Znth i (map Vbyte (sublist 0 i s)
                       ++ list_repeat (Z.to_nat (n - i)) Vundef)
             (Vint (Int.repr (Byte.signed (Znth i (s ++ [Byte.zero])))))) dest
  |-- data_at wsh (tarray tschar n)
      (map Vbyte (sublist 0 (i + 1) s)
           ++ list_repeat (Z.to_nat (n - (i + 1))) Vundef) dest.
Proof.
intros.
apply derives_refl'.
f_equal.
(** Useful lemmas here will be: upd_Znth_app2, sublist_split,
list_repeat_app', app_Znth1, map_app, app_ass, sublist_len_1. *)
(* FILL IN HERE *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** data_at is not injective!

    The [Vundef] value means _uninitialized_ or _undefined_ or
   _defined but don't care_.  Consider this lemma: *)
Lemma data_at_Vundef_example:
  forall i n sh p,
    0 <= i < n ->
  data_at sh (tarray tschar n)
          (list_repeat (Z.to_nat (i+1)) (Vbyte Byte.zero)
             ++ list_repeat (Z.to_nat (n-(i+1))) Vundef) p
 |--           
  data_at sh (tarray tschar n)
          (list_repeat (Z.to_nat i) (Vbyte Byte.zero)
             ++ list_repeat (Z.to_nat (n-i)) Vundef) p.
Proof.
intros.

(** The proof goal means: If cells [0 <= j < i+1] are zero and cells
   [i+1 <= j < n] are don't care, that implies the weaker statement that
   cells [0 <= j < i] are zero and cells [i <= j < n] are don't-care.

   Now, let's try to prove it using the same technique as in
   [strcpy_then_clause]: *)
apply derives_refl'.
f_equal.
rewrite <- list_repeat_app' by lia.
replace (n-i) with (1 + (n-(i+1))) by lia.
rewrite <- list_repeat_app' by lia.
rewrite !app_ass.
f_equal.
f_equal.
(** Oops!  The current proof goal is False!  The problem was
that we should not have applied [derives_refl']. *)
Abort.

Lemma data_at_Vundef_example:
  forall i n sh p,
    0 <= i < n ->
  data_at sh (tarray tschar n)
          (list_repeat (Z.to_nat (i+1)) (Vbyte Byte.zero)
             ++ list_repeat (Z.to_nat (n-(i+1))) Vundef) p
 |--           
  data_at sh (tarray tschar n)
          (list_repeat (Z.to_nat i) (Vbyte Byte.zero)
             ++ list_repeat (Z.to_nat (n-i)) Vundef) p.
Proof.
intros.
rewrite <- list_repeat_app' by lia.
replace (n-i) with (1 + (n-(i+1))) by lia.
rewrite <- list_repeat_app' by lia.
rewrite !app_ass.
Check split2_data_at_Tarray_app.
(*  forall (cs : compspecs) (mid n : Z) (sh : Share.t) 
    (t : type) (v1 v2 : list (reptype t)) (p : val),
  Zlength v1 = mid ->
  Zlength v2 = n - mid ->
  data_at sh (tarray t n) (v1 ++ v2) p =
  data_at sh (tarray t mid) v1 p *
  data_at sh (tarray t (n - mid)) v2
    (field_address0 (tarray t n) [ArraySubsc mid] p)
*)
rewrite (split2_data_at_Tarray_app i) by list_solve.
rewrite (split2_data_at_Tarray_app 1) by list_solve.
rewrite (split2_data_at_Tarray_app i) by list_solve.
rewrite (split2_data_at_Tarray_app 1) by list_solve.
cancel.
Qed.

(** Why did that work?  Let's look at a simpler example. *)

Lemma cancel_example:
 forall sh i j p q, 
   data_at sh tint (Vint i) p * data_at sh tint (Vint j) q
 |-- data_at sh tint (Vint i) p * data_at sh tint (Vundef) q.
Proof.
intros.
(** Uncomment the following line, and notice that it solves the goal. *)
(* cancel.

    [cancel] breaks this into two subgoals: *)
apply sepcon_derives.
- 
(** In the first subgoal, we use the fact that |-- is reflexive *)
apply derives_refl.
-
(** In the second subgoal, we use the fact that _any_ value
  implies a Vundef, or more generally, _any_ value implies
  [default_val t] for any CompCert type t. *)
apply stronger_default_val.
Qed.

(** The moral of the story is:  When proving 

   data_at sh t a p |-- data_at sh t b p

   if (a=b) you can simplify the goal using

   apply derives_refl'; f_equal.

   but if a is strictly more defined than b, then derives_refl' is not appropriate. *)

(** **** Exercise: 3 stars, standard (body_strcpy) *)
Lemma body_strcpy: semax_body Vprog Gprog f_strcpy strcpy_spec.
Proof.
start_function.
(** Because this function subscripts the strings, it does _not_
  treat the strings abstractly, we must unfold [cstring] and [cstringn]. *)  
unfold cstring,cstringn in *.
forward.
Intros.
forward_loop (EX i : Z,
  PROP (0 <= i < Zlength s + 1)
  LOCAL (temp _i (Vint (Int.repr i)); temp _dest dest; temp _src src)
  SEP (data_at wsh (tarray tschar n)
        (map Vbyte (sublist 0 i s) ++ list_repeat (Z.to_nat (n - i)) Vundef) dest;
       data_at rsh (tarray tschar (Zlength s + 1)) (map Vbyte (s ++ [Byte.zero])) src)).
+ (* Prove the precondition implies the loop invariant *)
(* FILL IN HERE *) admit.
+ (* Prove the loop body

    In the [then] clause of this proof, you may reach a proof goal similar to
 Lemma strcpy_then_clause, but not identical.  In that case you may want to
 use the same proof techniques you used in that exercise.  Ditto for the else
 clause, and strcpy_else_clause. *)
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, standard (example_call_strcpy)

    Prove the correctness of a function that calls [strcpy].

  int example_call_strcpy(void) {
    char buf[10];
    strcpy(buf,"Hello");
    return buf[0];
  }
*)

Definition stringlit_1_contents := Hello' ++ [Byte.zero].

Definition example_call_strcpy_spec :=
 DECLARE _example_call_strcpy
  WITH gv: globals
  PRE [  ]
    PROP ()
    PARAMS() GLOBALS (gv)
    SEP (cstring Ews (Hello' ++ [Byte.zero]) (gv ___stringlit_1))
  POST [ tint ]
    PROP ()
    RETURN (Vint (Int.repr (Z.of_N (Ascii.N_of_ascii "H"%char))))
    SEP (cstring Ews (Hello' ++ [Byte.zero]) (gv ___stringlit_1)).

Lemma body_example_call_strcpy: semax_body Vprog Gprog 
         f_example_call_strcpy example_call_strcpy_spec.
Proof.
start_function.
(** This proof is fairly straightforward.  First, figure out what WITH
 witness to give for forward_call.  Hint: look at the SEP clause of the
 precondition of strcpy_spec, and see how the [data_at] and [cstring]
 conjuncts must match your current assertion.

 Second, after the forward_call, don't forget to unfold [cstringn]; this is
 necessary because after the call we subscript the [_buf] array directly. *)
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 4 stars, standard, optional (body_strcmp) *)
Lemma body_strcmp: semax_body Vprog Gprog f_strcmp strcmp_spec.
(* FILL IN HERE *) Admitted.
(** [] *)

(* 2020-09-18 15:39 *)
