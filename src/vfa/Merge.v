(** * Merge:  Merge Sort, With Specification and Proof of Correctness*)

From VFA Require Import Perm.
From VFA Require Import Sort.
From Coq Require Import Recdef.  (* needed for [Function] feature *)

(** Mergesort is a well-known sorting algorithm, normally presented
    as an imperative algorithm on arrays, that has worst-case
    O(n log n) execution time and requires O(n) auxiliary space.

    The basic idea is simple: we divide the data to be sorted into two
    halves, recursively sort each of them, and then
    merge together the (sorted) results from each half:

    [[
    mergesort xs =
      split xs into ys,zs;
      ys' = mergesort ys;
      zs' = mergesort zs;
      return (merge ys' zs')
    ]]

    (As usual, if you are unfamiliar with mergesort see Wikipedia or
    your favorite algorithms textbook.)

    Mergesort on lists works essentially the same way: we split the
    original list into two halves, recursively sort each sublist,
    and then merge the two sublists together again.  The only 
    difference, compared to the imperative algorithm, is that splitting
    the list takes O(n) rather than O(1) time; however, that 
    does not affect the asymptotic cost, since the merge step already
    takes O(n) anyhow. 
*)

(* ================================================================= *)
(** ** Split and its properties *)

(** Let us try to write down the Gallina code for mergesort.
    The first step is to write a splitting function. There are
    several ways to do this, since the exact splitting method does
    not matter as long as the results are (roughly) equal in size.
    For example, if we know the length of the list, we could use that to split
    at the half-way point. But here is an attractive alternative, which simply
    alternates assigning the elements into left and right sublists:
*)     

Fixpoint split {X:Type} (l:list X) : (list X * list X) :=
  match l with
  | [] => ([],[])
  | [x] => ([x],[])
  | x1::x2::l' =>
    let (l1,l2) := split l' in
    (x1::l1,x2::l2)
  end.

(** Note: For generality, we made this function polymorphic, since the
    type of the values in the list is irrelevant to the splitting process. 

    While this function is straightforward to define, it can be a bit challenging
    to work with.  Let's try to prove the following lemma, which is obviously true:
*)

Lemma split_len_first_try: forall {X} (l:list X) (l1 l2: list X),
    split l = (l1,l2) ->
    length l1 <= length l /\
    length l2 <= length l.
Proof.
  induction l; intros. 
  - inv H. simpl. omega. 
  - destruct l as [| x l'].
    + inv H. 
      split; simpl; auto.
    + inv H. destruct (split l') as [l1' l2'] eqn:E. inv H1. 
      (* We're stuck! The IH talks about [split (x::l')] but we
         only know aobut [split (a::x::l'). *)
Abort.

(** The problem here is that the standard induction principle for lists
    requires us to show that the property being proved follows for      
    any non-empty list if it holds for the tail of that list.
    What we want here is a "two-step" induction principle, that instead requires
    us to show that the property being proved follows for a list of
    length at least two, if it holds for the tail of the tail of that list.
    Formally: 
*)

Definition list_ind2_principle:=
    forall (A : Type) (P : list A -> Prop),
      P [] ->
      (forall (a:A), P [a]) ->
      (forall (a b : A) (l : list A), P l -> P (a :: b :: l)) ->
      forall l : list A, P l.

(** If we assume the correctness of this "non-standard" induction principle, 
    our [split_len] proof is easy, using a form of the [induction] tactic 
    that lets us specify the induction principle to use: 
*)

Lemma split_len': list_ind2_principle -> 
    forall {X} (l:list X) (l1 l2: list X),
    split l = (l1,l2) ->
    length l1 <= length l /\
    length l2 <= length l.
Proof.
  unfold list_ind2_principle; intro IP.
  induction l using IP; intros.
  - inv H. omega.
  - inv H. simpl; omega.
  - inv H. destruct (split l) as [l1' l2']. inv H1. 
    simpl. 
    destruct (IHl l1' l2') as [P1 P2]; auto; omega.
Qed.

(** We still need to prove [list_ind2_principle].  There are several
    ways to do this, but one direct way is to write an explicit proof
    term, thus: *)

Definition list_ind2 :
  forall (A : Type) (P : list A -> Prop),
      P [] ->
      (forall (a:A), P [a]) ->
      (forall (a b : A) (l : list A), P l -> P (a :: b :: l)) ->
      forall l : list A, P l :=
  fun (A : Type)
      (P : list A -> Prop)
      (H : P [])
      (H0 : forall a : A, P [a])
      (H1 : forall (a b : A) (l : list A), P l -> P (a :: b :: l))  => 
    fix IH (l : list A) :  P l :=
    match l with
    | [] => H
    | [x] => H0 x
    | x::y::l' => H1 x y l' (IH l')
    end.

(** Here, the [fix] keyword defines a local recursive function [IH]
    of type [forall l:list A, P l], which is returned as the overall value of
    [list_ind2]. As usual, this function must be obviously terminating 
    to Coq (which it is because the recursive call is on a sublist [l'] 
    of the original argument [l]) and the [match] must be exhaustive over
    all possible lists (which it evidently is). 
*)

(** With our induction principle in hand, we can finally prove 
    [split_len] free and clear: 
*)

Lemma split_len: forall {X} (l:list X) (l1 l2: list X),
    split l = (l1,l2) ->
    length l1 <= length l /\
    length l2 <= length l.
Proof.
 apply (@split_len' list_ind2).
Qed.

(** **** Exercise: 3 stars, standard (split_perm)  *)

(** Here's another fact about [split] that we will find useful later on.  
*)

Lemma split_perm : forall {X:Type} (l l1 l2: list X),
    split l = (l1,l2) -> Permutation l (l1 ++ l2).
Proof.
  induction l as [| x | x1 x2 l1' IHl'] using list_ind2; intros.
(* FILL IN HERE *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** Defining Merge *)

(** Next, we need a [merge] function, which takes two
    sorted lists (of naturals) and returns their sorted result.
    This would seem easy to write:

    [[
    Fixpoint merge l1 l2 :=
      match l1, l2 with
      | [], _ => l2
      | _, [] => l1
      | a1::l1', a2::l2' =>
          if a1 <=? a2 then a1 :: merge l1' l2 else a2 :: merge l1 l2'
      end.
    ]]

    But Coq will reject this definition with the message:

    [[
    Error: Cannot guess decreasing argument of fix.
    ]]

    Coq insists the every [Fixpoint] definition be structurally recursive
    on some specified argument, meaning that at each recursive call the
    callee is passed a value that is a sub-term of the caller's argument value.
    This check guarantees that every [Fixpoint] is actually terminating.

    It is fairly obvious that this function is in fact terminating, because
    at each call, either [l1] or [l2] is passed the tail of its original value.
    But unfortunately, [Fixpoint] recursive calls must always decrease on
    a _single fixed_ argument -- and neither [l1] nor [l2] will do. (That's
    why Coq couldn't guess the one to use.)  We might reasonably wish
    that Coq was a little smarter, but it isn't.

    There are a number of ways to get around the problem of convincing
    Coq that a function is actually terminating when the "natural" [Fixpoint]
    doesn't work. In this case, a little creativity (or a peek at the Coq
    library) might lead us to the following definition:
*)

Fixpoint merge l1 l2  {struct l1} :=
  let fix merge_aux l2 :=
  match l1, l2 with
  | [], _ => l2
  | _, [] => l1
  | a1::l1', a2::l2' =>
      if a1 <=? a2 then a1 :: merge l1' l2 else a2 :: merge_aux l2'
  end
  in merge_aux l2.

(** Coq accepts the outer definition because it is structurally
    decreasing on [l1] (we specify that with the [{struct l1}] annotation,
    although Coq would have guessed this even if we didn't write it), 
    and it accepts the inner definition because it is structurally recursive 
    on its (sole) argument. (Note that [let fix ... in ... end] is just a 
    mechanism for  defining a local recursive function.)  

    This definition will turn out to work pretty well; the only irritation 
    is that simplification will show the definition of [merge_aux], as
    illustrated by the following examples. 

    First, let's remind ourselves that Coq desugars a [match] over multiple 
    arguments into a nested sequence of matches: 
*)

Print merge.

(** ==> (after a little renaming for clarity)

    [[
    fix merge (l1 l2 : list nat) {struct l1} : list nat :=
      let
        fix merge_aux (l2 : list nat) : list nat :=
          match l1 with
          | [] => l2
          | a1 :: l1' =>
              match l2 with
              | [] => l1
              | a2 :: l2' =>
                  if a1 <=? a2 then a1 :: merge l1' l2 else a2 :: merge_aux l2'
              end
          end in
      merge_aux l2.
    ]]
*)

(** Let's prove the following simple lemmas about [merge]: 
*)

Lemma merge2 : forall (x1 x2:nat) r1 r2,
    x1 <= x2 ->
    merge (x1::r1) (x2::r2) =
    x1::merge r1 (x2::r2).
Proof.
  intros.
  simpl. (* This blows up in an unpleasant way, but we can
      still make some sense of it.  Look at the
      [(fix merge_aux ...)] term. It represents the
      the local function [merge_aux] after the value of the
      free variable [l1] has been substituted by [x1::r1],
      the match over [l1] has been simplified to its
      second arm (the non-empty case) and [x1] and [r1] have
      been substituted for the pattern variables [a1] and [l1']. 
      The entire [fix] is applied to [r2], but Coq won't attempt
      any further simplification until the structure of [r2] 
      is known. *)
  bdestruct (x1 <=? x2).
  - auto.
  - (* Since [H] and [H0] are contradictory, this case follows by [omega].
       But (ignoring that for the moment), note that we can get further 
       simplification to occur if we give some structure to [l2]: *)
    simpl. (* does nothing *)
    destruct r2; simpl.  (* makes some progress *)
    + omega.
    + omega. 
Qed.  

Lemma merge_nil_l : forall l, merge [] l = l. 
Proof.
  intros. simpl.
  (* Once again, we see a version of [merge_aux] specialized to
  the value [l1 = nil]. Now we see only the first arm (the
  empty case) of the [match] expression, which simply returns [l2];
  in other words, here the [fix] is just the identity function. 
  And once again, the [fix] is applied to [l].  Irritatingly,
  Coq _still_ refuses to perform the application unless [l]
  is destructured first (even though the answer is always [l]). *)
  destruct l.
  - auto.
  - auto. 
Qed.

(** Morals: 

    (1) Even though the proof state involving local recursive
        functions can can be hard to read, persevere!

    (2) If Coq won't simplify an "obvious" application, try destructing
        the argument.

    We will defer stating and proving other properties of [merge] until later.
*)

(* ================================================================= *)
(** ** Defining Mergesort *)

(** Finally, we need to define the main mergesort function itself.
    Once again, we might hope to write something simple like this:

    [[
    Fixpoint mergesort (l: list nat) :  list nat :=
       let (l1,l2) := split l in
       merge (mergesort l1) (mergesort l2).
    ]]

    Since this function has only one argument, Coq guesses that it is
    intended to be structurally decreasing, but still 
    rejects the definition, this time with the complaint:

    [[
    Recursive call to mergesort has principal argument equal to 
    "l1" instead of a subterm of "l".
    ]]

    Again, the problem is that Coq has no way to know that [l1] and [l2]
    are "smaller" than [l].  And this time, it is hard to complain that
    Coq is being stupid, since the fact that [split] returns smaller
    lists than it is passed is nontrivial.

    In fact, it isn't true! Consider the behavior of [split] on 
    empty or singleton lists...  This is case where Coq's totality
    requirements can actually help us correct the definition of 
    our code.  What we really want to write is something more like:

    [[
    Fixpoint mergesort (l: list nat) :  list nat :=
        match l with
        | [] => []
        | [x] => [x]
        | _ => let (l1,l2) := split l in merge (mergesort l1) (mergesort l2).
    ]]

    Now this function really is terminating!  But Coq still won't let us
    write it with a [Fixpoint].  Instead, we need to use a mechanism 
    (there are several available) for defining functions that accommodates
    an explicit way to show that the function only calls itself on smaller
    arguments.   We will use the [Function] command:
*)

Function mergesort (l: list nat) {measure length l} :  list nat :=
  match l with
  | [] => []
  | [x] => [x]
  | _ => let (l1,l2) := split l in
         merge (mergesort l1) (mergesort l2)
  end.

(** [Function] is similar to [Fixpoint], but it lets us specify 
    an explicit _measure_ on the function arguments. 
    The annotation [{measure length l}] says that the function 
    [length] applied to argument [l] serves as a decreasing measure.  
    After processing this definition, Coq enters proof mode and demands 
    proofs that each recursive call is indeed on a shorter list. 
    Happily, we proved that fact already. 
*)

Proof.
  - (* recursive call on l1 *)
    intros.
    simpl in *.  destruct (split l1) as [l1' l2'] eqn:E. inv teq1. 
    destruct (split_len _ _ _ E).
    simpl. omega.
  - (* recursive call on l2 *)
    intros.
    simpl in *. destruct (split l1) as [l1' l2'] eqn:E. inv teq1. 
    destruct (split_len _ _ _ E).
    simpl. omega.
Defined.

(** Notice that the [Proof] must end with the keyword [Defined] rather
    than [Qed]; if we don't do this, we won't be able to actually 
    compute with [mergesort]. 

    Defining [mergesort] with [Function] rather than [Fixpoint] causes
    the automatic generation of some useful auxiliary definitions that we 
    will need when working with it. 
    First, we get a lemma [mergesort_equation], which performs a one-level
    unfolding of the function. *)

Check mergesort_equation.
 
(** ==> 

    [[
    mergesort_equation
     : forall l : list nat,
       mergesort l =
       match l with
       | [] => []
       | [x] => [x]
       | x :: _ :: _ =>
           let (l2, l3) := split l in merge (mergesort l2) (mergesort l3)
       end
    ]]

    We should always use [apply mergesort_equation]
    to simplify a call to [mergesort] rather than trying to [unfold] or [simpl]
    it, which will lead to ugly or mysterious results.

    Second, we get an induction principle [mergesort_ind]; performing
    induction using this principle can be much easier than trying to
    use list induction over the argument [l].  
*)

Check mergesort_ind.

(** ==>   
    [[
    mergesort_ind
     : forall P : list nat -> list nat -> Prop,
       (forall l : list nat, l = [] -> P [] []) ->
       (forall (l : list nat) (x : nat), l = [x] -> P [x] [x]) ->
       (forall l _x : list nat,
        l = _x ->
        match _x with
        | _ :: _ :: _ => True
        | _ => False
        end ->
        forall l1 l2 : list nat,
        split l = (l1, l2) ->
        P l1 (mergesort l1) ->
        P l2 (mergesort l2) -> P _x (merge (mergesort l1) (mergesort l2))) ->
        forall l : list nat, P l (mergesort l)
    ]]
*)

(* ================================================================= *)
(** ** Correctness: Sortedness *)

(** As with insertion sort, our goal is to prove that mergesort produces
    a sorted list that is a permutation of the original list, i.e. to prove
    
    [[
    is_a_sorting_algorithm mergesort
    ]] 
  
    We will start by showing that [mergesort] produces a sorted list.  The key 
    lemma is to show that [merge] of two sorted lists produces a sorted list.
    It is perhaps easiest to break out a sub-lemma first:
*)

(** **** Exercise: 2 stars, standard (sorted_merge1)  *)
Lemma sorted_merge1 : forall x x1 l1 x2 l2,
    x <= x1 -> x <= x2 -> 
    sorted (merge (x1::l1) (x2::l2)) ->
    sorted (x :: merge (x1::l1) (x2::l2)).
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 4 stars, standard (sorted_merge)  *)
Lemma sorted_merge : forall l1, sorted l1 ->
                     forall l2, sorted l2 ->
                     sorted (merge l1 l2).
Proof.
  (* Hint: This is one unusual case where it is _much_ easier to do induction on 
     [l1] rather than on [sorted l1]. You will also need to do
     nested inductions on [l2]. *)
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard (mergesort_sorts)  *)
Lemma mergesort_sorts: forall l, sorted (mergesort l).
Proof. 
  apply mergesort_ind; intros. (* Note that we use the special induction principle. *)
(* FILL IN HERE *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** Correctness: Permutation *)

(** Finally, we must show that [mergesort] returns a permutation of its input.

    As usual, the key lemma is for [merge]. 

    Incidentally, you are welcome to import the alternative characterizations
    of permutations as multisets given in [Multiset] or [BagPerm] 
    and use that instead of [Permutation] if you think it will be easier. 
    (I'm not sure!)
*)

(** **** Exercise: 3 stars, advanced (merge_perm)  *)
Lemma merge_perm: forall (l1 l2: list nat),
    Permutation (l1 ++ l2) (merge l1 l2).
Proof. 
  (* Hint: A nested induction on [l2] is required. *)
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, advanced (mergesort_perm)  *)
Lemma mergesort_perm: forall l, Permutation l (mergesort l).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** Putting it all together: *)

Theorem mergesort_correct:
  is_a_sorting_algorithm mergesort.
Proof.
  split.
  apply mergesort_perm.
  apply mergesort_sorts.
Qed.

(** $Date$ *)

(* 2020-08-07 17:08 *)
