(** * ImpCEvalFun: Evaluation Function for Imp *)

(* #################################### *)
(** * Evaluation Function *)

Require Import Imp.

(** Here's a first try at an evaluation function for commands,
    omitting [WHILE]. *)

Fixpoint ceval_step1 (st : state) (c : com) : state :=
  match c with 
    | SKIP => 
        st
    | l ::= a1 => 
        update st l (aeval st a1)
    | c1 ;; c2 => 
        let st' := ceval_step1 st c1 in
        ceval_step1 st' c2
    | IFB b THEN c1 ELSE c2 FI => 
        if (beval st b) 
          then ceval_step1 st c1 
          else ceval_step1 st c2
    | WHILE b1 DO c1 END => 
        st  (* bogus *)
  end.

(** In a traditional functional programming language like ML or
    Haskell we could write the WHILE case as follows:
<<
    | WHILE b1 DO c1 END => 
        if (beval st b1) 
          then ceval_step1 st (c1;; WHILE b1 DO c1 END)
          else st 
>>
    Coq doesn't accept such a definition ([Error: Cannot guess
    decreasing argument of fix]) because the function we want to
    define is not guaranteed to terminate. Indeed, the changed
    [ceval_step1] function applied to the [loop] program from [Imp.v] would
    never terminate. Since Coq is not just a functional programming
    language, but also a consistent logic, any potentially
    non-terminating function needs to be rejected. Here is an
    invalid(!) Coq program showing what would go wrong if Coq allowed
    non-terminating recursive functions:
<<
     Fixpoint loop_false (n : nat) : False := loop_false n.
>>
    That is, propositions like [False] would become
    provable (e.g. [loop_false 0] would be a proof of [False]), which
    would be a disaster for Coq's logical consistency.

    Thus, because it doesn't terminate on all inputs, the full version
    of [ceval_step1] cannot be written in Coq -- at least not
    without one additional trick... *)


(** Second try, using an extra numeric argument as a "step index" to
    ensure that evaluation always terminates. *)

Fixpoint ceval_step2 (st : state) (c : com) (i : nat) : state :=
  match i with 
  | O => empty_state
  | S i' =>
    match c with 
      | SKIP => 
          st
      | l ::= a1 => 
          update st l (aeval st a1)
      | c1 ;; c2 => 
          let st' := ceval_step2 st c1 i' in
          ceval_step2 st' c2 i' 
      | IFB b THEN c1 ELSE c2 FI => 
          if (beval st b) 
            then ceval_step2 st c1 i' 
            else ceval_step2 st c2 i'
      | WHILE b1 DO c1 END => 
          if (beval st b1) 
          then let st' := ceval_step2 st c1 i' in
               ceval_step2 st' c i'
          else st
    end
  end.

(** _Note_: It is tempting to think that the index [i] here is
    counting the "number of steps of evaluation."  But if you look
    closely you'll see that this is not the case: for example, in the
    rule for sequencing, the same [i] is passed to both recursive
    calls.  Understanding the exact way that [i] is treated will be
    important in the proof of [ceval__ceval_step], which is given as
    an exercise below. *)

(** Third try, returning an [option state] instead of just a [state]
    so that we can distinguish between normal and abnormal
    termination. *)

Fixpoint ceval_step3 (st : state) (c : com) (i : nat) 
                    : option state :=
  match i with 
  | O => None
  | S i' =>
    match c with 
      | SKIP => 
          Some st
      | l ::= a1 => 
          Some (update st l (aeval st a1))
      | c1 ;; c2 => 
          match (ceval_step3 st c1 i') with
          | Some st' => ceval_step3 st' c2 i'
          | None => None
          end
      | IFB b THEN c1 ELSE c2 FI => 
          if (beval st b) 
            then ceval_step3 st c1 i' 
            else ceval_step3 st c2 i'
      | WHILE b1 DO c1 END => 
          if (beval st b1)           
          then match (ceval_step3 st c1 i') with
               | Some st' => ceval_step3 st' c i'
               | None => None
               end
          else Some st
    end
  end.

(** We can improve the readability of this definition by introducing a
    bit of auxiliary notation to hide the "plumbing" involved in
    repeatedly matching against optional states. *)

Notation "'LETOPT' x <== e1 'IN' e2" 
   := (match e1 with
         | Some x => e2
         | None => None
       end)
   (right associativity, at level 60).

Fixpoint ceval_step (st : state) (c : com) (i : nat) 
                    : option state :=
  match i with 
  | O => None
  | S i' =>
    match c with 
      | SKIP => 
          Some st
      | l ::= a1 => 
          Some (update st l (aeval st a1))
      | c1 ;; c2 => 
          LETOPT st' <== ceval_step st c1 i' IN
          ceval_step st' c2 i'
      | IFB b THEN c1 ELSE c2 FI => 
          if (beval st b) 
            then ceval_step st c1 i' 
            else ceval_step st c2 i'
      | WHILE b1 DO c1 END => 
          if (beval st b1)           
          then LETOPT st' <== ceval_step st c1 i' IN
               ceval_step st' c i'
          else Some st
    end
  end.

Definition test_ceval (st:state) (c:com) := 
  match ceval_step st c 500 with
  | None    => None
  | Some st => Some (st X, st Y, st Z)
  end.  

(* Eval compute in 
     (test_ceval empty_state 
         (X ::= ANum 2;;
          IFB BLe (AId X) (ANum 1)
            THEN Y ::= ANum 3 
            ELSE Z ::= ANum 4
          FI)).
   ====>
      Some (2, 0, 4)   *)

(** **** Exercise: 2 stars (pup_to_n)  *)
(** Write an Imp program that sums the numbers from [1] to
   [X] (inclusive: [1 + 2 + ... + X]) in the variable [Y].  Make sure
   your solution satisfies the test that follows. *)

Definition pup_to_n : com := 
  (* FILL IN HERE *) admit.

(* 
Example pup_to_n_1 : 
  test_ceval (update empty_state X 5) pup_to_n
  = Some (0, 15, 0).
Proof. reflexivity. Qed.
*)
(** [] *)

(** **** Exercise: 2 stars, optional (peven)  *)
(** Write a [While] program that sets [Z] to [0] if [X] is even and
    sets [Z] to [1] otherwise.  Use [ceval_test] to test your
    program. *)

(* FILL IN HERE *)
(** [] *)

(* ################################################################ *)
(** * Equivalence of Relational and Step-Indexed Evaluation *)

(** As with arithmetic and boolean expressions, we'd hope that
    the two alternative definitions of evaluation actually boil down
    to the same thing.  This section shows that this is the case.
    Make sure you understand the statements of the theorems and can
    follow the structure of the proofs. *)

Theorem ceval_step__ceval: forall c st st',
      (exists i, ceval_step st c i = Some st') ->
      c / st || st'.
Proof.
  intros c st st' H.
  inversion H as [i E].
  clear H.
  generalize dependent st'.
  generalize dependent st.
  generalize dependent c.
  induction i as [| i' ].

  Case "i = 0 -- contradictory".
    intros c st st' H. inversion H.

  Case "i = S i'".
    intros c st st' H.
    com_cases (destruct c) SCase; 
           simpl in H; inversion H; subst; clear H. 
      SCase "SKIP". apply E_Skip.
      SCase "::=". apply E_Ass. reflexivity.

      SCase ";;".
        destruct (ceval_step st c1 i') eqn:Heqr1. 
        SSCase "Evaluation of r1 terminates normally".
          apply E_Seq with s. 
            apply IHi'. rewrite Heqr1. reflexivity.
            apply IHi'. simpl in H1. assumption.
        SSCase "Otherwise -- contradiction".
          inversion H1.

      SCase "IFB". 
        destruct (beval st b) eqn:Heqr.
        SSCase "r = true".
          apply E_IfTrue. rewrite Heqr. reflexivity.
          apply IHi'. assumption.
        SSCase "r = false".
          apply E_IfFalse. rewrite Heqr. reflexivity.
          apply IHi'. assumption.

      SCase "WHILE". destruct (beval st b) eqn :Heqr.
        SSCase "r = true". 
         destruct (ceval_step st c i') eqn:Heqr1.
          SSSCase "r1 = Some s".
            apply E_WhileLoop with s. rewrite Heqr. reflexivity.
            apply IHi'. rewrite Heqr1. reflexivity. 
            apply IHi'. simpl in H1. assumption.
          SSSCase "r1 = None".
            inversion H1.
        SSCase "r = false".
          inversion H1. 
          apply E_WhileEnd. 
          rewrite <- Heqr. subst. reflexivity.  Qed.

(** **** Exercise: 4 stars (ceval_step__ceval_inf)  *)
(** Write an informal proof of [ceval_step__ceval], following the
    usual template.  (The template for case analysis on an inductively
    defined value should look the same as for induction, except that
    there is no induction hypothesis.)  Make your proof communicate
    the main ideas to a human reader; do not simply transcribe the
    steps of the formal proof.

(* FILL IN HERE *)
[]
*)

Theorem ceval_step_more: forall i1 i2 st st' c,
  i1 <= i2 -> 
  ceval_step st c i1 = Some st' -> 
  ceval_step st c i2 = Some st'.
Proof. 
induction i1 as [|i1']; intros i2 st st' c Hle Hceval.
  Case "i1 = 0".
    simpl in Hceval. inversion Hceval.
  Case "i1 = S i1'".
    destruct i2 as [|i2']. inversion Hle. 
    assert (Hle': i1' <= i2') by omega.
    com_cases (destruct c) SCase.
    SCase "SKIP".
      simpl in Hceval. inversion Hceval.
      reflexivity.
    SCase "::=".
      simpl in Hceval. inversion Hceval.
      reflexivity.
    SCase ";;".
      simpl in Hceval. simpl. 
      destruct (ceval_step st c1 i1') eqn:Heqst1'o.
      SSCase "st1'o = Some".
        apply (IHi1' i2') in Heqst1'o; try assumption.
        rewrite Heqst1'o. simpl. simpl in Hceval.
        apply (IHi1' i2') in Hceval; try assumption.
      SSCase "st1'o = None".
        inversion Hceval.

    SCase "IFB".
      simpl in Hceval. simpl.
      destruct (beval st b); apply (IHi1' i2') in Hceval; assumption.
    
    SCase "WHILE".
      simpl in Hceval. simpl.
      destruct (beval st b); try assumption. 
      destruct (ceval_step st c i1') eqn: Heqst1'o.
      SSCase "st1'o = Some".
        apply (IHi1' i2') in Heqst1'o; try assumption. 
        rewrite -> Heqst1'o. simpl. simpl in Hceval. 
        apply (IHi1' i2') in Hceval; try assumption.
      SSCase "i1'o = None".
        simpl in Hceval. inversion Hceval.  Qed.

(** **** Exercise: 3 stars (ceval__ceval_step)  *)
(** Finish the following proof.  You'll need [ceval_step_more] in a
    few places, as well as some basic facts about [<=] and [plus]. *)

Theorem ceval__ceval_step: forall c st st',
      c / st || st' ->
      exists i, ceval_step st c i = Some st'.
Proof. 
  intros c st st' Hce.
  ceval_cases (induction Hce) Case.
  (* FILL IN HERE *) Admitted.
(** [] *)

Theorem ceval_and_ceval_step_coincide: forall c st st',
      c / st || st'
  <-> exists i, ceval_step st c i = Some st'.
Proof.
  intros c st st'.
  split. apply ceval__ceval_step. apply ceval_step__ceval.
Qed.

(* ####################################################### *)
(** * Determinism of Evaluation (Simpler Proof) *)

(** Here's a slicker proof showing that the evaluation relation is
    deterministic, using the fact that the relational and step-indexed
    definition of evaluation are the same. *)

Theorem ceval_deterministic' : forall c st st1 st2,
     c / st || st1  ->
     c / st || st2 ->
     st1 = st2.
Proof. 
  intros c st st1 st2 He1 He2.
  apply ceval__ceval_step in He1.
  apply ceval__ceval_step in He2.
  inversion He1 as [i1 E1]. 
  inversion He2 as [i2 E2].
  apply ceval_step_more with (i2 := i1 + i2) in E1.
  apply ceval_step_more with (i2 := i1 + i2) in E2.
  rewrite E1 in E2. inversion E2. reflexivity. 
  omega. omega.  Qed.

(** $Date: 2014-12-31 11:17:56 -0500 (Wed, 31 Dec 2014) $ *)

