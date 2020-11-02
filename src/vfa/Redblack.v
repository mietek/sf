(** * Redblack: Red-Black Trees *)

(** Red-black trees are a kind of _balanced_ binary search tree (BST).
    Keeping the tree balanced ensures that the worst-case running
    time of operations is logarithmic rather than linear. *)

(** This chapter uses Okasaki's algorithms for red-black trees.
    If you don't recall those or haven't seem them in a while, read one
    of the following:

    - Red-Black Trees in a Functional Setting, by Chris Okasaki.
      _Journal of Functional Programming_, 9(4):471-477, July 1999.
      Available from https://doi.org/10.1017/S0956796899003494.
      Archived at
      https://web.archive.org/web/20070926220746/http://www.eecs.usma.edu/webs/people/okasaki/jfp99.ps.

    - _Purely Functional Data Structures_, by Chris Okasaki. Section
      3.3.  Cambridge University Press, 1998.

    You can also consult Wikipedia or other standard textbooks, though
    they are likely to use different, imperative implementations. *)

(** This chapter is based on the Coq standard library module
    [MSetRBT], which can be found at
    [https://coq.inria.fr/distrib/current/stdlib/Coq.MSets.MSetRBT.html].
    The design decisions for that module are described in the
    following paper:

    - Efficient Verified Red-Black Trees, by Andrew W. Appel,
      September 2011.  Available from
      http://www.cs.princeton.edu/~appel/papers/redblack.pdf.  *)

From Coq Require Import String.
From Coq Require Import Logic.FunctionalExtensionality.
From VFA Require Import Perm.
From VFA Require Import Extract.
Open Scope Z_scope.

(* ################################################################# *)
(** * Implementation *)

(** A [Section] enables declaration of some [Variable]s, which are in
    scope throughout. That saves us from having to write [V] and
    [default] as arguments to most of the definitions in the
    chapter. The variables do get inserted by Coq as arguments after
    the section is closed. *)

Section ValueType.

  Variable V : Type.
  Variable default : V.

  (** We use the [int] type axiomatized in [Extract] as the key
      type. *)
  Definition key := int.

  Inductive color := Red | Black.

  Inductive tree : Type :=
  | E : tree
  | T : color -> tree -> key -> V -> tree -> tree.

  Definition empty_tree : tree :=
    E.

  (** The [lookup] implementation for red-black trees is exactly the same
      as the [lookup] for BSTs, except that the [T] constructor
      carries a [color] component that is ignored. *)

  
  Fixpoint lookup (x: key) (t : tree) : V :=
    match t with
    | E => default
    | T _ tl k v tr => if ltb x k then lookup x tl
                      else if ltb k x then lookup x tr
                           else v
    end.

  (** We won't explain the [insert] algorithm here; read Okasaki's
      work if you want to understand it.  In fact, you'll need very
      little understanding of it to follow along with the verification
      below. It uses [balance] and [ins] as helpers:

      - [ins] recurses down the tree to find where to insert, and is
        mostly the same as the BST [insert] algorithm.

      - [balance] takes care of rebalancing the tree on the way back
        up. *)

  
  Definition balance (rb : color) (t1 : tree) (k : key) (vk : V) (t2 : tree) : tree :=
    match rb with
    | Red => T Red t1 k vk t2
    | _ => match t1 with
          | T Red (T Red a x vx b) y vy c =>
            T Red (T Black a x vx b) y vy (T Black c k vk t2)
          | T Red a x vx (T Red b y vy c) =>
            T Red (T Black a x vx b) y vy (T Black c k vk t2)
          | a => match t2 with
                | T Red (T Red b y vy c) z vz d =>
	          T Red (T Black t1 k vk b) y vy (T Black c z vz d)
                | T Red b y vy (T Red c z vz d)  =>
	          T Red (T Black t1 k vk b) y vy (T Black c z vz d)
                | _ => T Black t1 k vk t2
                end
          end
    end.

  Fixpoint ins (x : key) (vx : V) (t : tree) : tree :=
    match t with
    | E => T Red E x vx E
    | T c a y vy b => if ltb x y then balance c (ins x vx a) y vy b
                      else if ltb y x then balance c a y vy (ins x vx b)
                           else T c a x vx b
    end.

  Definition make_black (t : tree) : tree :=
    match t with
    | E => E
    | T _ a x vx b => T Black a x vx b
    end.

  Definition insert (x : key) (vx : V) (t : tree) :=
    make_black (ins x vx t).

  (** The [elements] implementation is the same as for BSTs, except that it
      ignores colors. *)

  
  Fixpoint elements_tr (t : tree) (acc: list (key * V)) : list (key * V) :=
    match t with
    | E => acc
    | T _ l k v r => elements_tr l ((k, v) :: elements_tr r acc)
    end.

  Definition elements (t : tree) : list (key * V) :=
    elements_tr t [].

  (* ###################################################################### *)
  (** * Case-Analysis Automation *)

  (** Before verifying the correctness of our red-black tree
      implementation, let's warm up by proving that the result of any
      [insert] is a nonempty tree. *)

  
  Lemma ins_not_E : forall (x : key) (vx : V) (t : tree),
      ins x vx t <> E.
  Proof.
    intros. destruct t; simpl.
    discriminate.

    (* Let's [destruct] on the topmost case, [ltb x k]. We can use
       [destruct] instead of [bdestruct] because we don't need to know
       whether [x < k] or [x >= k]. *)

    destruct (ltb x k).
    unfold balance.

    (* A huge goal!  The proof of this goal begins by matching
       against a color. *)

    destruct c.
    discriminate.

    (* Another [match], this time against a tree. *)

    destruct (ins x vx t1).

    (* Another [match] against a tree. *)

    destruct t2.
    discriminate.

    (* Yet another [match]. This pattern deserves automation.  The
       following tactic applies [destruct] whenever the current goal
       is a [match] against a color or a tree. *)

    
    match goal with
    | |- match ?c with Red => _ | Black => _  end <> _ => destruct c
    | |- match ?t with E => _ | T _ _ _ _ _ => _ end  <> _=> destruct t
    end.

    (* Let's apply that tactic repeatedly. *)

    repeat
      match goal with
      | |- match ?c with Red => _ | Black => _  end <> _ => destruct c
      | |- match ?t with E => _ | T _ _ _ _ _ => _ end  <> _=> destruct t
      end.

    (* Now we're down to a base case. *)

    discriminate.

    (* And another base case. We could match against those, too. *)

    match goal with
    | |- T _ _ _ _ _ <> E => discriminate
    end.

    (* Let's restart the proof to incorporate this automation. *)

  Abort.

  Lemma ins_not_E : forall (x : key) (vx : V) (t : tree),
      ins x vx t <> E.
  Proof.
    intros. destruct t; simpl.
    - discriminate.
    - unfold balance.
      repeat
        match goal with
        | |- (if ?x then _ else _) <> _ => destruct x
        | |- match ?c with Red => _ | Black => _  end <> _=> destruct c
        | |- match ?t with E => _ | T _ _ _ _ _ => _ end  <> _=> destruct t
        | |- T _ _ _ _ _ <> E => discriminate
        end.
  Qed.

  (** This automation of case analysis will be quite useful in the rest
      of our development. *)

  (* ###################################################################### *)
  (** * The BST Invariant *)

  (** The BST invariant is mostly the same for red-black trees as it
      was for ordinary BSTs as defined in [SearchTree].  We adapt
      it by ignoring the color of each node, and changing from [nat]
      keys to [int]. *)

  
  (** [ForallT P t] holds if [P k v] holds for every [(k, v)] node of
      tree [t]. *)

  Fixpoint ForallT (P: int -> V -> Prop) (t: tree) : Prop :=
    match t with
    | E => True
    | T c l k v r => P k v /\ ForallT P l /\ ForallT P r
    end.

  Inductive BST : tree -> Prop :=
  | ST_E : BST E
  | ST_T : forall (c : color) (l : tree) (k : key) (v : V) (r : tree),
      ForallT (fun k' _ => (Abs k') < (Abs k)) l ->
      ForallT (fun k' _ => (Abs k') > (Abs k)) r ->
      BST l ->
      BST r ->
      BST (T c l k v r).

  Lemma empty_tree_BST:  BST empty_tree.
  Proof.
    unfold empty_tree. constructor.
  Qed.

  (** Let's show that [insert] preserves the BST invariant, that is: *)

  Theorem insert_BST : forall t v k,
      BST t ->
      BST (insert k v t).
  Abort.

  (** It will take quite a bit of work, but automation will help. *)

  (** First, we show that if a non-empty tree would be a BST, then the
      balanced version of it is also a BST: *)

  Lemma balance_BST: forall (c : color) (l : tree) (k : key) (v : V) (r : tree),
      ForallT (fun k' _ => (Abs k') < (Abs k)) l ->
      ForallT (fun k' _ => (Abs k') > (Abs k)) r ->
      BST l ->
      BST r ->
      BST (balance c l k v r).
  Proof.
    intros c l k v r PL PR BL BR. unfold balance.

    repeat
      match goal with
      | |- BST (match ?c with Red => _ | Black => _ end)  => destruct c
      | |- BST (match ?t with E => _ | T _ _ _ _ _ => _ end)  => destruct t
      end.

    (* 58 cases remaining. *)

    - constructor. assumption. assumption. assumption. assumption.
    - constructor; auto.
    - constructor; auto.
    - (* Now the tree gets bigger, and the proof gets more complicated. *)
      constructor; auto.

      + simpl in *. repeat split.
        (* The intro pattern [?] means to let Coq choose the name. *)
        destruct PR as [? _]. omega.

      + simpl in *. repeat split.
        * inv BR. simpl in *. destruct H5 as [? _]. omega.
        * inv BR. simpl in *. destruct H5 as [_ [? _]]. auto.
        * inv BR. simpl in *. destruct H5 as [_ [_ ?]]. auto.

      + constructor; auto.

      + inv BR. inv H7. constructor; auto.

    - constructor; auto.

    - (* 53 cases remain. This could go on for a while... *)

  Abort.

  (** Let's use some of what we discovered above to automate.
      Whenever we have a subgoal of the form

        ForallT _ (T _ _ _ _ _)

      we can split it.  Whenever we have a hypothesis of the form

        BST (T _ _ _ _ _)

      we can invert it.  And with a hypothesis

        ForallT _ (T _ _ _ _ _)

      we can simplify then destruct it.  Actually, the simplification
      is optional -- Coq will do the destruct without needing the
      simplification.  Anything else seems able to be finished with
      [constructor], [auto], and [omega].  Let's see how far that can
      take us...
   *)

  
  Lemma balance_BST: forall (c : color) (l : tree) (k : key) (v : V) (r : tree),
      ForallT (fun k' _ => (Abs k') < (Abs k)) l ->
      ForallT (fun k' _ => (Abs k') > (Abs k)) r ->
      BST l ->
      BST r ->
      BST (balance c l k v r).
  Proof.
    intros. unfold balance.

    repeat
      (match goal with
       |  |- BST (match ?c with Red => _ | Black => _ end)  => destruct c
       |  |- BST (match ?t with E => _ | T _ _ _ _ _ => _ end)  => destruct t
       |  |- ForallT _ (T _ _ _ _ _) => repeat split
       |  H: ForallT _ (T _ _ _ _ _) |- _ => destruct H as [? [? ?] ]
       |  H: BST (T _ _ _ _ _) |- _ => inv H
       end;
       (try constructor; auto; try omega)).

  (** 41 cases remain.  It's a little disappointing that we didn't clear
      more of them.  Let's look at why are we stuck.

      All the remaining subgoals appear to be about proving an inequality
      over all the nodes of a subtree.  For example, the first subgoal
      follows from the hypotheses

        ForallT (fun (k' : int) (_ : V) => Abs k' > Abs k0) r2
        Abs k1 < Abs k0

      The other goals look similar. *)

  
  Abort.

  (** To make progress, we can set up some helper lemmas. *)

  Lemma ForallT_imp : forall (P Q : int -> V -> Prop) t,
      ForallT P t ->
      (forall k v, P k v -> Q k v) ->
      ForallT Q t.
  Proof.
    induction t; intros.
    - auto.
    - destruct H as [? [? ?]]. repeat split; auto.
  Qed.

  Lemma ForallT_greater : forall t k k0,
      ForallT (fun k' _ => Abs k' > Abs k) t  ->
      Abs k > Abs k0 ->
      ForallT (fun k' _ => Abs k' > Abs k0) t.
  Proof.
    intros. eapply ForallT_imp; eauto.
    intros. simpl in H1. omega.
  Qed.

  Lemma ForallT_less : forall t k k0,
      ForallT (fun k' _ => Abs k' < Abs k) t  ->
      Abs k < Abs k0 ->
      ForallT (fun k' _ => Abs k' < Abs k0) t.
  Proof.
    intros; eapply ForallT_imp; eauto.
    intros. simpl in H1. omega.
  Qed.

  (** Now we can return to automating the proof. *)

  Lemma balance_BST: forall (c : color) (l : tree) (k : key) (v : V) (r : tree),
      ForallT (fun k' _ => (Abs k') < (Abs k)) l ->
      ForallT (fun k' _ => (Abs k') > (Abs k)) r ->
      BST l ->
      BST r ->
      BST (balance c l k v r).
  Proof.
    intros. unfold balance.

    repeat
      (match goal with
       |  |- BST  (match ?c with Red => _ | Black => _ end)  => destruct c
       |  |- BST  (match ?s with E => _ | T _ _ _ _ _ => _ end)  => destruct s
       |  |- ForallT _ (T _ _ _ _ _) => repeat split
       |  H: ForallT _ (T _ _ _ _ _) |- _ => destruct H as [? [? ?] ]
       |  H: BST (T _ _ _ _ _) |- _ => inv H
       end;
       (try constructor; auto; try omega)).

    (* [all: t] applies [t] to every subgoal. *)
    all: try eapply ForallT_greater; try eapply ForallT_less; eauto; try omega.
  Qed.

    (** **** Exercise: 2 stars, standard (balanceP)  *)

  (** Prove that [balance] preserves [ForallT P]. Use proof automation
      with [match goal] and/or [all:].*)

  Lemma balanceP : forall (P : key -> V -> Prop) (c : color) (l r : tree) (k : key) (v : V),
      ForallT P l ->
      ForallT P r ->
      P k v ->
      ForallT P (balance c l k v r).
  Proof.
    (* FILL IN HERE *) Admitted.

  (** [] *)

  (** **** Exercise: 2 stars, standard (insP)  *)

  (** Prove that [ins] preserves [ForallT P]. Hint: proceed by induction on [t].
      Use the previous lemma. There's no need for automated case analysis. *)

  Lemma insP : forall (P : key -> V -> Prop) (t : tree) (k : key) (v : V),
      ForallT P t ->
      P k v ->
      ForallT P (ins k v t).
  Proof.
    (* FILL IN HERE *) Admitted.

  (** [] *)

  (** **** Exercise: 3 stars, standard (ins_BST)  *)

  (** Prove that [ins] maintains [BST].  Proceed by induction on the evidence
      that [t] is a BST.  You don't need any automated case analysis. *)

  Lemma ins_BST : forall (t : tree) (k : key) (v : V),
      BST t ->
      BST (ins k v t).
  Proof.
    (* FILL IN HERE *) Admitted.

  (** [] *)

  
  
  (** **** Exercise: 2 stars, standard (insert_BST)  *)

  (** Prove the main theorem: [insert] preserves [BST]. *)

  Theorem insert_BST : forall t v k,
      BST t ->
      BST (insert k v t).
  Proof.
    (* FILL IN HERE *) Admitted.
  (** [] *)

  (* ###################################################################### *)
  (** * Verification *)

  (** We now verify that the equational specification of maps holds for
      red-black trees:

        lookup k empty_tree = default
        lookup k (insert k v t) = v
        lookup k' (insert k v t) = lookup k' t       if k <> k'

      The first equation is trivial to verify. *)

  Lemma lookup_empty : forall k, lookup k empty_tree = default.
  Proof. auto. Qed.

  (** The next two equations are more challenging because of [balance]. *)

    (** **** Exercise: 4 stars, standard (balance_lookup)  *)

  (** Prove that [balance] preserves the result of [lookup] on
      non-empty trees. Hint: automate the case analysis similarly to
      [balance_BST]. *)

  Lemma balance_lookup: forall (c : color) (k k' : key) (v : V) (l r : tree),
      BST l ->
      BST r ->
      ForallT (fun k' _ => Abs k' < Abs k) l ->
      ForallT (fun k' _ => Abs k' > Abs k) r ->
      lookup k' (balance c l k v r) =
      if Abs k' <? Abs k
      then lookup k' l
      else if Abs k' >? Abs k
           then lookup k' r
           else v.
  Proof.
    (* FILL IN HERE *) Admitted.

  (** [] *)

  (** **** Exercise: 3 stars, standard (lookup_ins_eq)  *)

  (** Verify the second equation, though for [ins] rather than
      [insert].  Proceed by induction on the evidence that [t] is a
      [BST].  Note that precondition [BST t] will be essential in your
      proof, unlike the ordinary BST's we saw in [SearchTree].

      Hint: no automation of case analysis is needed; rely on the
      lemmas we've already proved above about [balance] and [ins]. *)

  Lemma lookup_ins_eq: forall (t : tree) (k : key) (v : V),
      BST t ->
      lookup k (ins k v t) = v.
  Proof.
    (* FILL IN HERE *) Admitted.

  (** [] *)

  (** **** Exercise: 3 stars, standard (lookup_ins_neq)  *)

  (** Verify the third equation, again for [ins] instead of [insert].
      The same hints as for the second equation hold.  *)

  Theorem lookup_ins_neq: forall (t : tree) (k k' : key) (v : V),
      BST t ->
      k <> k' ->
      lookup k' (ins k v t) = lookup k' t.
  Proof.
    (* FILL IN HERE *) Admitted.

  (** [] *)

  (** Finally, finish verify the second and third equations.  The
      proofs are almost identical.  *)

  
  
  (** **** Exercise: 3 stars, standard (lookup_insert)  *)

  Theorem lookup_insert_eq : forall (t : tree) (k : key) (v : V),
      BST t ->
      lookup k (insert k v t) = v.
  Proof.
    (* FILL IN HERE *) Admitted.

  Theorem lookup_insert_neq: forall (t : tree) (k k' : key) (v : V),
      BST t ->
      k <> k' ->
      lookup k' (insert k v t) = lookup k' t.
  Proof.
    (* FILL IN HERE *) Admitted.

    
  (** [] *)

    (** That concludes the verification of the map equations for red-black trees.
      We have proved these main theorems: *)

  Check empty_tree_BST : BST empty_tree.

  Check insert_BST :
    forall (t : tree) (v : V) (k : key),
      BST t -> BST (insert k v t).

  Check lookup_empty :
    forall k : key,
      lookup k empty_tree = default.

  Check lookup_insert_eq :
    forall (t : tree) (k : key) (v : V),
      BST t -> lookup k (insert k v t) = v.

  Check lookup_insert_neq :
    forall (t : tree) (k k' : key) (v : V),
      BST t ->
      k <> k' ->
      lookup k' (insert k v t) = lookup k' t.

  (** We could now proceed to reprove all the facts about [elements]
      that we developed in [SearchTree].  But since [elements]
      does not not pay attention to colors, and does not rebalance the
      tree, these proofs should be a simple copy-paste from that
      chapter, with only minor edits.  This would be an uninteresting
      exercise, so we don't pursue it here. *)
  
  (* ###################################################################### *)
  (** * Efficiency *)

  (** Red-black trees are more efficient than ordinary search trees,
      because red-black trees stay balanced.  The [insert] operation
      ensures that these _red-black invariants_ hold: *)

  
  (** - Local Invariant: No red node has a red child.

      - Global Invariant: Every path from the root to a leaf has the
        same number of black nodes. *)

  (** Together these invariants guarantee that no leaf is more
      than twice as deep as another leaf, a property that we will here
      call _approximately balanced_.  The maximum depth of a node is
      therefore [2 log N], so the running-time of [insert] and
      [lookup] is [O(log N)], where [N] is the number of nodes in the
      tree.

      Coq does not have a formal time--cost model for its execution,
      so we cannot verify that logarithmic running time in Coq.  But
      we can prove that the trees are approximately balanced. *)

  (** These ensure that the tree remains approximately balanced. *)

  (** Relation [RB], below, formalizes the red-black
      invariants. Proposition [RB t c n] holds when [t] satisfies the
      red-black invariants, assuming that [c] is the color of [t]'s
      parent, and [n] is the black height that [t] is supposed to
      have.

      If [t] happens to have no parent (i.e., it is the entire tree),
      then it will be colored black by [insert], so it won't actually
      matter what color its (non-existent) parent might purportedly
      have: whether red or black, it can't violate the local
      invariant.

      If [t] is a leaf, then it likewise won't matter what its parent
      color is, and its black height must be zero. *)

  
  Inductive RB : tree -> color -> nat -> Prop :=
  | RB_leaf: forall (c : color), RB E c 0
  | RB_r: forall (l r : tree) (k : key) (v : V) (n : nat),
      RB l Red n ->
      RB r Red n ->
      RB (T Red l k v r) Black n
  | RB_b: forall (c : color) (l r : tree) (k : key) (v : V) (n : nat),
      RB l Black n ->
      RB r Black n ->
      RB (T Black l k v r) c (S n).

    (** **** Exercise: 2 stars, standard (RB_blacken_parent)  *)

  (** Prove that blackening a parent would preserve the red-black
      invariants. *)

  Lemma RB_blacken_parent : forall (t : tree) (n : nat),
      RB t Red n -> RB t Black n.
  Proof.
    (* FILL IN HERE *) Admitted.

  (** [] *)

  (** **** Exercise: 2 stars, standard (RB_blacken_root)  *)

  (** Prove that blackening a subtree root (whose hypothetical parent
      is black) would preserve the red-black invariants, though the
      black height of the subtree might change (and the color of the
      parent would need to become red). *)

  Lemma RB_blacken_root : forall (t : tree) (n : nat),
      RB t Black n ->
      exists (n' : nat), RB (make_black t) Red n'.
  Proof.
    (* FILL IN HERE *) Admitted.

  (** [] *)

  (** Relation [NearlyRB] expresses, "the tree is a red-black tree,
      except that it's nonempty and it is permitted to have two
      consecutive red nodes at the root only."  *)

  Inductive NearlyRB : tree -> nat -> Prop :=
  | NearlyRB_r : forall (l r : tree) (k : key) (v : V) (n : nat),
      RB l Black n ->
      RB r Black n ->
      NearlyRB (T Red l k v r) n
  | NearlyRB_b : forall (l r : tree) (k : key) (v : V) (n : nat),
      RB l Black n ->
      RB r Black n ->
      NearlyRB (T Black l k v r) (S n).

  (** **** Exercise: 5 stars, standard (ins_RB)  *)

  (** Prove that [ins] creates a tree that is either red-black or
      nearly so, depending on what the parent's color was.  You will
      need significant case-analysis automation in a similar style to
      the proofs of [ins_not_E] and [balance_lookup]. *)

  

  Lemma ins_RB : forall (k : key) (v : V) (t : tree) (n : nat),
      (RB t Black n -> NearlyRB (ins k v t) n) /\
      (RB t Red n -> RB (ins k v t) Black n).
  Proof.
    induction t; intro n; simpl; split; intros; inv H; repeat constructor; auto.
    * destruct (IHt1 n); clear IHt1.
      destruct (IHt2 n); clear IHt2.
      specialize (H0 H6).
      specialize (H2 H7).
      clear H H1.
      unfold balance.

      (* FILL IN HERE *) Admitted.

  (** [] *)

  (** Therefore, [ins] produces a red-black tree when given one as
      input -- though the parent color changes. *)
  Corollary ins_red : forall (t : tree) (k : key) (v : V) (n : nat),
      (RB t Red n -> RB (ins k v t) Black n).
  Proof.
    intros. apply ins_RB. assumption.
  Qed.
  
  
  (** **** Exercise: 2 stars, standard (insert_RB)  *)

  (** Prove that [insert] produces a red-black tree when given one as
      input.  This can be done entirely with lemmas already proved. *)

  
  Lemma insert_RB : forall (t : tree) (k : key) (v : V) (n : nat),
      RB t Red n ->
      exists (n' : nat), RB (insert k v t) Red n'.
  Proof.
    (* FILL IN HERE *) Admitted.

  (** [] *)

    (** **** Exercise: 4 stars, advanced (redblack_bound)  *)

  (** To confirm that red-black trees are approximately balanced,
      define functions to compute the height (i.e., maximum depth) and
      minimum depth of a red-black tree, and prove that the height is
      bounded by twice the minimum depth, possibly plus 1.  Hints:

      - Prove two auxiliary lemmas, one about height and the other
        about mindepth, and then combine them to get the result.  The
        lemma about height will need a slightly complicated induction
        hypothesis for the proof to go through.

      - Depending on how you defined [height] and [mindepth], the
        tactic [zify] (defined in the standard library
        [Coq.omega.PreOmega]) may be useful as a preliminary to using
        [omega] when proving these lemmas. *)

  Fixpoint height (t : tree) : nat
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

  Fixpoint mindepth (t : tree) : nat
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

  

  Lemma redblack_balanced : forall t c n,
      RB t c n ->
      (height t <= 2 * mindepth t + 1)%nat.
  Proof.
    (* FILL IN HERE *) Admitted.

  (* Do not modify the following line: *)
Definition manual_grade_for_redblack_bound : option (nat*string) := None.

  (** [] *)

  
End ValueType.

(* ################################################################# *)
(** * Performance of Extracted Code *)

(** We can extract the red-black tree implementation: *)

Extraction "redblack.ml" empty_tree insert lookup elements.

(** Run it in the OCaml top level with these commands:

      #use "redblack.ml";;
      #use "test_searchtree.ml";;

    On a recent machine with a 2.9 GHz Intel Core i9 that prints:

      Insert and lookup 1000000 random integers in 0.860663 seconds.
      Insert and lookup 20000 random integers in 0.007908 seconds.
      Insert and lookup 20000 consecutive integers in 0.004668 seconds.

    That execution uses the bytecode interpreter.  The native compiler
    will have better performance:

      $ ocamlopt -c redblack.mli redblack.ml
      $ ocamlopt redblack.cmx -open Redblack test_searchtree.ml -o test_redblack
      $ ./test_redblack

On the same machine that prints,

      Insert and lookup 1000000 random integers in 0.475669 seconds.
      Insert and lookup 20000 random integers in 0.00312 seconds.
      Insert and lookup 20000 consecutive integers in 0.001183 seconds.
*)

(** The benchmark measurements above (and in [Extract])
    demonstrate the following:

    - On random insertions, red-black trees are about the same as
      ordinary BSTs.

    - On consecutive insertions, red-black trees are _much_ faster
      than ordinary BSTs.

    - Red-black trees are about as fast on consecutive insertions as
      on random. *)

(* 2020-08-07 17:08 *)
