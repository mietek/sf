(** * SfLib: Software Foundations Library *)

(** Here we collect together a few useful definitions from earlier
    chapters that are not provided as part of the Coq standard
    library.  Later chapters will [Import] or [Export] just this file,
    instead of cluttering the top-level environment with all the
    examples and false starts in those files. *)

Definition admit {T: Type} : T.  Admitted.

Tactic Notation "solve_by_inversion_step" tactic(t) :=
  match goal with
  | H : _ |- _ => solve [ inversion H; subst; t ]
  end
  || fail "because the goal is not solvable by inversion.".

Tactic Notation "solve" "by" "inversion" "1" :=
  solve_by_inversion_step idtac.
Tactic Notation "solve" "by" "inversion" "2" :=
  solve_by_inversion_step (solve by inversion 1).
Tactic Notation "solve" "by" "inversion" "3" :=
  solve_by_inversion_step (solve by inversion 2).
Tactic Notation "solve" "by" "inversion" :=
  solve by inversion 1.

(** $Date: 2016-05-24 14:00:08 -0400 (Tue, 24 May 2016) $ *)
