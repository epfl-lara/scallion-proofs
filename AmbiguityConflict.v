Require Import Coq.Lists.List.
Import ListNotations.

Require Export Parser.HasConflictInd.

Lemma matches_nil_unicity_helper:
  forall A (s: Syntax A) ts v1,
    matches s ts v1 ->
    ts = [] ->
    ~ has_conflict_ind s ->
    forall v2,
      matches s [] v2 ->
      v1 = v2.
Proof.
  induction 1;
    repeat light || invert_matches || f_equal || lists || invert_constructor_equalities;
    eauto with matches has_conflict_ind exfalso.
Qed.

Lemma matches_nil_unicity:
  forall A (s: Syntax A) v1 v2,
    ~ has_conflict_ind s ->
    matches s [] v1 ->
    matches s [] v2 ->
    v1 = v2.
Proof.
  eauto using matches_nil_unicity_helper.
Qed.

Ltac matches_nil_unicity :=
  match goal with
  | H: has_conflict_ind ?s -> False, H1: matches ?s [] ?v1, H2: matches ?s [] ?v2 |- _ =>
    pose proof (matches_nil_unicity _ _ _ _ H H1 H2); clear H1
  end.

Ltac matches_nil_unicity2 :=
  match goal with
  | H1: matches ?s [] ?v1, H2: matches ?s [] ?v2 |- _ =>
    unshelve epose proof (matches_nil_unicity _ _ _ _ _ H1 H2); clear H1
  end.
