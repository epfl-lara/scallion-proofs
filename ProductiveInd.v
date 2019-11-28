Require Import Parser.DescriptionInd.
Require Import Parser.Structures.
Require Import Parser.Matches.
Require Import Parser.ProductiveDescr.

Definition productive_ind { A } (s: Syntax A): Prop := descr_ind productive_descr s tt.

Lemma productive_ind_sound:
  forall A (s: Syntax A),
    productive_ind s ->
    (exists xs v, matches s xs v).
Proof.
  intros.
  induction H; repeat light || options || bools || destruct_match; eauto with matches.
Qed.

Lemma productive_ind_complete:
  forall A (s: Syntax A) xs v,
    matches s xs v ->
    productive_ind s.
Proof.
  unfold productive_ind;
  induction 1;
    repeat light || lists; eauto 3 with descr_ind lights.
Qed.

Lemma productive_ind_correct:
  forall A (s: Syntax A),
    productive_ind s <-> (exists xs v, matches s xs v).
Proof.
  lights;
    eauto using productive_ind_sound;
    eauto using productive_ind_complete.
Qed.
