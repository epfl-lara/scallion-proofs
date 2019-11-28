Require Import Coq.Lists.List.
Import ListNotations.

Require Export Parser.NullableDescr.
Require Export Parser.DescriptionInd.
Require Export Parser.Matches.

Definition nullable_ind { A }: Syntax A -> A -> Prop := descr_ind nullable_descr.

Lemma nullable_sound:
  forall A (s: Syntax A) (v: A),
    nullable_ind s v ->
    matches s nil v.
Proof.
  unfold nullable_ind; intros.
  remember (Some v) as opt.
  induction H; repeat light || options || rules || destruct_match || invert_constructor_equalities;
    eauto with matches.
Qed.

Lemma nullable_complete:
  forall A (s: Syntax A) (v: A),
    matches s nil v ->
    exists v', nullable_ind s v'.
Proof.
  unfold nullable_ind; intros.
  remember [] as forgotten.
  remember [] as ts in H.
  induction H;
    repeat light || lists; eauto 3 with descr_ind lights.
Qed.
