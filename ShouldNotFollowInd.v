Require Import Coq.Lists.List.
Import ListNotations.

Require Export Parser.DescriptionInd.
Require Export Parser.ShouldNotFollowDescr.

Definition should_not_follow_ind { A } (s: Syntax A) (k: token_class): Prop :=
  descr_ind (should_not_follow_descr k) s tt.

Lemma should_not_follow_sound:
  forall A (s: Syntax A) k,
    should_not_follow_ind s k ->
    exists xs t ys v1 v2,
      matches s xs v1 /\
      matches s (xs ++ t :: ys) v2 /\
      class t = k
   .
Proof.
  induction 1;
    repeat light || lists || instantiate_any || destruct_match ||
           nullable_fun_spec || productive_fun_spec || apply_anywhere first_fun_sound || clear_in_dec;
    eauto 12 with matches.
Qed.

Lemma should_not_follow_first:
  forall A (s: Syntax A) ts v1,
    matches s ts v1 ->
    forall t ts' v2,
      ts = nil ->
      matches s (t :: ts') v2 ->
      should_not_follow_ind s (class t).
Proof.
  unfold should_not_follow_ind;
  induction 1;
    repeat light || invert_matches || invert_constructor_equalities || lists || app_cons_destruct;
    eauto 3 with descr_ind lights.

  - apply DisjInd0 with (some_rule tt);
      repeat
        light || lists || destruct_match || clear_in_dec || apply_anywhere first_fun_complete ||
        nullable_fun_spec.

  - apply DisjInd0 with (some_rule tt);
      repeat
        light || lists || destruct_match || clear_in_dec || apply_anywhere first_fun_complete ||
        nullable_fun_spec.

  - apply SeqInd2 with right_rule tt;
      repeat light || lists || destruct_match || nullable_fun_spec || productive_fun_spec;
      eauto.

  - apply SeqInd1 with left_rule tt;
      repeat light || lists || destruct_match || nullable_fun_spec || productive_fun_spec;
      eauto.
Qed.
