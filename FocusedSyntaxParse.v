Require Import Equations.Equations.

Require Export Parser.FocusedSyntaxDerive.
Require Export Parser.FocusedSyntaxNullable.

Opaque unfocus_helper.
Opaque result.
Opaque derive.

Program Fixpoint parse { A } (fs: Focused_Syntax A) (ts: list token)
  (pre:
    ~ has_conflict_ind (core fs) /\
    ~ have_conflict_ind (layers fs)
  ): option A :=
  match ts with
  | nil => result fs
  | t :: ts =>
    match derive fs t _ with
    | None => None
    | Some fs' => parse fs' ts _
    end
  end.

Next Obligation.
  lights; eauto using derive_no_conflict, derive_no_conflicts.
Qed.

Fail Next Obligation. (* no more obligation for `parse` *)

Lemma parse_sound:
  forall ts A (fs: Focused_Syntax A) pre v,
    parse fs ts pre = Some v ->
    matches (unfocus fs) ts v.
Proof.
  induction ts; repeat light;
    eauto using result_sound.

  - revert H.
    generalize (parse_obligation_2 A fs pre a);
      repeat light || destruct_match.

    pose proof (IHts _ _ _ _ H); lights;
      eauto using derive_sound_add.
Qed.

Lemma parse_complete:
  forall ts A (fs: Focused_Syntax A) pre v,
    matches (unfocus fs) ts v ->
    ~ has_conflict_ind (unfocus fs) ->
    parse fs ts pre = Some v.
Proof.
  induction ts; repeat light || options || destruct_match;
    eauto using result_complete.

  generalize (parse_obligation_2 A fs pre a);
    repeat light || destruct_match || destruct_and.

  - unshelve epose proof (derive_sound_remove _ _ _ _ _ _ _ matched _ H) as HM;
      eauto using derive_no_conflict_unfocus.
  - eapply derive_complete in H;
      repeat light || options || destruct_match || rewrite_any.
Qed.

Program Definition parse_correct_statement: Prop :=
  forall A (s: Syntax A) (LL1: ll1_ind s) ts v,
    parse (focus s) ts _ = Some v <->
    matches s ts v.

Fail Next Obligation. (* no more obligations for parse_correct_statement *)

Lemma parse_correct: parse_correct_statement.
Proof.
  unfold parse_correct_statement; lights;
    eauto using parse_complete.
  apply_anywhere parse_sound; rewrite unfocus_focus in *; auto.
Qed.

Lemma non_ambiguous_ll1:
  forall ts A (s: Syntax A) v1 v2,
    matches s ts v1 ->
    matches s ts v2 ->
    ll1_ind s ->
    v1 = v2.
Proof.
  unfold ll1_ind; intros.
  rewrite <- (unfocus_focus A s) in *.
  assert (
    ~ has_conflict_ind (core (focus s)) /\
    ~ have_conflict_ind (layers (focus s))
  ) as pre; [ lights | idtac ].
  apply (parse_complete  _ _ _ pre) in H; [ idtac | lights ].
  apply (parse_complete  _ _ _ pre) in H0; lights.
Qed.
