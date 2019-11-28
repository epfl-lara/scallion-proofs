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
