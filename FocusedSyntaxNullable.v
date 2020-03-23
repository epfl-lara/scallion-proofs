Require Import Equations.Init.
Require Import Equations.Equations.

Require Export Parser.FocusedSyntaxPlug.
Require Export Parser.AmbiguityConflict.

Opaque unfocus_helper.

Program Definition conv { A B } (ls: Layers A B) (pre: empty_layers ls) (x: A): B :=
  match ls as ls' in Layers X Y return empty_layers ls' -> X -> Y with
  | Empty _ => fun H x => x
  | _ => _
  end pre x.

Equations (noind) result { A } (fs: Focused_Syntax A): option A
  by wf (length (layers fs) + count_follow_by (layers fs)) lt :=

  result fs :=
    match nullable_fun (core fs) with
    | None => None
    | Some x =>
      if (dec_empty_layers (layers fs))
      then Some (conv (layers fs) _ x)
      else result (plug (layers fs) x)
    end.

Next Obligation.
  auto using plug_count_follow_by.
Qed.

Fail Next Obligation. (* no more obligation for result *)

Ltac result_def := rewrite result_equation_1 in *.

Opaque result.

Lemma result_sound':
  forall n A (fs : Focused_Syntax A) v,
    length (layers fs) + count_follow_by (layers fs) <= n ->
    result fs = Some v ->
    matches (unfocus fs) [] v.
Proof.
  induction n; destruct fs; result_def;
    repeat light || destruct_match || nullable_fun_spec.

  - destruct layers; light; try lia.
    unfold unfocus; repeat light || unfocus_helper_def.

  - destruct layers; light; try lia.

  - unfold conv in *;
      repeat light || destruct_match.
    unfold unfocus; repeat light || unfocus_helper_def.

  - unshelve epose proof (IHn _ (plug layers i) v _ H0);
      lights.
    + unshelve epose proof (plug_count_follow_by _ _ layers i _);
        lights; try lia.
    + apply_anywhere plug_sound.
      eapply matches_unfocus_sub;
        eauto; repeat light || invert_matches.
Qed.

Lemma result_sound:
  forall A (fs : Focused_Syntax A) v,
    result fs = Some v ->
    matches (unfocus fs) [] v.
Proof.
  eauto using result_sound'.
Qed.

Lemma result_complete':
  forall n A (fs: Focused_Syntax A) v,
    length (layers fs) + count_follow_by (layers fs) <= n ->
    matches (unfocus_helper (layers fs) (core fs)) [] v ->
    ~ has_conflict_ind (unfocus_helper (layers fs) (core fs)) ->
    result fs = Some v.
Proof.
  induction n; destruct fs; result_def;
    repeat light || destruct_match || nullable_fun_spec || f_equal || unfold conv in * || destruct_match ||
           unfocus_helper_def;
    eauto using matches_nil_unicity;
    try solve [ destruct layers; lights; eauto with exfalso lia ].

  - apply_any;
      eauto using plug_no_conflict_unfocus.

    + unshelve epose proof (plug_count_follow_by _ _ layers i _);
        lights; try lia.
    + eapply plug_nullable;
        eauto.

  - apply_anywhere matches_unfocus_helper_nil;
      lights; eauto with exfalso.
Qed.

Lemma result_complete:
  forall A (fs: Focused_Syntax A) v,
    matches (unfocus fs) [] v ->
    ~ has_conflict_ind (unfocus_helper (layers fs) (core fs)) ->
    result fs = Some v.
Proof.
  destruct fs;
    eauto using result_complete'.
Qed.

Lemma result_correct:
  forall A (fs: Focused_Syntax A),
    ll1_ind (unfocus fs) ->
    result fs = nullable_fun (unfocus fs).
Proof.
  unfold ll1_ind; intros.
  destruct (result fs) eqn:RES;
  destruct (nullable_fun (unfocus fs)) eqn:NULL;
    repeat light || nullable_fun_spec.
  - apply_anywhere result_sound; matches_nil_unicity; lights.
  - apply_anywhere result_sound; eauto with exfalso.
  - apply_anywhere result_complete; lights.
Qed.
