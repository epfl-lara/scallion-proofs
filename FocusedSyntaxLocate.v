Require Import Equations.Init.
Require Import Equations.Equations.

Require Export Parser.FocusedSyntaxPlug.

Opaque plug.
Opaque unfocus_helper.

Equations (noind) locate { A } (k: token_class) (fs: Focused_Syntax A): option (Focused_Syntax A)
  by wf (length (layers fs) + count_follow_by (layers fs)) lt :=

  locate k fs :=
    if (in_dec kind_eq_dec k (first_fun (core fs)))
    then Some fs
    else
      match nullable_fun (core fs) with
      | None => None
      | Some v =>
        if (dec_empty_layers (layers fs))
        then None
        else locate k (plug (layers fs) v)
      end.

Next Obligation. eauto using plug_count_follow_by. Qed.

Fail Next Obligation. (* no more obligations for `locate` *)

Ltac locate_def :=
  rewrite locate_equation_1 in *.

Opaque locate.

Lemma locate_first_fun_helper:
  forall n A k (fs fs': Focused_Syntax A),
    length (layers fs) + count_follow_by (layers fs) <= n ->
    locate k fs = Some fs' ->
    In k (first_fun (core fs')).
Proof.
  induction n; destruct fs; locate_def; repeat light || destruct_match || invert_constructor_equalities.

  - destruct layers; lights; eauto with exfalso lia.

  - eapply_any; eauto.
    pose proof (plug_count_follow_by _ _ layers i); lights; eauto with lia.
Qed.

Lemma locate_first_fun:
  forall A k (fs fs': Focused_Syntax A),
    locate k fs = Some fs' ->
    In k (first_fun (core fs')).
Proof.
  eauto using locate_first_fun_helper.
Qed.

Lemma locate_first_ind:
  forall A k (fs fs': Focused_Syntax A),
    locate k fs = Some fs' ->
    first_ind (core fs') k.
Proof.
  intros.
  apply first_fun_correct;
    eauto using locate_first_fun.
Qed.

Lemma locate_no_conflict_helper:
  forall n A k (fs fs': Focused_Syntax A),
    length (layers fs) + count_follow_by (layers fs) <= n ->
    locate k fs = Some fs' ->
    has_conflict_ind (core fs') ->
      has_conflict_ind (core fs) \/
      have_conflict_ind (layers fs).
Proof.
  induction n; destruct fs; locate_def; repeat light || destruct_match || invert_constructor_equalities.

  - destruct layers; lights; eauto with lia.
  - eapply IHn in H1; eauto; lights; eauto with lia;
      eauto using plug_no_conflict;
      eauto using plug_no_conflicts.
    unshelve epose proof (plug_count_follow_by _ _ layers i _); lights; lia.
Qed.

Lemma locate_no_conflict:
  forall A k (fs fs': Focused_Syntax A),
    locate k fs = Some fs' ->
    has_conflict_ind (core fs') ->
      has_conflict_ind (core fs) \/
      have_conflict_ind (layers fs).
Proof.
  eauto using locate_no_conflict_helper.
Qed.

Lemma locate_no_conflicts_helper:
  forall n A k (fs fs': Focused_Syntax A),
    length (layers fs) + count_follow_by (layers fs) <= n ->
    locate k fs = Some fs' ->
    have_conflict_ind (layers fs') ->
      has_conflict_ind (core fs) \/
      have_conflict_ind (layers fs).
Proof.
  induction n; destruct fs; locate_def; repeat light || destruct_match || invert_constructor_equalities.

  - destruct layers; lights; eauto with lia.
  - eapply IHn in H1; eauto; lights; eauto with lia;
      eauto using plug_no_conflict;
      eauto using plug_no_conflicts.
    unshelve epose proof (plug_count_follow_by _ _ layers i _); lights; lia.
Qed.

Lemma locate_no_conflicts:
  forall A k (fs fs': Focused_Syntax A),
    locate k fs = Some fs' ->
    have_conflict_ind (layers fs') ->
      has_conflict_ind (core fs) \/
      have_conflict_ind (layers fs).
Proof.
  eauto using locate_no_conflicts_helper.
Qed.

Lemma locate_no_conflict_unfocus_helper':
  forall n A k (fs fs': Focused_Syntax A),
    length (layers fs) + count_follow_by (layers fs) <= n ->
    locate k fs = Some fs' ->
    has_conflict_ind (unfocus_helper (layers fs') (core fs')) ->
    has_conflict_ind (unfocus_helper (layers fs) (core fs)).
Proof.
  induction n; destruct fs; locate_def;
    repeat light || destruct_match || nullable_fun_spec || invert_constructor_equalities.

  - destruct layers; lights; eauto with lia.
  - eapply IHn in H1; eauto; lights;
      eauto using plug_no_conflict_unfocus.
    unshelve epose proof (plug_count_follow_by _ _ layers i _); lights; lia.
Qed.

Lemma locate_no_conflict_unfocus_helper:
  forall A k (fs fs': Focused_Syntax A),
    locate k fs = Some fs' ->
    has_conflict_ind (unfocus_helper (layers fs') (core fs')) ->
    has_conflict_ind (unfocus_helper (layers fs) (core fs)).
Proof.
  eauto using locate_no_conflict_unfocus_helper'.
Qed.

Lemma locate_no_conflict_unfocus:
  forall A k (fs fs': Focused_Syntax A),
    locate k fs = Some fs' ->
    has_conflict_ind (unfocus fs') ->
    has_conflict_ind (unfocus fs).
Proof.
  unfold unfocus;
    eauto using locate_no_conflict_unfocus_helper.
Qed.
