Require Export Parser.FocusedSyntaxLocate.

Opaque locate.
Opaque unfocus_helper.

Lemma locate_sound_helper:
  forall n A (fs fs': Focused_Syntax A) t ts v,
    length (layers fs) + count_follow_by (layers fs) <= n ->
    matches (unfocus_helper (layers fs') (core fs')) (t :: ts) v ->
    locate (get_kind t) fs = Some fs' ->
    matches (unfocus_helper (layers fs) (core fs)) (t :: ts) v.
Proof.
  induction n; destruct fs; intros; locate_def;
    repeat light || destruct_match || destruct_layer || invert_constructor_equalities || plug_def.

  - destruct layers; repeat light; eauto with exfalso lia.
  - eapply_anywhere IHn; lights; eauto.
    + apply_anywhere plug_sound. unfold unfocus in *; lights.
      eapply matches_unfocus_helper_sub;
        eauto; repeat light || invert_matches || nullable_fun_spec.
    + unshelve epose proof (plug_count_follow_by _ _ layers i _); lights.
      unfold plug in *; lia.
Qed.

Lemma locate_sound:
  forall A (fs fs': Focused_Syntax A) t ts v,
    matches (unfocus_helper (layers fs') (core fs')) (t :: ts) v ->
    locate (get_kind t) fs = Some fs' ->
    matches (unfocus_helper (layers fs) (core fs)) (t :: ts) v.
Proof.
  eauto using locate_sound_helper.
Qed.

Lemma locate_complete_helper:
  forall n A (fs fs': Focused_Syntax A) t ts v,
    length (layers fs) + count_follow_by (layers fs) <= n ->
    matches (unfocus_helper (layers fs) (core fs)) (t :: ts) v ->
    ~ has_conflict_ind (unfocus_helper (layers fs) (core fs)) ->
    locate (get_kind t) fs = Some fs' ->
    matches (unfocus_helper (layers fs') (core fs')) (t :: ts) v.
Proof.
  induction n; destruct fs; intros; locate_def;
    repeat light || destruct_match || destruct_layer || invert_constructor_equalities || plug_def.

  - destruct layers; repeat light; eauto with exfalso lia.
  - eapply IHn; repeat light || nullable_fun_spec; eauto;
      eauto using plug_no_conflict_unfocus.
    + unshelve epose proof (plug_count_follow_by _ _ layers i _); lights.
      unfold plug in *; lia.
    + apply plug_complete. unfold unfocus in *; lights.
      eapply matches_unfocus_propagate_first;
        eauto; repeat light || invert_matches || nullable_fun_spec;
          eauto with matches;
          eauto with exfalso unfocus_conflict_more.
Qed.

Lemma locate_complete:
  forall A (fs fs': Focused_Syntax A) t ts v,
    matches (unfocus_helper (layers fs) (core fs)) (t :: ts) v ->
    ~ has_conflict_ind (unfocus_helper (layers fs) (core fs)) ->
    locate (get_kind t) fs = Some fs' ->
    matches (unfocus_helper (layers fs') (core fs')) (t :: ts) v.
Proof.
  eauto using locate_complete_helper.
Qed.

Lemma locate_correct:
  forall A (fs fs': Focused_Syntax A) t,
    locate (get_kind t) fs = Some fs' ->
    ~ has_conflict_ind (unfocus_helper (layers fs) (core fs)) ->
      forall ts v,
      matches (unfocus_helper (layers fs') (core fs')) (t :: ts) v <->
      matches (unfocus_helper (layers fs) (core fs)) (t :: ts) v.
Proof.
  lights; eauto using locate_sound, locate_complete.
Qed.

Lemma locate_not_none_helper:
  forall n A (fs: Focused_Syntax A) t ts v,
    length (layers fs) + count_follow_by (layers fs) <= n ->
    locate (get_kind t) fs = None ->
    matches (unfocus fs) (t :: ts) v ->
    False.
Proof.
  unfold unfocus;
  induction n; destruct fs; intros; locate_def;
    repeat light || destruct_match || destruct_layer || invert_constructor_equalities || plug_def ||
           options || destruct_match || unfocus_helper_def || nullable_fun_spec;
    try solve [
      destruct layers; repeat light || unfocus_helper_def; eauto with lia;
        eauto using first_fun_complete with exfalso
    ];
    try solve [ eapply_anywhere plug_no_conflict_unfocus; eauto ];
    try solve [ rewrite_any; lights ].

  - apply (matches_unfocus_helper_sub_first3 _ _ _ _ (Epsilon i)) in H1;
      lights;
      eauto with matches;
      eauto using first_fun_complete with exfalso.

    eapply IHn in H0;
      eauto;
      try solve [ intros; eapply_anywhere plug_no_conflict_unfocus; eauto ].
    + unshelve epose proof (plug_count_follow_by _ _ layers i _); lights.
      unfold plug in *; lia.

    + apply plug_complete; unfold unfocus; lights; eauto.

  - matches_unfocus_helper_prefix;
      repeat light || app_cons_destruct || invert_constructor_equalities;
      eauto using first_fun_complete.
Qed.

Lemma locate_not_none:
  forall A (fs: Focused_Syntax A) t ts v,
    locate (get_kind t) fs = None ->
    matches (unfocus fs) (t :: ts) v ->
    False.
Proof.
  eauto using locate_not_none_helper.
Qed.

Lemma locate_not_none2:
  forall A (fs: Focused_Syntax A) k,
    locate k fs = None ->
    ~ first_ind (unfocus fs) k.
Proof.
  lights.
  apply_anywhere first_ind_sound; lights.
  eauto using locate_not_none.
Qed.

Lemma locate_is_some:
  forall A (fs: Focused_Syntax A) t ts v,
    matches (unfocus fs) (t :: ts) v ->
    is_some (locate (get_kind t) fs).
Proof.
  intros.
  destruct (locate (get_kind t) fs) eqn:L;
    repeat light || options;
    eauto using locate_not_none.
Qed.
