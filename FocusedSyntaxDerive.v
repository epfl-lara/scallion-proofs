Require Export Parser.FocusedSyntaxLocateMatches.
Require Export Parser.FocusedSyntaxPierceMatches.

Opaque locate.
Opaque pierce_helper.
Opaque unfocus_helper.
Opaque plug.

Program Definition derive { A } (fs: Focused_Syntax A) (t: token)
  (pre:
    ~ has_conflict_ind (core fs) /\
    ~ have_conflict_ind (layers fs))
    : option (Focused_Syntax A) :=
  let k := class t in
  let opt := locate k fs in
  if (is_some_dec opt)
  then
    let fs' := get_option opt _ in
    Some {| core := Epsilon t; layers := pierce k (core fs') (layers fs') _ |}
  else
    None.

Next Obligation.
  repeat light || options || destruct_match;
    eauto using locate_first_fun.

  apply_anywhere locate_no_conflict; lights.
Qed.

Fail Next Obligation. (* no more obligations for derive *)

Opaque derive_obligation_1.
Opaque derive_obligation_2.

Lemma derive_no_conflict:
  forall A (fs: Focused_Syntax A) t fs' pre,
    derive fs t pre = Some fs' ->
    has_conflict_ind (core fs') ->
    has_conflict_ind (core fs).
Proof.
  unfold derive;
    repeat light || destruct_match || invert_constructor_equalities;
    try inversion_solve.
Qed.

Lemma derive_no_conflicts:
  forall A (fs: Focused_Syntax A) t fs' pre,
    derive fs t pre = Some fs' ->
    have_conflict_ind (layers fs') ->
    have_conflict_ind (layers fs).
Proof.
  unfold derive;
    repeat light || destruct_match.

  inversion H; lights. clear H.

  apply_anywhere pierce_no_conflicts; lights.

  -revert H.
    generalize (derive_obligation_1 A fs t pre i).
    destruct (locate (class t) fs) eqn:L;
      repeat light.
    apply locate_no_conflicts in L; lights.

  - revert H.
    generalize (derive_obligation_1 A fs t pre i).
    destruct (locate (class t) fs) eqn:L;
      lights.
    apply locate_no_conflict in L; lights.
Qed.

Lemma derive_no_conflict_unfocus:
  forall A (fs: Focused_Syntax A) t fs' pre,
    derive fs t pre = Some fs' ->
    has_conflict_ind (unfocus fs') ->
    has_conflict_ind (unfocus fs).
Proof.
  unfold derive, unfocus;
    repeat light || destruct_match || invert_constructor_equalities;
    try inversion_solve.

  clear_some_dec.
  revert H0.
  generalize (derive_obligation_2 A fs t pre i); lights.
  revert a H0.
  generalize (derive_obligation_1 A fs t pre i); lights.
  destruct (locate (class t) fs) eqn:L;
    repeat light || destruct_and;
    eauto using pierce_no_conflict_unfocus, locate_no_conflict_unfocus_helper.
Qed.

Lemma derive_sound_add:
  forall A (fs fs': Focused_Syntax A) t ts pre v,
    derive fs t pre = Some fs' ->
    matches (unfocus fs') ts v ->
    matches (unfocus fs) (t :: ts) v.
Proof.
  unfold derive, unfocus;
    repeat light || destruct_match || invert_constructor_equalities.

  clear_some_dec.
  revert H0.
  generalize (derive_obligation_2 A fs t pre i); lights.
  revert a H0.
  generalize (derive_obligation_1 A fs t pre i); lights.

  repeat light || options || destruct_match || destruct_and.

  apply_anywhere matches_unfocus_prepend_one.
  apply_anywhere pierce_sound.
  unfold unfocus in *;
    eauto using locate_sound.
Qed.

Lemma derive_sound_remove:
  forall A (fs fs': Focused_Syntax A) t ts pre v,
    derive fs t pre = Some fs' ->
    ~ has_conflict_ind (unfocus fs) ->
    matches (unfocus fs) (t :: ts) v ->
    matches (unfocus fs') ts v.
Proof.
  unfold derive, unfocus;
    repeat light || destruct_match || invert_constructor_equalities.

  clear_some_dec.
  revert H0.
  generalize (derive_obligation_2 A fs t pre i); lights.
  revert a H0.
  generalize (derive_obligation_1 A fs t pre i); lights.

  repeat light || options || destruct_match || destruct_and.

  eapply locate_complete in H1; eauto.
  eapply pierce_complete in H1; lights; eauto.
  - eapply matches_unfocus_drop in H1;
      repeat light || invert_matches || invert_constructor_equalities;
      eauto using first_fun_complete with matches.

    apply (unfocus_conflict_more _ _ _ _ (Epsilon t)) in H3;
      repeat light || invert_matches || invert_constructor_equalities
             apply_anywhere should_not_follow_fun_sound;
      eauto with matches.

    + apply pierce_no_conflict_unfocus in H3; lights.
      eapply locate_no_conflict_unfocus in H3; lights; eauto.
    + unfold has_conflict_ind in *; repeat light || descr_ind_inversion.
    + apply_anywhere should_not_follow_fun_sound;
        repeat light || invert_matches.

  - eapply_anywhere locate_no_conflict_unfocus; eauto.
Qed.

Lemma derive_complete:
  forall A (fs: Focused_Syntax A) t ts pre v,
    matches (unfocus fs) (t :: ts) v ->
    ~ has_conflict_ind (unfocus fs) ->
    is_some (derive fs t pre).
Proof.
  unfold derive, unfocus;
    repeat light || destruct_match || invert_constructor_equalities;
    eauto using locate_is_some.
Qed.
