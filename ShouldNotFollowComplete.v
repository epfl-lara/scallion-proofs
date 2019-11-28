Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import PeanoNat.
Require Import Psatz. (* lia tactic for linear integer arithmetic *)

Require Export Parser.FocusedSyntaxDerive.
Require Export Parser.HasConflictFun.

Opaque unfocus_helper.
Opaque should_not_follow_fun.
Opaque locate.

Opaque FocusedSyntaxDerive.derive_obligation_1.
Opaque FocusedSyntaxDerive.derive_obligation_2.

Lemma should_not_follow_fun_unfocus_monotone:
  forall A T (ls: Layers T A) k core1 core2,
    In k (should_not_follow_fun (unfocus_helper ls core1)) ->
    (forall ts v, matches core1 ts v -> exists ts' v', matches core2 ts' v') ->
    (forall k, In k (should_not_follow_fun core1) -> In k (should_not_follow_fun core2)) ->
    In k (should_not_follow_fun (unfocus_helper ls core2)).
Proof.
  induction ls; lights; destruct_layer; unfocus_helper_def; eapply IHls; eauto;
    repeat light || invert_matches ||
           match goal with
           | H1: forall _ _, _ -> _, H2: matches _ _ _ |- _ => pose proof (H1 _ _ H2); clear H1
           end;
    eauto with matches;
    eauto with should_not_follow_fun;
    eauto using should_not_follow_fun_seq_monotone_l.
Qed.

Lemma should_not_follow_fun_plug_subset:
  forall A T (ls: Layers T A) (v: T) core k ts0 v0,
    matches core ts0 v0 ->
    In k (should_not_follow_fun (unfocus (plug ls v))) ->
    In k (should_not_follow_fun (unfocus_helper ls core)).
Proof.
  induction ls;
    repeat light || unfocus_helper_def || plug_def ||
           unfold unfocus in * || destruct_layer || apply_anywhere should_not_follow_fun_eps_seq2;
    eauto using should_not_follow_fun_epsilon with exfalso matches.

  eapply should_not_follow_fun_unfocus_monotone; eauto;
    repeat light || invert_matches || invert_constructor_equalities;
    eauto with matches.

  eapply should_not_follow_fun_seq_monotone_l;
    eauto using should_not_follow_fun_epsilon with exfalso matches.
Qed.

Lemma should_not_follow_fun_locate_subset_helper:
  forall n A (fs fs': Focused_Syntax A) k1 k2,
    length (layers fs) + count_follow_by (layers fs) < n ->
    locate k1 fs = Some fs' ->
    In k2 (should_not_follow_fun (unfocus fs')) ->
    In k2 (should_not_follow_fun (unfocus fs)).
Proof.
  unfold unfocus; induction n; destruct fs; intros; try lia.

  locate_def; repeat light || destruct_match || invert_constructor_equalities.

  unshelve epose proof (IHn _ _ _ _ _ _ H0 H1);
    repeat light || nullable_fun_spec;
    try solve [ pose proof (plug_count_follow_by _ _ layers i); lights; eauto with lia ];
    eauto using should_not_follow_fun_plug_subset with eapply_any.
Qed.

Lemma should_not_follow_fun_locate_subset:
  forall A (fs fs': Focused_Syntax A) k1 k2,
    locate k1 fs = Some fs' ->
    In k2 (should_not_follow_fun (unfocus fs')) ->
    In k2 (should_not_follow_fun (unfocus fs)).
Proof.
  eauto using should_not_follow_fun_locate_subset_helper.
Qed.

Lemma should_not_follow_fun_pierce_helper_subset_helper:
  forall m A T (ls: Layers A T) core t k gv pre,
    (List.length vars - List.length gv, syntax_size core) = m ->
    In k (should_not_follow_fun (unfocus_helper (pierce_helper (class t) core ls gv pre) (Epsilon t))) ->
    In k (should_not_follow_fun (unfocus_helper ls core)).
Proof.
  induction m using measure_induction; destruct core;
    repeat light || pierce_helper_def || find_false || unfocus_helper_def || destruct_match.

  - eapply should_not_follow_fun_unfocus_monotone; eauto;
      repeat light;
      eauto with matches;
      eauto using should_not_follow_fun_epsilon with exfalso.

  - apply should_not_follow_fun_unfocus_monotone with core1; lights;
      eauto with matches;
      eauto with should_not_follow_fun;
      eauto with lex;
      try solve [ eapply_any; eauto; eauto with lex has_conflict_ind ].

  - apply should_not_follow_fun_unfocus_monotone with core2; lights;
      eauto with matches;
      eauto with should_not_follow_fun;
      eauto with lex;
      try solve [ eapply_any; eauto; eauto with lex has_conflict_ind ].

  - unshelve epose proof (H _ _ _ _ _ _ _ _ _ _ eq_refl H1);
      repeat light || unfocus_helper_def; try lex.

  - pose proof i as ip.
    repeat light || options || destruct_match.
    destruct (nullable_fun core1) eqn:N in ip; lights.
    pose proof (nullable_fun_some _ _ _ N).

    unshelve epose proof (H _ _ _ _ _ _ _ _ _ _ eq_refl H1) as IH;
      repeat light || unfocus_helper_def || options || destruct_match || clear_some_dec; try lex.

    revert IH.
    generalize i.
    generalize (FocusedSyntaxPierce.pierce_helper'_obligations_obligation_9 A B
                          (class t) core1 core2 gv pre).
    rewrite N;
      lights.

    eapply should_not_follow_fun_unfocus_monotone; eauto;
      repeat light || invert_matches;
      eauto with matches;
      eauto with should_not_follow_fun.

  - unshelve epose proof (H _ _ _ _ _ _ _ _ _ _ eq_refl H1) as IH;
      repeat light || unfocus_helper_def || options || destruct_match || clear_some_dec; try lex.

  - unshelve epose proof (H _ _ _ _ _ _ _ _ _ _ eq_refl H1) as IH;
      repeat light || unfocus_helper_def || options || destruct_match || clear_some_dec; try lex.

  - unshelve epose proof (H _ _ _ _ _ _ _ _ _ _ eq_refl H1) as IH;
      repeat light || unfocus_helper_def || options || destruct_match || destruct_and ||
             clear_some_dec;
      try lex;
        eauto using pierce_var_measure.

    eapply should_not_follow_fun_unfocus_monotone; eauto;
      repeat light || invert_matches;
      eauto with matches;
      eauto with should_not_follow_fun.
Qed.

Lemma should_not_follow_fun_pierce_helper_subset:
  forall A T (ls: Layers A T) core t k gv pre,
    In k (should_not_follow_fun (unfocus_helper (pierce_helper (class t) core ls gv pre) (Epsilon t))) ->
    In k (should_not_follow_fun (unfocus_helper ls core)).
Proof.
  eauto using should_not_follow_fun_pierce_helper_subset_helper.
Qed.

Lemma should_not_follow_fun_pierce_subset:
  forall A T (ls: Layers A T) core t k pre,
    In k (should_not_follow_fun (unfocus_helper (pierce (class t) core ls pre) (Epsilon t))) ->
    In k (should_not_follow_fun (unfocus_helper ls core)).
Proof.
  unfold pierce;
    eauto using should_not_follow_fun_pierce_helper_subset.
Qed.

Lemma should_not_follow_fun_derive_subset:
  forall A (s ds: Focused_Syntax A) t k pre,
    derive s t pre = Some ds ->
    In k (should_not_follow_fun (unfocus ds)) ->
    In k (should_not_follow_fun (unfocus s)).
Proof.
  unfold derive, unfocus;
    repeat light || destruct_match || invert_constructor_equalities.

  clear matched.
  revert H0.
  generalize (FocusedSyntaxDerive.derive_obligation_2 A s t pre).
  generalize (FocusedSyntaxDerive.derive_obligation_1 A s t pre).
  repeat light || options || destruct_match.
  generalize (locate (class t) s).
  destruct (locate (class t) s) eqn:L;
    repeat light || invert_constructor_equalities.
  eapply should_not_follow_fun_locate_subset; eauto; unfold unfocus;
    eauto using should_not_follow_fun_pierce_subset.
Qed.

Theorem should_not_follow_fun_complete':
  forall xs A (fs: Focused_Syntax A) t ys v1 v2,
    matches (unfocus fs) xs v1 ->
    matches (unfocus fs) (xs ++ t :: ys) v2 ->
    ll1_fun (unfocus fs) = true ->
    In (class t) (should_not_follow_fun (unfocus fs)).
Proof.
  unfold unfocus;
    induction xs; repeat light || apply_anywhere ll1_fun_true;
    eauto using should_not_follow_fun_first.

  unshelve epose proof (derive_complete _ fs a xs _ v1 H);
    repeat light || options || destruct_match;
    eauto using unfocus_conflict_remains;
    eauto using unfocus_conflict_remains2.

  eapply should_not_follow_fun_derive_subset; eauto; lights.
  apply IHxs with ys v1 v2; lights;
    try solve [ eapply derive_sound_remove; eauto ].

  destruct (ll1_fun (unfocus_helper (layers f) (core f))) eqn:LL1;
    repeat light || apply_anywhere ll1_fun_false || apply_anywhere derive_no_conflict_unfocus.
Qed.

Theorem should_not_follow_fun_complete:
  forall xs A (s: Syntax A) t ys v1 v2,
    matches s xs v1 ->
    matches s (xs ++ t :: ys) v2 ->
    ll1_fun s = true ->
    In (class t) (should_not_follow_fun s).
Proof.
  intros.
  pose proof (unfocus_focus _ s) as HU.
  rewrite <- HU in *; eauto using should_not_follow_fun_complete'.
Qed.
