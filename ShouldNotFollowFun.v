Require Import Coq.Lists.List.
Import ListNotations.

Require Export Parser.DescriptionToFunctionSoundness.
Require Export Parser.DescriptionToFunctionCompleteness.
Require Export Parser.ShouldNotFollowInd.
Require Export Parser.MonotonicRules.

Definition should_not_follow_fun' { A } (k: token_class): Syntax A -> option unit :=
  build_fun (should_not_follow_descr k).

Definition should_not_follow_fun { A } (s: Syntax A): list token_class :=
  filter (fun k => is_some_b (should_not_follow_fun' k s)) token_classes.

Lemma monotonic_should_not_follow: forall k, monotonic_descr (should_not_follow_descr k).
Proof.
  unfold monotonic_descr, should_not_follow_descr;
    repeat light || lists || destruct_match;
    eauto using monotonic_rule_1_map;
    eauto using monotonic_rule_2_disj;
    eauto using monotonic_rule_2_combine;
    eauto using monotonic_rule_2_left;
    eauto using monotonic_rule_2_right;
    eauto using monotonic_rule_2_some;
    eauto using monotonic_rule_1_id.
Qed.

Lemma should_not_follow_fun_sound:
  forall A (s: Syntax A) k,
    In k (should_not_follow_fun s) ->
    exists xs t ys v1 v2,
      matches s xs v1 /\
      matches s (xs ++ t :: ys) v2 /\
      get_kind t = k.
Proof.
  unfold should_not_follow_fun, should_not_follow_fun'; intros.
  rewrite filter_In in *; repeat light || options || destruct_match || destruct_unit.
  pose proof (fun_soundness _ (should_not_follow_descr k) _ s tt); lights.
  apply should_not_follow_ind_sound in H2; auto.
Qed.

Lemma should_not_follow_ind_fun:
  forall A k (s: Syntax A),
    should_not_follow_ind s k <->
    In k (should_not_follow_fun s).
Proof.
  unfold should_not_follow_ind, should_not_follow_fun, should_not_follow_fun';
    repeat light || rewrite filter_In in * || options || destruct_match || destruct_unit;
    eauto using all_token_classes;
    eauto using fun_soundness.

  apply_anywhere fun_completeness;
    repeat light || options || destruct_match;
    eauto using monotonic_should_not_follow.
Qed.

Lemma should_not_follow_fun_first:
  forall A (s: Syntax A) t ts v1 v2,
    matches s [] v1 ->
    matches s (t :: ts) v2 ->
    In (get_kind t) (should_not_follow_fun s).
Proof.
  repeat light || rewrite <- should_not_follow_ind_fun in *;
    eauto using should_not_follow_ind_first.
Qed.

Lemma should_not_follow_fun_epsilon:
  forall A (t: A) k,
    In k (should_not_follow_fun (Epsilon t)) ->
    False.
Proof.
  repeat light || apply_anywhere should_not_follow_fun_sound || invert_matches.
Qed.

Lemma should_not_follow_fun_disj_l:
  forall A (s1 s2: Syntax A) k,
    In k (should_not_follow_fun s1) ->
    In k (should_not_follow_fun (Disjunction s1 s2)).
Proof.
  repeat light || rewrite <- should_not_follow_ind_fun in * || unfold should_not_follow_ind in *;
    eauto with descr_ind lights.
Qed.

Lemma should_not_follow_fun_disj_r:
  forall A (s1 s2: Syntax A) k,
    In k (should_not_follow_fun s2) ->
    In k (should_not_follow_fun (Disjunction s1 s2)).
Proof.
  repeat light || rewrite <- should_not_follow_ind_fun in * || unfold should_not_follow_ind in *;
    eauto with descr_ind lights.
Qed.

Lemma should_not_follow_fun_seq_l:
  forall A1 A2 (s1: Syntax A1) (s2: Syntax A2) k v,
    In k (should_not_follow_fun s1) ->
    matches s2 [] v ->
    In k (should_not_follow_fun (Sequence s1 s2)).
Proof.
  repeat light || rewrite <- should_not_follow_ind_fun in * || unfold should_not_follow_ind in *.
  apply SeqInd1 with left_rule tt;
    repeat light || lists || destruct_match || nullable_fun_spec.
Qed.

Lemma should_not_follow_fun_seq_r:
  forall A1 A2 (s1: Syntax A1) (s2: Syntax A2) k ts v,
    In k (should_not_follow_fun s2) ->
    matches s1 ts v ->
    In k (should_not_follow_fun (Sequence s1 s2)).
Proof.
  repeat light || rewrite <- should_not_follow_ind_fun in * || unfold should_not_follow_ind in *.
  apply SeqInd2 with right_rule tt;
    repeat light || lists || destruct_match || productive_fun_spec.
Qed.

Lemma should_not_follow_fun_map:
  forall A B (f: A -> B) g (s: Syntax A) k,
    In k (should_not_follow_fun s) ->
    In k (should_not_follow_fun (Map f g s)).
Proof.
  repeat light || rewrite <- should_not_follow_ind_fun in * || unfold should_not_follow_ind in *;
    eauto with descr_ind lights.
Qed.

Lemma should_not_follow_fun_map2:
  forall A B (f: A -> B) g (s: Syntax A) k,
    In k (should_not_follow_fun (Map f g s)) ->
    In k (should_not_follow_fun s).
Proof.
  repeat light || rewrite <- should_not_follow_ind_fun in * || unfold should_not_follow_ind in * ||
         descr_ind_inversion.
Qed.

Lemma should_not_follow_fun_var:
  forall k x,
    In k (should_not_follow_fun (e x)) ->
    In k (should_not_follow_fun (Var x)).
Proof.
  repeat light || rewrite <- should_not_follow_ind_fun in * || unfold should_not_follow_ind in *;
    eauto with descr_ind lights.
Qed.

Lemma should_not_follow_fun_var2:
  forall k x,
    In k (should_not_follow_fun (Var x)) ->
    In k (should_not_follow_fun (e x)).
Proof.
  repeat light || rewrite <- should_not_follow_ind_fun in * || unfold should_not_follow_ind in * ||
         descr_ind_inversion.
Qed.

Lemma should_not_follow_fun_eps_seq:
  forall A1 A2 (a: A1) (s2: Syntax A2) k,
    In k (should_not_follow_fun s2) ->
    In k (should_not_follow_fun (Sequence (Epsilon a) s2)).
Proof.
  repeat light || rewrite <- should_not_follow_ind_fun in * || unfold should_not_follow_ind in *.

  apply SeqInd2 with right_rule tt;
    repeat light || lists || destruct_match || productive_fun_spec;
    eauto with exfalso matches.
Qed.

Lemma should_not_follow_fun_eps_seq2:
  forall A1 A2 (a: A1) (s2: Syntax A2) k,
    In k (should_not_follow_fun (Sequence (Epsilon a) s2)) ->
    In k (should_not_follow_fun s2).
Proof.
  repeat light || rewrite <- should_not_follow_ind_fun in * || unfold should_not_follow_ind in * ||
         lists || destruct_match || descr_ind_inversion.
Qed.

Ltac should_not_follow_ind_descr :=
  match goal with
  | H1: forall k, In k (should_not_follow_fun ?s) -> _,
    H2: descr_ind (should_not_follow_descr ?k) ?s tt |- _ =>
    unshelve epose proof (H1 k _); clear H1
  end.

Lemma should_not_follow_fun_seq_monotone_l:
  forall A B (s1 s2: Syntax A) (s: Syntax B) k,
    In k (should_not_follow_fun (Sequence s1 s)) ->
    (forall ts v, matches s1 ts v -> exists ts' v', matches s2 ts' v') ->
    (forall k, In k (should_not_follow_fun s1) -> In k (should_not_follow_fun s2)) ->
    In k (should_not_follow_fun (Sequence s2 s)).
Proof.
  repeat light || rewrite <- should_not_follow_ind_fun in * || unfold should_not_follow_ind in * ||
         invert_matches || app_cons_destruct || lists || descr_ind_inversion || nullable_fun_spec ||
         invert_constructor_equalities || should_not_follow_ind_descr || destruct_match ||
         destruct_unit.

  - apply SeqInd1 with left_rule tt;
      repeat light || lists || destruct_match || nullable_fun_spec || productive_fun_spec.
  - apply SeqInd2 with right_rule tt;
      repeat light || lists || destruct_match || nullable_fun_spec || productive_fun_spec ||
             instantiate_any;
      eauto with exfalso.
  - apply SeqInd1 with left_rule tt;
      repeat light || lists || destruct_match || nullable_fun_spec || productive_fun_spec.
  - apply SeqInd2 with right_rule tt;
      repeat light || lists || destruct_match || nullable_fun_spec || productive_fun_spec ||
             instantiate_any;
      eauto with exfalso.
Qed.

Hint Resolve should_not_follow_fun_disj_l: should_not_follow_fun.
Hint Resolve should_not_follow_fun_disj_r: should_not_follow_fun.
Hint Resolve should_not_follow_fun_seq_l: should_not_follow_fun.
Hint Resolve should_not_follow_fun_seq_r: should_not_follow_fun.

Hint Resolve should_not_follow_fun_map: should_not_follow_fun.
Hint Resolve should_not_follow_fun_var: should_not_follow_fun.
Hint Resolve should_not_follow_fun_eps_seq: should_not_follow_fun.

Hint Immediate should_not_follow_fun_map2: should_not_follow_fun.
Hint Immediate should_not_follow_fun_var2: should_not_follow_fun.
Hint Immediate should_not_follow_fun_eps_seq2: should_not_follow_fun.
Hint Extern 1 => solve [ exfalso; eauto using should_not_follow_fun_epsilon ]: should_not_follow_fun.
