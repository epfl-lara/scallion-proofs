Require Import Coq.Lists.List.
Import ListNotations.

Require Export Parser.DescriptionToFunctionSoundness.
Require Export Parser.DescriptionToFunctionCompleteness.
Require Export Parser.ProductiveInd.
Require Export Parser.Matches.
Require Export Parser.DescriptionInd.
Require Export Parser.ProductiveDescr.
Require Export Parser.MonotonicRules.

Definition productive_fun' { A }: Syntax A -> option unit := build_fun productive_descr.
Definition productive_fun { A } (s: Syntax A): bool := is_some_b (productive_fun' s).

Lemma monotonic_productive: monotonic_descr productive_descr.
Proof.
  unfold monotonic_descr, productive_descr;
    repeat light;
    eauto using monotonic_rule_1_map;
    eauto using monotonic_rule_2_disj;
    eauto using monotonic_rule_2_combine;
    eauto using monotonic_rule_1_id.
Qed.

Lemma productive_fun_true:
  forall A (s: Syntax A) xs v,
    matches s xs v ->
    productive_fun s = true.
Proof.
  unfold productive_fun, productive_fun'; intros.
  destruct (build_fun productive_descr s) eqn:E; repeat light || destruct_unit.
  - unshelve epose proof (fun_completeness _ productive_descr _ s tt _ monotonic_productive);
      repeat light || options || destruct_match.
    apply_anywhere productive_ind_complete; eauto with exfalso.
Qed.

Lemma productive_fun_true_iff:
  forall A (s: Syntax A),
    productive_fun s = true <-> exists xs v, matches s xs v.
Proof.
  unfold productive_fun, productive_fun'; intros.
  destruct (build_fun productive_descr s) eqn:E; repeat light || destruct_unit.
  - pose proof (fun_soundness _ productive_descr _ s tt);
      repeat light || options || destruct_match.
    apply productive_ind_sound in H1; auto.
  - unshelve epose proof (fun_completeness _ productive_descr _ s tt _ monotonic_productive);
      repeat light || options || destruct_match.
    apply productive_ind_complete in H; eauto with exfalso.
Qed.

Lemma productive_fun_false_iff:
  forall A (s: Syntax A),
    productive_fun s = false <-> forall xs v, ~matches s xs v.
Proof.
  intros.
  pose proof (productive_fun_true_iff _ s).
  destruct (productive_fun s) eqn:PS; lights;
    eauto with exfalso.
  unshelve epose proof (H1 _); eauto; lights.
Qed.

Lemma productive_fun_false:
  forall A (s: Syntax A) xs v,
    productive_fun s = false ->
    matches s xs v ->
    False.
Proof.
  intros.
  pose proof (productive_fun_false_iff _ s); lights; eauto.
Qed.

Ltac productive_fun_spec :=
  match goal with
  | H1: productive_fun ?s = false,
    H2: matches ?s _ _ |-  _ =>
    apply (False_ind _ (productive_fun_false _ _ _ _ H1 H2))
  | _ => rewrite productive_fun_true_iff in * || rewrite productive_fun_false_iff in *
  end.
